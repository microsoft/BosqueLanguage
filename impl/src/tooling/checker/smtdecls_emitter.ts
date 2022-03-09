//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";
import { BSQRegex } from "../../ast/bsqregex";

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, MIRType, MIRTypeOption, SymbolicActionMode } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEntityCollectionTypeDecl, SMTEntityInternalOfTypeDecl, SMTEntityOfTypeDecl, SMTEntityStdDecl, SMTEphemeralListDecl, SMTFunction, SMTFunctionUninterpreted, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallSimple, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTMaskConstruct, SMTTypeInfo, SMTVar, VerifierOptions } from "./smt_exp";

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;
    readonly vopts: VerifierOptions;

    readonly havocPathType: SMTTypeInfo;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly, vopts: VerifierOptions) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
        this.vopts = vopts;

        this.havocPathType = this.temitter.getSMTTypeFor(this.temitter.getMIRType("HavocSequence"));
    }

    private generateAPITypeConstructorFunction_StringOf(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("String"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(this.temitter.getMIRType("String"), new SMTVar("path"));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRStringOfInternalEntityTypeDecl;
        const vre = this.bemitter.assembly.validatorRegexs.get(ttdecl.validatortype) as BSQRegex;
        const lre = vre.compileToPatternToSMT(true);

        const accept: SMTExp = new SMTCallSimple("str.in.re", [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("String"), new SMTVar("str")), new SMTConst(lre)]);
        const fbody = new SMTLet("str", bcreate,
            new SMTIf(SMTCallSimple.makeAndOf(this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("String"), new SMTVar("str")), accept),
                new SMTVar("str"),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_DataString(tt: MIRType, havocfuncs: Set<String>,  ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("String"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(this.temitter.getMIRType("String"), new SMTVar("path"));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRDataStringInternalEntityTypeDecl;
        const accepts = this.temitter.lookupFunctionName(ttdecl.accepts as MIRInvokeKey);
        const pcheck = SMTCallSimple.makeEq(new SMTCallGeneral(accepts, [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("String"), new SMTVar("str"))]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));

        const fbody = new SMTLet("str", bcreate,
            new SMTIf(SMTCallSimple.makeAndOf(this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("String"), new SMTVar("str")), pcheck),
                new SMTVar("str"),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_DataBuffer(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("ByteBuffer"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(this.temitter.getMIRType("ByteBuffer"), new SMTVar("path"));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRDataBufferInternalEntityTypeDecl;
        const accepts = this.temitter.lookupFunctionName(ttdecl.accepts as MIRInvokeKey);
        const pcheck = SMTCallSimple.makeEq(new SMTCallGeneral(accepts, [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("ByteBuffer"), new SMTVar("bb"))]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));

        const fbody = new SMTLet("bb", bcreate,
            new SMTIf(SMTCallSimple.makeAndOf(this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("ByteBuffer"), new SMTVar("bb")), pcheck),
                new SMTVar("bb"),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_TypedPrimitive(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(oftype, new SMTVar("path"));

        let fexp: SMTExp = new SMTConst("[INVALID]");
        if(tdecl.validatefunc === undefined) {
            fexp = new SMTIf(this.temitter.generateResultIsSuccessTest(tt, new SMTVar("vv")),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))),
                this.temitter.generateErrorResultAssert(tt)
            );
        }
        else {
            const cchk = SMTCallSimple.makeEq(new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.validatefunc), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));
            const ccons = (tdecl.usingcons !== undefined) ? new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.usingcons), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]) : this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv")));
            
            fexp = new SMTIf(cchk, ccons, this.temitter.generateErrorResultAssert(tt));
        }

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), new SMTLet("vv", bcreate, fexp)));
    }

    private generateAPITypeConstructorFunction_Something(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(oftype, new SMTVar("path"));
        
        const fexp = new SMTLet("vv", bcreate, 
                new SMTIf(this.temitter.generateResultIsSuccessTest(tt, new SMTVar("vv")),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fexp));
    }

    private generateAPITypeConstructorFunction_Ok(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(oftype, new SMTVar("path"));
        
        const fexp = new SMTLet("vv", bcreate, 
                new SMTIf(this.temitter.generateResultIsSuccessTest(tt, new SMTVar("vv")),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fexp));
    }

    private generateAPITypeConstructorFunction_Err(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(oftype, new SMTVar("path"));
        
        const fexp = new SMTLet("vv", bcreate, 
                new SMTIf(this.temitter.generateResultIsSuccessTest(tt, new SMTVar("vv")),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fexp));
    }

    private generateAPITypeConstructorFunction_Enum(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIREnumEntityTypeDecl;

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const bcreate = new SMTCallSimple("BNat@UFCons_API", [new SMTVar("path")]);
        
        const emax = tdecl.enums.length.toString();
        const fexp = new SMTLet("vv", bcreate, 
                new SMTIf(SMTCallSimple.makeAndOf(new SMTCallSimple("<=", [new SMTConst("0"), new SMTVar("vv")]), new SMTCallSimple("<", [new SMTVar("vv"), new SMTConst(emax)])),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTVar("vv")),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fexp));
    }

    private generateAPITypeConstructorFunction_Tuple(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const ttuple = tt.options[0] as MIRTupleType;

        const ctors = ttuple.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee, new SMTVar("path"), new SMTConst(i.toString()));
            const ccvar = this.bemitter.generateTempName();

            const chkfun = this.temitter.generateResultIsSuccessTest(ee, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee, new SMTVar(ccvar));

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                (ttuple.entries.length !== 0 ? SMTCallSimple.makeAndOf(...ctors.map((ctor) => ctor.chk as SMTExp)) : new SMTConst("true")),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Record(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const trecord = tt.options[0] as MIRRecordType;

        const ctors = trecord.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee.ptype, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee.ptype, new SMTVar("path"), new SMTVar(i.toString()));
            const ccvar = this.bemitter.generateTempName();

            const chkfun = this.temitter.generateResultIsSuccessTest(ee.ptype, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee.ptype, new SMTVar(ccvar));

            return { pname: ee.pname, ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                (trecord.entries.length !== 0 ? SMTCallSimple.makeAndOf(...ctors.map((ctor) => ctor.chk as SMTExp)) : new SMTConst("true")),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Object(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRObjectEntityTypeDecl;

        const argpath = this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst("0"));
        const maskpath = this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst("1"));

        const ctors = tdecl.consfuncfields.map((ee, i) => {
            const ff = this.temitter.assembly.fieldDecls.get(ee.cfkey) as MIRFieldDecl;
            const fftype = this.temitter.getMIRType(ff.declaredType);

            this.walkAndGenerateHavocType(fftype, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(fftype, argpath, new SMTVar(i.toString()));
            const ccvar = this.bemitter.generateTempName();

            const chkfun = this.temitter.generateResultIsSuccessTest(fftype, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(fftype, new SMTVar(ccvar));

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const optidx = tdecl.consfuncfields.findIndex((param) => param.isoptional);
        let cvalidate: SMTExp = new SMTConst("true");
        let ccons: SMTExp = new SMTConst("[UNDEF]");
        if (optidx === -1) {
            ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access)));

            if(tdecl.validatefunc !== undefined) {
                cvalidate = SMTCallSimple.makeEq(this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")), new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access)));
            }
        }
        else {
            const mask = new SMTMaskConstruct("InputOutputMask");
            if (this.vopts.ActionMode === SymbolicActionMode.EvaluateSymbolic) {
                for(let ii = optidx; ii < tdecl.consfuncfields.length; ++ii) {
                    const idiff = ii - optidx;
                    mask.entries.push(new SMTCallSimple("BBool@UFCons_API", [this.temitter.generateHavocConstructorPathExtend(maskpath, new SMTVar(idiff.toString()))]));
                }
            }
            else {
                for(let ii = optidx; ii < tdecl.consfuncfields.length; ++ii) {
                    mask.entries.push(new SMTConst("true"));
                }
            }

            ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask));

            if(tdecl.validatefunc !== undefined) {
                cvalidate = SMTCallSimple.makeEq(this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")), new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask));
            }
        }
        
        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                SMTCallSimple.makeAndOf(...ctors.map((ctor) => ctor.chk as SMTExp), cvalidate),
                ccons,
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_List(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveListEntityTypeDecl;
        const lentrytype = this.temitter.getMIRType(tdecl.oftype);

        assert(this.vopts.CONTAINER_MAX <= 3, "Only small input containters supported right now");
        const clen = new SMTCallSimple("ContainerSize@UFCons_API", [new SMTVar("path")]);

        const vv1 = this.temitter.assembly.typeMap.get(`Vector1<${tdecl.oftype}>`) as MIRType;
        const ehavoc1 = this.temitter.generateHavocConstructorCall(lentrytype, new SMTVar("path"), new SMTConst("1"));
        const ccvar1 = this.bemitter.generateTempName();
        const chkfun1 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar1));
        const access1 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar1));

        const vv2 = this.temitter.assembly.typeMap.get(`Vector2<${tdecl.oftype}>`) as MIRType;
        const ehavoc2 = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType(tdecl.oftype), new SMTVar("path"), new SMTConst("2"));
        const ccvar2 = this.bemitter.generateTempName();
        const chkfun2 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar2));
        const access2 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar2));

        const vv3 = this.temitter.assembly.typeMap.get(`Vector3<${tdecl.oftype}>`) as MIRType;
        const ehavoc3 = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType(tdecl.oftype), new SMTVar("path"), new SMTConst("3"));
        const ccvar3 = this.bemitter.generateTempName();
        const chkfun3 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar3));
        const access3 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar3));

        const chk1: SMTExp = chkfun1;
        const cons1: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv1).cons, [access1]), vv1, tt));

        const chk2: SMTExp = SMTCallSimple.makeOrOf(chkfun1, chkfun2);
        const cons2: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv2).cons, [access1, access2]), vv2, tt));

        const chk3: SMTExp = SMTCallSimple.makeOrOf(chkfun1, chkfun2, chkfun3);
        const cons3: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv3).cons, [access1, access2, access3]), vv3, tt));

        const hbody = new SMTLet("clen", clen,
                new SMTIf(SMTCallSimple.makeOrOf(new SMTCallSimple("<", [new SMTVar("clen"), new SMTConst("0")]), new SMTCallSimple("<", [new SMTConst("@CONTAINERMAX"), new SMTVar("clen")])),
                    this.temitter.generateErrorResultAssert(tt),
                    new SMTLet("len", this.temitter.generateResultGetSuccess(this.temitter.getMIRType("BNat"), new SMTVar("clen")),
                        new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("0")),
                            new SMTConst("BTerm@none"),
                            new SMTLet(ccvar1, ehavoc1,
                                new SMTIf(chk1,
                                    this.temitter.generateErrorResultAssert(tt),
                                    new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("1")),
                                        cons1,
                                        new SMTLet(ccvar2, ehavoc2,
                                            new SMTIf(chk2,
                                                this.temitter.generateErrorResultAssert(tt),
                                                new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("2")),
                                                    cons2,
                                                    new SMTLet(ccvar3, ehavoc3,
                                                        new SMTIf(chk3,
                                                            this.temitter.generateErrorResultAssert(tt),
                                                            cons3
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), hbody));
    }

    private generateAPITypeConstructorFunction_Stack(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        assert(false, "generateAPITypeConstructorFunction_Stack");
    }

    private generateAPITypeConstructorFunction_Queue(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        assert(false, "generateAPITypeConstructorFunction_Queue");
    }

    private generateAPITypeConstructorFunction_Set(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        assert(false, "generateAPITypeConstructorFunction_Set");
    }

    private generateAPITypeConstructorFunction_Map(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveMapEntityTypeDecl;
        const lentrytype = this.temitter.getMIRType(tdecl.oftype);
        const keytype = tdecl.getTypeK();

        assert(this.vopts.CONTAINER_MAX <= 3, "Only small input containters supported right now");
        const clen = new SMTCallSimple("ContainerSize@UFCons_API", [new SMTVar("path")]);

        const vv1 = this.temitter.assembly.typeMap.get(`Vector1<${tdecl.oftype}>`) as MIRType;
        const ehavoc1 = this.temitter.generateHavocConstructorCall(lentrytype, new SMTVar("path"), new SMTConst("1"));
        const ccvar1 = this.bemitter.generateTempName();
        const chkfun1 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar1));
        const access1 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar1));
        const accesskey1 = new SMTCallSimple(this.temitter.generateTupleIndexGetFunction(lentrytype.options[0] as MIRTupleType, 0), [this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar1))]);

        const vv2 = this.temitter.assembly.typeMap.get(`Vector2<${tdecl.oftype}>`) as MIRType;
        const ehavoc2 = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType(tdecl.oftype), new SMTVar("path"), new SMTConst("2"));
        const ccvar2 = this.bemitter.generateTempName();
        const chkfun2 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar2));
        const access2 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar2));
        const accesskey2 = new SMTCallSimple(this.temitter.generateTupleIndexGetFunction(lentrytype.options[0] as MIRTupleType, 0), [this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar2))]);

        const vv3 = this.temitter.assembly.typeMap.get(`Vector3<${tdecl.oftype}>`) as MIRType;
        const ehavoc3 = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType(tdecl.oftype), new SMTVar("path"), new SMTConst("3"));
        const ccvar3 = this.bemitter.generateTempName();
        const chkfun3 = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar3));
        const access3 = this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar3));
        const accesskey3 = new SMTCallSimple(this.temitter.generateTupleIndexGetFunction(lentrytype.options[0] as MIRTupleType, 0), [this.temitter.generateResultGetSuccess(lentrytype, new SMTVar(ccvar3))]);

        const chk1: SMTExp = chkfun1;
        const cons1: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv1).cons, [access1]), vv1, tt));

        const chkorder12: SMTExp = SMTCallSimple.makeNot(this.bemitter.generateBinKeyCmpFor(keytype, keytype, accesskey1, keytype, accesskey2));
        const chk2: SMTExp = SMTCallSimple.makeOrOf(chkfun1, chkfun2, chkorder12);
        const cons2: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv2).cons, [access1, access2]), vv2, tt));

        const chkorder23: SMTExp = SMTCallSimple.makeNot(this.bemitter.generateBinKeyCmpFor(keytype, keytype, accesskey2, keytype, accesskey3));
        const chk3: SMTExp = SMTCallSimple.makeOrOf(chkfun1, chkfun2, chkfun3, chkorder12, chkorder23);
        const cons3: SMTExp = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(new SMTCallSimple(this.temitter.getSMTConstructorName(vv3).cons, [access1, access2, access3]), vv3, tt));

        const hbody = new SMTLet("clen", clen,
                new SMTIf(SMTCallSimple.makeOrOf(new SMTCallSimple("<", [new SMTVar("clen"), new SMTConst("0")]), new SMTCallSimple("<", [new SMTConst("@CONTAINERMAX"), new SMTVar("clen")])),
                    this.temitter.generateErrorResultAssert(tt),
                    new SMTLet("len", this.temitter.generateResultGetSuccess(this.temitter.getMIRType("BNat"), new SMTVar("clen")),
                        new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("0")),
                            new SMTConst("BTerm@none"),
                            new SMTLet(ccvar1, ehavoc1,
                                new SMTIf(chk1,
                                    this.temitter.generateErrorResultAssert(tt),
                                    new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("1")),
                                        cons1,
                                        new SMTLet(ccvar2, ehavoc2,
                                            new SMTIf(chk2,
                                                this.temitter.generateErrorResultAssert(tt),
                                                new SMTIf(SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("2")),
                                                    cons2,
                                                    new SMTLet(ccvar3, ehavoc3,
                                                        new SMTIf(chk3,
                                                            this.temitter.generateErrorResultAssert(tt),
                                                            cons3
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                );

        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), hbody));
    }

    private generateAPITypeConstructorFunction_Union(tt: MIRType, opts: MIRTypeOption[], havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));

        for(let i = 0; i < opts.length; ++i) {
            this.walkAndGenerateHavocType(this.temitter.getMIRType(opts[i].typeID), havocfuncs, ufuncs);
        }

        const bselect = new SMTCallSimple("UnionChoice@UFCons_API", [new SMTVar("path")]);
        let ccv = new SMTVar("cc");

        let bexp: SMTExp = this.temitter.generateErrorResultAssert(tt);
        for(let i = 0; i < opts.length; ++i) {
            let ofidx = opts.length - (i + 1);
            let oftt = this.temitter.getMIRType(opts[ofidx].typeID);

            const cc = this.temitter.generateHavocConstructorCall(oftt, new SMTVar("path"), new SMTConst(ofidx.toString()));
            const ccvar = this.bemitter.generateTempName();

            const chkfun = this.temitter.generateResultIsSuccessTest(oftt, new SMTVar(ccvar)); 
            const access = this.temitter.generateResultGetSuccess(oftt, new SMTVar(ccvar));

            bexp = new SMTIf(
                new SMTCallSimple("=", [ccv, new SMTConst(ofidx.toString())]),
                new SMTLet(ccvar, cc,
                    new SMTIf(
                        chkfun,
                        this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.coerce(access, oftt, tt)),
                        this.temitter.generateErrorResultAssert(tt)
                    )
                ),
                bexp
            );
        }

        let fbody: SMTExp = new SMTLet("cc", bselect, bexp);
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private processEntityDecl(edecl: MIRObjectEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: edecl.fields.map((fd) => {
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(fd.declaredType), true) };
            })
        };

        const smtdecl = new SMTEntityStdDecl(smttype.smttypename, smttype.smttypetag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }
    
    private processStringOfEntityDecl(edecl: MIRStringOfInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataStringEntityDecl(edecl: MIRDataStringInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataBufferEntityDecl(edecl: MIRDataBufferInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(false, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BByteBuffer");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processConstructableEntityDecl(edecl: MIRConstructableEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const oftype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(edecl.fromtype));
        const iskey = this.bemitter.assembly.subtypeOf(this.temitter.getMIRType(edecl.fromtype), this.temitter.getMIRType("KeyType"));

        const smtdecl = new SMTEntityOfTypeDecl(iskey, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, oftype.smttypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEntityInternalOfTypeDecl(edecl: MIRConstructableInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const oftype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(edecl.fromtype));
        
        const smtdecl = new SMTEntityInternalOfTypeDecl(this.temitter.lookupTypeName(edecl.tkey), smttype.smttypetag, consfuncs.box, consfuncs.bfield, oftype.smttypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEnumEntityDecl(edecl: MIREnumEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BNat");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processPrimitiveListEntityDecl(edecl: MIRPrimitiveListEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityCollectionTypeDecl(smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processPrimitiveStackEntityDecl(edecl: MIRPrimitiveStackEntityTypeDecl) {
        assert(false, "MIRPrimitiveStackEntityTypeDecl");
    }

    private processPrimitiveQueueEntityDecl(edecl: MIRPrimitiveQueueEntityTypeDecl) {
        assert(false, "MIRPrimitiveQueueEntityTypeDecl");
    }

    private processPrimitiveSetEntityDecl(edecl: MIRPrimitiveSetEntityTypeDecl) {
        assert(false, "MIRPrimitiveSetEntityTypeDecl");
    }

    private processPrimitiveMapEntityDecl(edecl: MIRPrimitiveMapEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);

        const smtdecl = new SMTEntityCollectionTypeDecl(smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processVirtualInvokes() {
        for(let i = this.lastVInvokeIdx; i < this.bemitter.requiredVirtualFunctionInvokes.length; ++i) {
            this.bemitter.generateVirtualFunctionInvoke(this.bemitter.requiredVirtualFunctionInvokes[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredVirtualFunctionInvokes.length;

        for(let i = this.lastVOperatorIdx; i < this.bemitter.requiredVirtualOperatorInvokes.length; ++i) {
            this.bemitter.generateVirtualOperatorInvoke(this.bemitter.requiredVirtualOperatorInvokes[i]);
        }
        this.lastVOperatorIdx = this.bemitter.requiredVirtualOperatorInvokes.length;
    }

    private processVirtualEntityUpdates() {
        for(let i = this.lastVEntityUpdateIdx; i < this.bemitter.requiredUpdateVirtualEntity.length; ++i) {
            this.bemitter.generateUpdateEntityFieldVirtual(this.bemitter.requiredUpdateVirtualEntity[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredUpdateVirtualEntity.length;
    }

    private walkAndGenerateHavocType(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        if(havocfuncs.has(this.temitter.generateHavocConstructorName(tt))) {
            return; //already generated function
        }

        if (tt.options.length !== 1) {
            this.generateAPITypeConstructorFunction_Union(tt, tt.options, havocfuncs, ufuncs);
        }
        else {
            if (this.temitter.isUniqueTupleType(tt)) {
                this.generateAPITypeConstructorFunction_Tuple(tt, havocfuncs, ufuncs);
            }
            else if (this.temitter.isUniqueRecordType(tt)) {
                this.generateAPITypeConstructorFunction_Record(tt, havocfuncs, ufuncs);
            }
            else if (this.temitter.isUniqueEntityType(tt)) {
                const etype = tt.options[0] as MIREntityType;
                const edecl = this.temitter.assembly.entityDecls.get(etype.typeID) as MIREntityTypeDecl;
 
                if (edecl.attributes.includes("__stringof_type")) {
                    this.generateAPITypeConstructorFunction_StringOf(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__datastring_type")) {
                    this.generateAPITypeConstructorFunction_DataString(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__databuffer_type")) {
                    this.generateAPITypeConstructorFunction_DataBuffer(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__typedprimitive")) {
                    this.generateAPITypeConstructorFunction_TypedPrimitive(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__enum_type")) {
                    this.generateAPITypeConstructorFunction_Enum(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__ok_type")) {
                    this.generateAPITypeConstructorFunction_Ok(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__err_type")) {
                    this.generateAPITypeConstructorFunction_Err(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__something_type")) {
                    this.generateAPITypeConstructorFunction_Something(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__list_type")) {
                    this.generateAPITypeConstructorFunction_List(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__stack_type")) {
                    this.generateAPITypeConstructorFunction_Stack(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__queue_type")) {
                    this.generateAPITypeConstructorFunction_Queue(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__set_type")) {
                    this.generateAPITypeConstructorFunction_Set(tt, havocfuncs, ufuncs);
                }
                else if (edecl.attributes.includes("__map_type")) {
                    this.generateAPITypeConstructorFunction_Map(tt, havocfuncs, ufuncs);
                }
                else if (edecl instanceof MIRObjectEntityTypeDecl) {
                    this.generateAPITypeConstructorFunction_Object(tt, havocfuncs, ufuncs);
                }
                else {
                    //Don't need to do anything
                }
            }
            else if (tt.options[0] instanceof MIRConceptType) {
                const etypes = [...this.temitter.assembly.entityDecls].filter((edi) => this.temitter.assembly.subtypeOf(this.temitter.getMIRType(edi[1].tkey), this.temitter.getMIRType(tt.typeID)));
                const opts: MIRTypeOption[] = etypes.map((opt) => this.temitter.getMIRType(opt[1].tkey).options[0]);

                this.generateAPITypeConstructorFunction_Union(tt, opts, havocfuncs, ufuncs);
            }
            else {
                //Don't need to do anything
            }
        }
    }

    private initializeSMTAssembly(assembly: MIRAssembly, istestbuild: boolean, entrypoint: MIRInvokeKey, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>) {
        const cginfo = constructCallGraphInfo([entrypoint], assembly, istestbuild);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            
            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            for (let mi = 0; mi < worklist.length; ++mi) {
                const ikey = worklist[mi];

                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = this.bemitter.generateSMTInvoke(idcl);
                this.processVirtualInvokes();
                this.processVirtualEntityUpdates();

                if (finfo !== undefined) {
                    if (finfo instanceof SMTFunction) {
                        this.assembly.functions.push(finfo);
                    }
                    else {
                        this.assembly.uninterpfunctions.push(finfo);
                    }
                }
            }
        }

        assembly.typeMap.forEach((tt) => {
            const restype = this.temitter.getSMTTypeFor(tt);
            if (this.assembly.resultTypes.find((rtt) => rtt.ctype.smttypename === restype.smttypename) === undefined) {
                this.assembly.resultTypes.push(({ hasFlag: false, rtname: tt.typeID, ctype: restype }));
            }
        });

        this.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => this.assembly.functions.push(this.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        this.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => this.assembly.functions.push(this.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        this.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => this.assembly.functions.push(this.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.assembly.functions.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.assembly.functions.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.assembly.functions.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        this.bemitter.requiredSingletonConstructorsList.forEach((scl) => this.assembly.functions.push(this.bemitter.generateSingletonConstructorList(scl)));
        this.bemitter.requiredSingletonConstructorsMap.forEach((scm) => this.assembly.functions.push(this.bemitter.generateSingletonConstructorMap(scm)));

        this.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => this.assembly.functions.push(this.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        this.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => this.assembly.functions.push(this.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        
        const iargs = mirep.params.map((param, i) => {
            const mirptype = this.temitter.getMIRType(param.type);
            const vname = this.bemitter.varStringToSMT(param.name).vname;

            let ufuncs: SMTFunctionUninterpreted[] = [];
            this.walkAndGenerateHavocType(mirptype, this.assembly.havocfuncs, []);
            ufuncs.forEach((uf) => {
                if(this.assembly.uninterpfunctions.find((f) => SMTFunctionUninterpreted.areDuplicates(f, uf)) === undefined) {
                    this.assembly.uninterpfunctions.push(uf);
                }
            });

            const vexp = this.temitter.generateHavocConstructorCall(mirptype, new SMTCallSimple("seq.unit", [new SMTConst("0")]), new SMTConst(i.toString()));
            return { vname: vname, vtype: this.temitter.generateResultType(mirptype), vinit: vexp, vchk: this.temitter.generateResultIsSuccessTest(mirptype, new SMTVar(vname)), callexp: this.temitter.generateResultGetSuccess(mirptype, new SMTVar(vname)) };
        });

        const restype = this.temitter.getMIRType(mirep.resultType);
        let rarg:  { vname: string, vtype: SMTTypeInfo, vchk: SMTExp | undefined, vinit: SMTExp, callexp: SMTExp } | undefined = undefined;
        if (this.vopts.ActionMode === SymbolicActionMode.EvaluateSymbolic) {
            let ufuncs: SMTFunctionUninterpreted[] = [];
            this.walkAndGenerateHavocType(restype, this.assembly.havocfuncs, ufuncs);
            ufuncs.forEach((uf) => {
                if (this.assembly.uninterpfunctions.find((f) => SMTFunctionUninterpreted.areDuplicates(f, uf)) === undefined) {
                    this.assembly.uninterpfunctions.push(uf);
                }
            });

            const resvexp = this.temitter.generateHavocConstructorCall(restype, new SMTConst("(as seq.empty (Seq BNat))"), new SMTConst("1"));
            rarg = { vname: "_@smtres@_arg", vtype: this.temitter.generateResultType(restype), vinit: resvexp, vchk: this.temitter.generateResultIsSuccessTest(restype, new SMTVar("_@smtres@_arg")), callexp: this.temitter.generateResultGetSuccess(restype, new SMTVar("_@smtres@_arg")) };
        }

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = this.temitter.getMIRType(edcl.tkey);
            const ttag = this.temitter.getSMTTypeFor(mirtype).smttypetag;

            if (!this.assembly.typeTags.includes(ttag)) {
                this.assembly.typeTags.push(ttag);
            }

            if (!this.assembly.keytypeTags.includes(ttag)) {
                if (assembly.subtypeOf(mirtype, this.temitter.getMIRType("KeyType"))) {
                    this.assembly.keytypeTags.push(ttag);
                }
            }

            if (edcl instanceof MIRObjectEntityTypeDecl) {
                this.processEntityDecl(edcl);
            }
            else if (edcl.attributes.includes("__stringof_type")) {
                this.processStringOfEntityDecl(edcl as MIRStringOfInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__datastring_type")) {
                this.processDataStringEntityDecl(edcl as MIRDataStringInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__databuffer_type")) {
                this.processDataBufferEntityDecl(edcl as MIRDataBufferInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__typedprimitive")) {
                this.processConstructableEntityDecl(edcl as MIRConstructableEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__enum_type")) {
                this.processEnumEntityDecl(edcl as MIREnumEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__ok_type")) {
                this.processEntityInternalOfTypeDecl(edcl as MIRConstructableInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__err_type")) {
                this.processEntityInternalOfTypeDecl(edcl as MIRConstructableInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__something_type")) {
                this.processEntityInternalOfTypeDecl(edcl as MIRConstructableInternalEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__list_type")) {
                this.processPrimitiveListEntityDecl(edcl as MIRPrimitiveListEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__stack_type")) {
                this.processPrimitiveStackEntityDecl(edcl as MIRPrimitiveStackEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__queue_type")) {
                this.processPrimitiveQueueEntityDecl(edcl as MIRPrimitiveQueueEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__set_type")) {
                this.processPrimitiveSetEntityDecl(edcl as MIRPrimitiveSetEntityTypeDecl);
            }
            else if (edcl.attributes.includes("__map_type")) {
                this.processPrimitiveMapEntityDecl(edcl as MIRPrimitiveMapEntityTypeDecl);
            }
            else {
                //Don't need to do anything -- including for collection decls which all map to BTerm
            }
        });

        this.bemitter.requiredSubtypeTagChecks.forEach((stc) => {
            const occ = stc.oftype.options[0] as MIRConceptType;
            for(let i = 0; i < occ.ckeys.length; ++i) {
                const atname = `AbstractTypeTag_${this.temitter.getSMTTypeFor(this.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!this.assembly.abstractTypes.includes(atname)) {
                    this.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = this.temitter.getSMTTypeFor(mtype).smttypetag;

                        if(this.assembly.subtypeRelation.find((ee) => ee.ttype === ttag && ee.atype === atname) === undefined) {
                            const issub = assembly.subtypeOf(mtype, stc.oftype);
                            this.assembly.subtypeRelation.push({ttype: ttag, atype: atname, value: issub});
                        }
                    }
                });
            }
        });

        this.bemitter.requiredIndexTagChecks.forEach((itc) => {
            const itag = `TupleIndexTag_${itc.idx}`;
            if(!this.assembly.indexTags.includes(itag)) {
                this.assembly.indexTags.push(itag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, itc.oftype)) {
                    const ttype = mtype.options[0] as MIRTupleType;
                    const ttag = this.temitter.getSMTTypeFor(mtype).smttypetag;

                    if (this.assembly.hasIndexRelation.find((ee) => ee.idxtag === itag && ee.atype === ttag) === undefined) {
                        const hasidx = itc.idx < ttype.entries.length;
                        this.assembly.hasIndexRelation.push({ idxtag: itag, atype: ttag, value: hasidx });
                    }
                }
            });
        });

        this.bemitter.requiredRecordTagChecks.forEach((rtc) => {
            const ptag = `RecordPropertyTag_${rtc.pname}`;
            if(!this.assembly.propertyTags.includes(ptag)) {
                this.assembly.propertyTags.push(ptag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, rtc.oftype)) {
                    const ttype = mtype.options[0] as MIRRecordType;
                    const ttag = this.temitter.getSMTTypeFor(mtype).smttypetag;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.pname === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.typeID);
            const ttag = this.temitter.getSMTTypeFor(mirtype).smttypetag;

            this.assembly.typeTags.push(ttag);
            ttup.entries.map((entry) => {
                const etype = this.temitter.getSMTTypeFor(entry);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.smttypename === etype.smttypename) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.typeID, ctype: etype }));
                }
            });
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getSMTTypeFor(entry) };
            });

            this.assembly.tupleDecls.push(new SMTTupleDecl(smttype.smttypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.typeID);
            const ttag = this.temitter.getSMTTypeFor(mirtype).smttypetag;

            this.assembly.typeTags.push(ttag);
            trec.entries.map((entry) => {
                const etype = this.temitter.getSMTTypeFor(entry.ptype);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.smttypename === etype.smttypename) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.ptype.typeID, ctype: etype }));
                }
            });

            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.pname), ftype: this.temitter.getSMTTypeFor(entry.ptype) };
            });

            this.assembly.recordDecls.push(new SMTRecordDecl(smttype.smttypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.typeID);
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getSMTTypeFor(entry) };
            });

            this.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.smttypename, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = this.temitter.lookupGlobalName(cdecl.gkey);
            const consf = this.temitter.lookupFunctionName(cdecl.ivalue);
            const ctype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(cdecl.declaredType));

            let optenumname: [string, string] | undefined = undefined;
            if(cdecl.attributes.includes("enum")) {
                optenumname = [cdecl.enclosingDecl as string, cdecl.gkey];
            }

            if((callsafety.get(cdecl.ivalue) as {safe: boolean, trgt: boolean}).safe) {
                this.assembly.constantDecls.push(new SMTConstantDecl(smtname, optenumname, ctype, consf, new SMTConst(consf), undefined));
            }
            else {
                const rconsf = this.temitter.generateResultGetSuccess(this.temitter.getMIRType(cdecl.declaredType), new SMTConst(consf));
                const rcheck = this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType(cdecl.declaredType), new SMTConst(consf));

                this.assembly.constantDecls.push(new SMTConstantDecl(smtname, optenumname, ctype, consf, rconsf, rcheck));
            }
        });

        this.assembly.maskSizes = this.bemitter.maskSizes;

        const smtcall = this.temitter.lookupFunctionName(mirep.ikey);
        const callargs = iargs.map((arg) => arg.callexp);
        const issafe = (callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

        let iexp: SMTExp | undefined = undefined;
        let argchk: SMTExp[] | undefined = undefined;
        let targeterrorcheck: SMTExp | undefined = undefined;
        let isvaluecheck: SMTExp | undefined = undefined;
        let isvaluefalsechk: SMTExp | undefined = undefined;
        if(issafe) {
            iexp = this.temitter.generateResultTypeConstructorSuccess(restype, new SMTCallSimple(smtcall, callargs));

            targeterrorcheck = new SMTConst("false");
            isvaluecheck = new SMTConst("true");
            isvaluefalsechk = SMTCallSimple.makeNot(this.temitter.generateResultGetSuccess(restype, new SMTVar("_@smtres@")));
        }
        else {
            iexp = new SMTCallGeneral(smtcall, callargs);
            if(mirep.preconditions !== undefined) {
                argchk = mirep.preconditions.map((pc) => {
                    const ispcsafe = (callsafety.get(pc) as {safe: boolean, trgt: boolean}).safe;
                    if(ispcsafe) {
                        return new SMTCallSimple(this.temitter.lookupFunctionName(pc), callargs); 
                    }
                    else {
                        return SMTCallSimple.makeEq(new SMTCallGeneral(this.temitter.lookupFunctionName(pc), callargs), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));
                    }
                });
            }

            targeterrorcheck = new SMTCallSimple("=", [new SMTVar("_@smtres@"), this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))]);
            isvaluecheck = this.temitter.generateResultIsSuccessTest(restype, new SMTVar("_@smtres@"));
            isvaluefalsechk = (restype.typeID === "Bool") ? SMTCallSimple.makeNot(this.temitter.generateResultGetSuccess(restype, new SMTVar("_@smtres@"))) : new SMTConst("[Not a Bool Result]");
        }
        
        this.bemitter.requiredUFConsts.forEach((ctype) => {
            const ufcc = new SMTFunctionUninterpreted(`${ctype.smttypename}@uicons_UF`, [], ctype);
            this.assembly.uninterpfunctions.push(ufcc);
        });

        this.assembly.model = new SMTModelState(iargs, rarg, argchk, this.temitter.generateResultType(restype), iexp, targeterrorcheck, isvaluecheck, isvaluefalsechk);
        this.assembly.allErrors = this.bemitter.allErrors;
    }

    static generateSMTPayload(assembly: MIRAssembly, istestbuild: boolean, runtime: string, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): string {
        const callsafety = markSafeCalls([entrypoint], assembly, istestbuild, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        assembly.typeMap.forEach((tt) => {
            temitter.internTypeName(tt.typeID);
        });
        assembly.invokeDecls.forEach((idcl) => {
            temitter.internFunctionName(idcl.ikey, idcl.shortname);
        });
        assembly.primitiveInvokeDecls.forEach((idcl) => {
            temitter.internFunctionName(idcl.ikey, idcl.shortname);
        });
        assembly.constantDecls.forEach((cdecl) => {
            temitter.internGlobalName(cdecl.gkey, cdecl.shortname);
        });

        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts, temitter.lookupFunctionName(entrypoint));

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly, vopts);
        smtemit.initializeSMTAssembly(assembly, istestbuild, entrypoint, callsafety);

        ////////////
        const smtinfo = smtemit.assembly.buildSMT2file(runtime);

        return smtinfo;
    }

    static generateSMTAssemblyAllErrors(assembly: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, entrypoint: MIRInvokeKey): { file: string, line: number, pos: number, msg: string }[] {
        const callsafety = markSafeCalls(["__i__" + entrypoint], assembly, istestbuild, undefined);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        assembly.typeMap.forEach((tt) => {
            temitter.internTypeName(tt.typeID);
        });
        assembly.invokeDecls.forEach((idcl) => {
            temitter.internFunctionName(idcl.ikey, idcl.shortname);
        });
        assembly.primitiveInvokeDecls.forEach((idcl) => {
            temitter.internFunctionName(idcl.ikey, idcl.shortname);
        });
        assembly.constantDecls.forEach((cdecl) => {
            temitter.internGlobalName(cdecl.gkey, cdecl.shortname);
        });

        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, {file: "[]", line: -1, pos: -1});
        const smtassembly = new SMTAssembly(vopts, temitter.lookupFunctionName(entrypoint));

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly, vopts);
        smtemit.initializeSMTAssembly(assembly, istestbuild, entrypoint, callsafety);

        return smtemit.assembly.allErrors;
    }
}

export {
    SMTEmitter
};
