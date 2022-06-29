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
import { SMTAssembly, SMTConstantDecl, SMTEntityCollectionEntryTypeDecl, SMTEntityCollectionTypeDecl, SMTEntityInternalOfTypeDecl, SMTEntityOfTypeDecl, SMTEntityStdDecl, SMTEphemeralListDecl, SMTFunction, SMTFunctionUninterpreted, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallSimple, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTMaskConstruct, SMTTypeInfo, SMTVar, VerifierOptions } from "./smt_exp";

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;
    readonly vopts: VerifierOptions;
    readonly callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>;

    readonly havocPathType: SMTTypeInfo;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly, vopts: VerifierOptions, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
        this.vopts = vopts;
        this.callsafety = callsafety;

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
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(this.temitter.getMIRType("String"), new SMTVar("str"))),
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
        const oftype = this.temitter.getMIRType(tdecl.valuetype);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall_PassThrough(oftype, new SMTVar("path"));

        let fexp: SMTExp = new SMTConst("[INVALID]");
        if(tdecl.validatefunc === undefined) {
            fexp = new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))),
                this.temitter.generateErrorResultAssert(tt)
            );
        }
        else {
            let cchk: SMTExp = new SMTConst("[UNDEFINED]");
            let ccons: SMTExp = new SMTConst("[Undefined]");
            if((this.callsafety.get(tdecl.validatefunc) as {safe: boolean, trgt: boolean}).safe) {
                cchk = SMTCallSimple.makeAndOf(
                    this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")), 
                    new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.validatefunc), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))])
                );
            }
            else {
                cchk = SMTCallSimple.makeAndOf(
                    this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")), 
                    SMTCallSimple.makeEq(new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.validatefunc), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")))
                );
            }
            
            if(tdecl.usingcons === undefined) {
                ccons = this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv")));
            }
            else {
                if((this.callsafety.get(tdecl.usingcons) as {safe: boolean, trgt: boolean}).safe) {
                    ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.usingcons), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]));
                }
                else {
                    ccons = new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.usingcons), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]);
                }
            }

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
                new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
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
                new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
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
                new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
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
            if(tdecl.validatefunc !== undefined) {
                if((this.callsafety.get(tdecl.validatefunc) as {safe: boolean, trgt: boolean}).safe) {
                    cvalidate = new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.validatefunc as MIRInvokeKey), ctors.map((arg) => arg.access));
                }
                else {
                    cvalidate = SMTCallSimple.makeEq(new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.validatefunc as MIRInvokeKey), ctors.map((arg) => arg.access)), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));
                }
            }

            if((this.callsafety.get(tdecl.consfunc) as {safe: boolean, trgt: boolean}).safe) {
                ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access)));
            }
            else {
                ccons = new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access));
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

            if(tdecl.validatefunc !== undefined) {
                if((this.callsafety.get(tdecl.validatefunc) as {safe: boolean, trgt: boolean}).safe) {
                    cvalidate = new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.validatefunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask);
                }
                else {
                    cvalidate = SMTCallSimple.makeEq(new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.validatefunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("Bool"), new SMTConst("true")));
                }
            }

            if((this.callsafety.get(tdecl.consfunc) as {safe: boolean, trgt: boolean}).safe) {
                ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask));
            }
            else {
                ccons = new SMTCallGeneralWOptMask(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access), mask);
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
        const lentrytype = this.temitter.getMIRType(tdecl.getTypeT().typeID);

        this.walkAndGenerateHavocType(lentrytype, havocfuncs, ufuncs);

        const clen = new SMTCallSimple("ContainerSize@UFCons_API", [new SMTVar("path")]);

        let cargs: SMTExp[] = [];
        for (let i = 0; i < this.vopts.CONTAINER_MAX; ++i) {
            cargs.push(new SMTVar(`carg_${i}`));
        }

        let optblock: SMTExp = new SMTLet(`carg_${this.vopts.CONTAINER_MAX - 1}`, this.temitter.generateHavocConstructorCall(lentrytype, new SMTVar("path"), new SMTConst(`${this.vopts.CONTAINER_MAX - 1}`)),
            new SMTIf(
                this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(`carg_${this.vopts.CONTAINER_MAX - 1}`)),
                this.temitter.generateErrorResultAssert(tt),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateListTypeConstructorSeq(tt, new SMTCallSimple("seq.++", cargs.map((cc) => new SMTCallSimple("seq.unit", [this.temitter.generateResultGetSuccess(lentrytype, cc)])))))
            )
        );

        for (let i = this.vopts.CONTAINER_MAX - 1; i > 0; --i) {
            const ehavoc = this.temitter.generateHavocConstructorCall(lentrytype, new SMTVar("path"), new SMTConst(`${i - 1}`));
            const ccvar = `carg_${i - 1}`;
            const chkfun = this.temitter.generateResultIsErrorTest(lentrytype, new SMTVar(ccvar));

            optblock = new SMTLet(ccvar, ehavoc,
                new SMTIf(
                    chkfun,
                    this.temitter.generateErrorResultAssert(tt),
                    new SMTIf(
                        SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst(`${i}`)),
                        this.temitter.generateResultTypeConstructorSuccess(tt, this.temitter.generateListTypeConstructorSeq(tt, new SMTCallSimple("seq.++", cargs.slice(0, i).map((cc) => new SMTCallSimple("seq.unit", [this.temitter.generateResultGetSuccess(lentrytype, cc)]))))),
                        optblock
                    )
                )
            );
        }

        const hbody = new SMTLet("len", clen,
            new SMTIf(SMTCallSimple.makeOrOf(new SMTCallSimple("<", [new SMTVar("len"), new SMTConst("0")]), new SMTCallSimple("<", [new SMTConst("@CONTAINERMAX"), new SMTVar("len")])),
                this.temitter.generateErrorResultAssert(tt),
                new SMTIf(
                    SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("0")),
                    this.temitter.generateResultTypeConstructorSuccess(tt, new SMTConst(`${this.temitter.getSMTTypeFor(tt).smttypename}@@empty`)),
                    optblock
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

    private generateMapTypeConstructorElements_EntryPoint(ttype: MIRType, keys: SMTExp[], values: SMTExp[]): SMTExp {
        const mirktype = (this.temitter.assembly.entityDecls.get(ttype.typeID) as MIRPrimitiveMapEntityTypeDecl).getTypeK();

        let consargs: SMTExp[] = [];
        for(let i = 0; i < keys.length; ++i) {
            consargs.push(new SMTCallSimple("seq.unit", [this.temitter.generateMapEntryTypeConstructor(ttype, keys[i], values[i])]));
        }
        const consexp = this.temitter.generateMapTypeConstructor(ttype, new SMTCallSimple("seq.++", consargs));

        const smtktype = this.temitter.getSMTTypeFor(mirktype);
        if (consargs.length == 1) {
            return consexp;
        }
        else {
            const cmpop: string = smtktype.isGeneralKeyType() ? `${smtktype.smttypename}@less` : "BKey@less";
            let cmps: SMTExp[] = [];
            for (let i = 0; i < keys.length - 1; ++i) {
                cmps.push(new SMTCallSimple(cmpop, [keys[i], keys[i + 1]]));
            }

            const chkordered = SMTCallSimple.makeAndOf(...cmps);
            return new SMTIf(chkordered,
                this.temitter.generateResultTypeConstructorSuccess(ttype, consexp),
                this.temitter.generateErrorResultAssert(ttype)
            );
        }
    }

    private generateAPITypeConstructorFunction_Map(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveMapEntityTypeDecl;

        const clen = new SMTCallSimple("ContainerSize@UFCons_API", [new SMTVar("path")]);

        this.walkAndGenerateHavocType(tdecl.getTypeK(), havocfuncs, ufuncs);
        this.walkAndGenerateHavocType(tdecl.getTypeV(), havocfuncs, ufuncs);

        let ckeys: SMTExp[] = [];
        let cvalues: SMTExp[] = [];
        for(let i = 0; i < this.vopts.CONTAINER_MAX; ++i) {
            ckeys.push(new SMTVar(`keyarg_${i}`));
            cvalues.push(new SMTVar(`valarg_${i}`))
        }

        let optblock: SMTExp = new SMTLetMulti([
                {
                    vname: `keyarg_${this.vopts.CONTAINER_MAX - 1}`, 
                    value: this.temitter.generateHavocConstructorCall(tdecl.getTypeK(), this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst(`${this.vopts.CONTAINER_MAX - 1}`)), new SMTConst("0"))
                },
                {
                    vname: `valarg_${this.vopts.CONTAINER_MAX - 1}`, 
                    value: this.temitter.generateHavocConstructorCall(tdecl.getTypeV(), this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst(`${this.vopts.CONTAINER_MAX - 1}`)), new SMTConst("1"))
                },
            ],
            new SMTIf(
                SMTCallSimple.makeOrOf(this.temitter.generateResultIsErrorTest(tdecl.getTypeK(), new SMTVar(`keyarg_${this.vopts.CONTAINER_MAX - 1}`)), this.temitter.generateResultIsErrorTest(tdecl.getTypeV(), new SMTVar(`valarg_${this.vopts.CONTAINER_MAX - 1}`))),
                this.temitter.generateErrorResultAssert(tt),
                this.temitter.generateResultTypeConstructorSuccess(tt, this.generateMapTypeConstructorElements_EntryPoint(tt, ckeys.map((cc) => this.temitter.generateResultGetSuccess(tdecl.getTypeK(), cc)), cvalues.map((cc) => this.temitter.generateResultGetSuccess(tdecl.getTypeV(), cc))))
            )
        );
            
        for (let i = this.vopts.CONTAINER_MAX - 1; i > 0; --i) {
            const keyhavoc = this.temitter.generateHavocConstructorCall(tdecl.getTypeK(), this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst(`${i-1}`)), new SMTConst("0"));
            const keyvar = `keyarg_${i-1}`;
            const keychk = this.temitter.generateResultIsErrorTest(tdecl.getTypeK(), new SMTVar(keyvar));

            const valhavoc = this.temitter.generateHavocConstructorCall(tdecl.getTypeV(), this.temitter.generateHavocConstructorPathExtend(new SMTVar("path"), new SMTConst(`${i-1}`)), new SMTConst("1"));
            const valvar = `valarg_${i-1}`;
            const valchk = this.temitter.generateResultIsErrorTest(tdecl.getTypeV(), new SMTVar(valvar));

            optblock = new SMTLetMulti([
                    { vname: keyvar, value: keyhavoc },
                    { vname: valvar, value: valhavoc }
                ], 
                new SMTIf(
                    SMTCallSimple.makeOrOf(keychk, valchk),
                    this.temitter.generateErrorResultAssert(tt),
                    new SMTIf(
                        SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst(`${i}`)),
                        this.temitter.generateResultTypeConstructorSuccess(tt, this.generateMapTypeConstructorElements_EntryPoint(tt, ckeys.slice(0, i).map((cc) => this.temitter.generateResultGetSuccess(tdecl.getTypeK(), cc)), cvalues.slice(0, i).map((cc) => this.temitter.generateResultGetSuccess(tdecl.getTypeV(), cc)))),
                        optblock
                    )
                )
            );
        }
        
        const hbody = new SMTLet("len", clen,
            new SMTIf(SMTCallSimple.makeOrOf(new SMTCallSimple("<", [new SMTVar("len"), new SMTConst("0")]), new SMTCallSimple("<", [new SMTConst("@CONTAINERMAX"), new SMTVar("len")])),
                this.temitter.generateErrorResultAssert(tt),
                new SMTIf(
                    SMTCallSimple.makeEq(new SMTVar("len"), new SMTConst("0")),
                    this.temitter.generateResultTypeConstructorSuccess(tt, new SMTConst(`${this.temitter.getSMTTypeFor(tt).smttypename}@@empty`)),
                    optblock
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
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(fd.declaredType)) };
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
        const oftype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(edecl.valuetype));
        const iskey = this.bemitter.assembly.subtypeOf(this.temitter.getMIRType(edecl.valuetype), this.temitter.getMIRType("KeyType"));

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

        const consopfuncs = this.temitter.getSMTConstructorName(mirtype);

        const consfuncs = this.temitter.generateListTypeConsInfoSeq(mirtype);

        const consdecl = {
            cname: consfuncs.cons,
            cargs: [{ fname: consfuncs.seqf, ftype: `(Seq ${this.temitter.getSMTTypeFor(edecl.getTypeT()).smttypename})` }]
        };

        const efunc = this.temitter.generateListTypeConstructorSeq(mirtype, new SMTConst(`(as seq.empty (Seq ${this.temitter.getSMTTypeFor(edecl.getTypeT()).smttypename}))`));
        const emptyconst = { fkind: smttype.smttypename, fname: smttype.smttypename + "@@empty", fexp: efunc.emitSMT2(undefined) };

        const smtdecl = new SMTEntityCollectionTypeDecl(smttype.smttypename, smttype.smttypetag, consdecl, consopfuncs.box, consopfuncs.bfield, emptyconst, undefined);
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
        const esmttype = this.temitter.generateMapEntryType(mirtype);

        const consopfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consfuncs = this.temitter.generateMapTypeConsInfo(mirtype);

        const efunc = this.temitter.generateMapTypeConstructor(mirtype, new SMTConst(`(as seq.empty (Seq ${esmttype.smttypename}))`));
        const emptyconst = {fkind: smttype.smttypename, fname: smttype.smttypename + "@@empty", fexp: efunc.emitSMT2(undefined)};

        const smtk = this.temitter.getSMTTypeFor(edecl.getTypeK());
        const smtv = this.temitter.getSMTTypeFor(edecl.getTypeV());

        const consdecl = {
            cname: consfuncs.cons,
            cargs: [
                { fname: consfuncs.seqf, ftype: `(Seq ${esmttype.smttypename})`}
            ]
        };

        const econsfuncs = this.temitter.generateMapEntryTypeConsInfo(mirtype);
        const econsdecl = {
            cname: econsfuncs.cons,
            cargs: [
                { fname: econsfuncs.keyf, ftype: smtk.smttypename},
                { fname: econsfuncs.valf, ftype: smtv.smttypename}
            ]
        };

        const esmtdecl = new SMTEntityCollectionEntryTypeDecl(esmttype.smttypename, esmttype.smttypetag, econsdecl);

        const smtdecl = new SMTEntityCollectionTypeDecl(smttype.smttypename, smttype.smttypetag, consdecl, consopfuncs.box, consopfuncs.bfield, emptyconst, esmtdecl);
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
            const etypes = [...this.temitter.assembly.typeMap].filter((edi) => this.temitter.assembly.subtypeOf(edi[1], this.temitter.getMIRType(tt.typeID)));
            const opts: MIRTypeOption[] = etypes.map((opt) => opt[1].options[0]).sort((a, b) => a.typeID.localeCompare(b.typeID));

            let ropts: MIRTypeOption[] = [];
            for(let i = 0; i < opts.length; ++i) {
                const has = ropts.find((ropt) => ropt.typeID === opts[i].typeID) !== undefined;
                if(!has) {
                    ropts.push(opts[i]);
                }
            }

            this.generateAPITypeConstructorFunction_Union(tt, ropts, havocfuncs, ufuncs);
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
                const opts: MIRTypeOption[] = etypes.map((opt) => this.temitter.getMIRType(opt[1].tkey).options[0]).sort((a, b) => a.typeID.localeCompare(b.typeID));

                let ropts: MIRTypeOption[] = [];
                for(let i = 0; i < opts.length; ++i) {
                    const has = ropts.find((ropt) => ropt.typeID === opts[i].typeID) !== undefined;
                    if(!has) {
                        ropts.push(opts[i]);
                    }
                }

                this.generateAPITypeConstructorFunction_Union(tt, ropts, havocfuncs, ufuncs);
            }
            else {
                //Don't need to do anything
            }
        }
    }

    private initializeSMTAssembly(assembly: MIRAssembly, istestbuild: boolean, entrypoint: MIRInvokeKey) {
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
                //Don't need to do anything
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

            if((this.callsafety.get(cdecl.ivalue) as {safe: boolean, trgt: boolean}).safe) {
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
        const issafe = (this.callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

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
                    const ispcsafe = (this.callsafety.get(pc) as {safe: boolean, trgt: boolean}).safe;
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

        this.assembly.uninterpOps = [...this.bemitter.requiredUFOps];

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

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly, vopts, callsafety);
        smtemit.initializeSMTAssembly(assembly, istestbuild, entrypoint);

        ////////////
        const smtinfo = smtemit.assembly.buildSMT2file(runtime);

        return smtinfo;
    }

    static generateSMTAssemblyAllErrors(assembly: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, entrypoint: MIRInvokeKey): { file: string, line: number, pos: number, msg: string }[] {
        const callsafety = markSafeCalls([entrypoint], assembly, istestbuild, undefined);

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

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly, vopts, callsafety);
        smtemit.initializeSMTAssembly(assembly, istestbuild, entrypoint);

        return smtemit.assembly.allErrors;
    }
}

export {
    SMTEmitter
};
