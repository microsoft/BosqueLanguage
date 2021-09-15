//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIREntityType, MIREntityTypeDecl, MIREnumEntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRRecordType, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { ListOpsInfo, SMTConstructorGenCode, SMTDestructorGenCode } from "./smtcollection_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEntityDecl, SMTEphemeralListDecl, SMTFunction, SMTFunctionUninterpreted, SMTListDecl, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

type APIModuleInfo = {
    apitypes: object[],
    apisig: object,
    bvwidth: number,
    constants: object[]
};

type Payload = {
    smt2decl: string, 
    timeout: number, 
    apimodule: APIModuleInfo
};

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;

    readonly havocPathType: SMTType;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;

        this.havocPathType = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::HavocSequence"));
    }

    private generateAPITypeConstructorFunction_BigNat(havocfuncs: Set<String>) {
        const bntype = this.temitter.getMIRType("NSCore::BigNat");

        const fbody = new SMTLet("@vval", new SMTCallSimple("BBigNat@UFCons_API", [new SMTVar("path")]),
            new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst("0")]), 
                this.temitter.generateErrorResultAssert(bntype), 
                this.temitter.generateResultTypeConstructorSuccess(bntype, new SMTVar("@vval")))
            );
        
        havocfuncs.add(this.temitter.generateHavocConstructorName(bntype));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(bntype), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(bntype), fbody));
    }

    private generateAPITypeConstructorFunction_String(havocfuncs: Set<String>) {
        const bcreate = new SMTCallSimple("BString@UFCons_API", [new SMTVar("path")]);

        let fbody: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.bemitter.vopts.StringOpt === "ASCII") {
            fbody = new SMTLet("str", bcreate,
                new SMTIf(new SMTCallSimple("<=", [new SMTCallSimple("str.len", [new SMTVar("str")]), new SMTConst(this.bemitter.numgen.int.natmax.toString(10))]),
                    this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::String"))
                )
            );
        }
        else {
            fbody = new SMTLet("str", bcreate,
                new SMTIf(new SMTCallSimple("<=", [new SMTCallSimple("seq.len", [new SMTVar("str")]), new SMTConst(this.bemitter.numgen.int.natmax.toString(10))]),
                    this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::String"))
                )
            );
        }

        havocfuncs.add(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::String")));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::String")), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(this.temitter.getMIRType("NSCore::String")), fbody));
    }


    private generateAPITypeConstructorFunction_ISOTime(havocfuncs: Set<String>) {
        const bntype = this.temitter.getMIRType("NSCore::ISOTime");

        const fbody = new SMTLet("@vval", new SMTCallSimple("BISOTime@UFCons_API", [new SMTVar("path")]),
            new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst("0")]), 
                this.temitter.generateErrorResultAssert(bntype), 
                this.temitter.generateResultTypeConstructorSuccess(bntype, new SMTVar("@vval")))
            );

        havocfuncs.add(this.temitter.generateHavocConstructorName(bntype));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(bntype), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(bntype), fbody));
    }

    private generateAPITypeConstructorFunction_LogicalTime(havocfuncs: Set<String>) {
        const bntype = this.temitter.getMIRType("NSCore::LogicalTime");

        const fbody = new SMTLet("@vval", new SMTCallSimple("BLogicalTime@UFCons_API", [new SMTVar("path")]),
            new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst("0")]), 
                this.temitter.generateErrorResultAssert(bntype), 
                this.temitter.generateResultTypeConstructorSuccess(bntype, new SMTVar("@vval")))
            );

        havocfuncs.add(this.temitter.generateHavocConstructorName(bntype));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(bntype), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(bntype), fbody));
    }

    private generateAPITypeConstructorFunction_UUID(havocfuncs: Set<String>) {
        const bcreate = new SMTCallSimple("BUUID@UFCons_API", [new SMTVar("path")]);

        const fbody: SMTExp = new SMTLet("bb", bcreate,
            new SMTIf(SMTCallSimple.makeEq(new SMTCallSimple("seq.len", [new SMTVar("bb")]), new SMTConst("16")),
                this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::UUID"), new SMTVar("bb")),
                this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::UUID"))
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::UUID")));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::UUID")), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(this.temitter.getMIRType("NSCore::ByteBuffer")), fbody));
    }

    private generateAPITypeConstructorFunction_ByteBuffer(havocfuncs: Set<String>) {
        const bcreate = new SMTCallSimple("BByteBuffer@UFCons_API", [new SMTVar("path")]);

        const fbody: SMTExp = new SMTLet("bb", bcreate,
            new SMTIf(new SMTCallSimple("<=", [new SMTCallSimple("seq.len", [new SMTVar("bb")]), new SMTConst(this.bemitter.numgen.int.natmax.toString(10))]),
                this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("bb")),
                this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::ByteBuffer"))
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::ByteBuffer")));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::ByteBuffer")), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(this.temitter.getMIRType("NSCore::ByteBuffer")), fbody));
    }

    private generateAPITypeConstructorFunction_ValidatedString(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::String"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::String"), new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const vre = this.bemitter.assembly.validatorRegexs.get(ttdecl.fromtype) as BSQRegex;
        const lre = vre.compileToPatternToSMT(this.bemitter.vopts.StringOpt === "ASCII");

        let accept: SMTExp = new SMTConst("false");
        if (this.bemitter.vopts.StringOpt === "ASCII") {
            accept = new SMTCallSimple("str.in.re", [this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), new SMTConst(lre)]);
        }
        else {
            accept = new SMTCallSimple("seq.in.re", [this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), new SMTConst(lre)]);
        }

        const fbody = new SMTLet("str", bcreate,
            new SMTIf(SMTCallSimple.makeAndOf(this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), accept),
                new SMTVar("str"),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_DataString(tt: MIRType, havocfuncs: Set<String>,  ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::String"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::String"), new SMTVar("path"), new SMTConst(`(_ bv${0} ${this.assembly.vopts.ISize})`));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const accepts = this.temitter.lookupFunctionName(ttdecl.optaccepts as MIRInvokeKey);
        const pcheck = SMTCallSimple.makeEq(new SMTCallGeneral(accepts, [new SMTVar("str")]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTConst("true")));

        const fbody = new SMTLet("str", bcreate,
            new SMTIf(SMTCallSimple.makeAndOf(this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), pcheck),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTVar("str")),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_ValidatedBuffer(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::ByteBuffer"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;

        const bcreateval = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType(ttdecl.fromtype), new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(1));
        const uufsmt = this.temitter.getSMTTypeFor(this.temitter.getMIRType(ttdecl.fromtype));
        const uuf = new SMTFunctionUninterpreted(`BByteBuffer@expand_${uufsmt.name}`, [this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::ByteBuffer"))], uufsmt);

        const fbody = new SMTLetMulti([{vname: "bb", value: bcreate}, {vname: "apiv", value: bcreateval}],
            new SMTIf(SMTCallSimple.makeAndOf(
                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("bb")),
                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType(ttdecl.fromtype), new SMTVar("apiv")),
                SMTCallSimple.makeEq(this.temitter.generateResultGetSuccess(this.temitter.getMIRType(ttdecl.fromtype), new SMTVar("apiv")), new SMTCallSimple(`BByteBuffer@expand_${uufsmt.name}`, [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("bb"))]))),
                new SMTVar("bb"),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        ufuncs.push(uuf);
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_DataBuffer(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::ByteBuffer"), havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::String"), havocfuncs, ufuncs);
        const screate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::String"), new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(1));

        const ttdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const accepts = this.temitter.lookupFunctionName(ttdecl.optaccepts as MIRInvokeKey);
        const pcheck = SMTCallSimple.makeEq(new SMTCallGeneral(accepts, [new SMTVar("str")]), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTConst("true")));

        const fbody = new SMTLetMulti([{vname: "bb", value: bcreate}, {vname: "str", value: screate}],
            new SMTIf(SMTCallSimple.makeAndOf(
                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("bb")),
                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")),
                pcheck,
                SMTCallSimple.makeEq(this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), 
                new SMTCallSimple("BByteBuffer@expandstr", [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::ByteBuffer"), new SMTVar("bb"))]))),
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

        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(oftype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        if(tdecl.usingcons === undefined) {
            this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), bcreate));
        }
        else {
            if (!this.bemitter.isSafeConstructorInvoke(tt)) {
                const ccons = new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.usingcons), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]);
                const fbody = new SMTLet("vv", bcreate, 
                    new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
                        new SMTLet("cc", ccons,
                            new SMTIf(this.temitter.generateResultIsSuccessTest(tt, new SMTVar("cc")),
                                new SMTVar("cc"),
                                this.temitter.generateErrorResultAssert(tt)
                            )
                        ),
                        this.temitter.generateErrorResultAssert(tt)
                    )
                );
                this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
            }
            else {
                const ccons = new SMTCallSimple(this.temitter.lookupFunctionName(tdecl.usingcons), [this.temitter.generateResultGetSuccess(oftype, new SMTVar("vv"))]);
                const fbody = new SMTLet("vv", bcreate, 
                    new SMTIf(this.temitter.generateResultIsSuccessTest(oftype, new SMTVar("vv")),
                    this.temitter.generateResultTypeConstructorSuccess(tt, ccons),
                        this.temitter.generateErrorResultAssert(tt)
                    )
                );
                this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
            }
        }
    }

    private generateAPITypeConstructorFunction_Something(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(oftype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), bcreate));
    }

    private generateAPITypeConstructorFunction_Ok(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(oftype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), bcreate));
    }

    private generateAPITypeConstructorFunction_Err(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRConstructableInternalEntityTypeDecl;
        const oftype = this.temitter.getMIRType(tdecl.fromtype);

        this.walkAndGenerateHavocType(oftype, havocfuncs, ufuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(oftype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), bcreate));
    }

    private generateAPITypeConstructorFunction_Enum(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIREnumEntityTypeDecl;

        const fbody = new SMTLet("@vval", new SMTCallSimple("EnumChoice@UFCons_API", [new SMTVar("path")]),
            new SMTIf(new SMTCallSimple("<", [new SMTVar("@vval"), new SMTConst(`${tdecl.enums.length}`)]), 
                this.temitter.generateErrorResultAssert(tt), 
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTVar("@vval")))
            );
    
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Tuple(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const ttuple = tt.options[0] as MIRTupleType;

        const ctors = ttuple.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(i));
            const ccvar = this.bemitter.generateTempName();
            const issafehavoc = this.temitter.isKnownSafeHavocConstructorType(ee);

            const chkfun = issafehavoc ? new SMTConst("true") : this.temitter.generateResultIsSuccessTest(ee, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee, new SMTVar(ccvar));

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                (ttuple.entries.length !== 0 ? SMTCallSimple.makeAndOf(...ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)) : new SMTConst("true")),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Record(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const trecord = tt.options[0] as MIRRecordType;

        const ctors = trecord.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee.ptype, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee.ptype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(i));
            const ccvar = this.bemitter.generateTempName();
            const issafehavoc = this.temitter.isKnownSafeHavocConstructorType(ee.ptype);

            const chkfun = issafehavoc ? new SMTConst("true") : this.temitter.generateResultIsSuccessTest(ee.ptype, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee.ptype, new SMTVar(ccvar));

            return { pname: ee.pname, ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                (trecord.entries.length !== 0 ? SMTCallSimple.makeAndOf(...ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)) : new SMTConst("true")),
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access))),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Object(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.typeID) as MIRObjectEntityTypeDecl;

        const ctors = tdecl.consfuncfields.map((ee, i) => {
            const ff = this.temitter.assembly.fieldDecls.get(ee) as MIRFieldDecl;
            const fftype = this.temitter.getMIRType(ff.declaredType);

            this.walkAndGenerateHavocType(fftype, havocfuncs, ufuncs);
            const cc = this.temitter.generateHavocConstructorCall(fftype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(i));
            const ccvar = this.bemitter.generateTempName();
            const issafehavoc = this.temitter.isKnownSafeHavocConstructorType(fftype);

            const chkfun = issafehavoc ? new SMTConst("true") : this.temitter.generateResultIsSuccessTest(fftype, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(fftype, new SMTVar(ccvar));

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        let ccons: SMTExp = new SMTConst("[UNDEF]");
        if (!this.bemitter.isSafeConstructorInvoke(tt)) {
            ccons = new SMTCallGeneral(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access));
        }
        else {
            ccons = this.temitter.generateResultTypeConstructorSuccess(tt, new SMTCallSimple(this.temitter.lookupFunctionName(tdecl.consfunc as MIRInvokeKey), ctors.map((arg) => arg.access)));
        }

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                (ctors.length !== 0 ? SMTCallSimple.makeAndOf(...ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)) : new SMTConst("true")),
                ccons,
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Union(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        for(let i = 0; i < tt.options.length; ++i) {
            this.walkAndGenerateHavocType(this.temitter.getMIRType(tt.options[i].typeID), havocfuncs, ufuncs);
        }

        const bselect = new SMTCallSimple("UnionChoice@UFCons_API", [new SMTVar("path")]);
        let ccv = new SMTVar("cc");

        let bexp: SMTExp = this.temitter.generateErrorResultAssert(tt);
        for(let i = 0; i < tt.options.length; ++i) {
            let ofidx = tt.options.length - (i + 1);
            let oftt = this.temitter.getMIRType(tt.options[ofidx].typeID);

            const cc = this.temitter.generateHavocConstructorCall(oftt, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(ofidx));
            const ccvar = this.bemitter.generateTempName();
            const issafehavoc = this.temitter.isKnownSafeHavocConstructorType(oftt);

            const chkfun = issafehavoc ? new SMTConst("true") : this.temitter.generateResultIsSuccessTest(oftt, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(oftt, new SMTVar(ccvar));

            bexp = new SMTIf(
                new SMTCallSimple("=", [ccv, this.bemitter.numgen.int.emitSimpleNat(ofidx)]),
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
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_List(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const ldecl = this.temitter.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveListEntityTypeDecl;
        const ctype = this.temitter.getMIRType(ldecl.oftype);
        
        this.walkAndGenerateHavocType(ctype, havocfuncs, ufuncs);

        const invop = this.bemitter.lopsManager.registerHavoc(tt);
        const fbody = new SMTCallGeneral(invop, [new SMTVar("path")]);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Stack(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        //
        //TODO: not implemented yet
        //
        assert(false, "Stack Havoc Not Implemented");
    }

    private generateAPITypeConstructorFunction_Queue(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        //
        //TODO: not implemented yet
        //
        assert(false, "Queue Havoc Not Implemented");
    }

    private generateAPITypeConstructorFunction_Set(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        //
        //TODO: not implemented yet
        //
        assert(false, "Set Havoc Not Implemented");
    }

    private generateAPITypeConstructorFunction_Map(tt: MIRType, havocfuncs: Set<String>, ufuncs: SMTFunctionUninterpreted[]) {
        const mdecl = this.temitter.assembly.entityDecls.get(tt.typeID) as MIRPrimitiveMapEntityTypeDecl;
        const ultype = this.temitter.getMIRType(mdecl.ultype);
        
        const ulcreate = this.temitter.generateHavocConstructorCall(ultype, new SMTVar("path"), this.bemitter.numgen.int.emitSimpleNat(0));

        const chk = new SMTCallGeneral(this.temitter.lookupFunctionName(mdecl.unqchkinv), [this.temitter.generateResultGetSuccess(ultype, new SMTVar("ll"))]);
        const rtrue = this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTConst("true"));
        const fbody = new SMTLet("ll", ulcreate, 
            new SMTIf(this.temitter.generateResultIsSuccessTest(ultype, new SMTVar("ll")),
                    new SMTIf(SMTCallSimple.makeEq(chk, rtrue),
                        new SMTVar("ll"),
                        this.temitter.generateErrorResultAssert(tt)
                    ),
                    this.temitter.generateErrorResultAssert(tt)
                )
            );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: this.havocPathType }], this.temitter.generateResultType(tt), fbody));
    }

    private processConstructorGenInfo(cgen: SMTConstructorGenCode, constructors: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[]) {
        cgen.uf.forEach((uf) => {
            if(this.assembly.uninterpfunctions.find((f) => SMTFunctionUninterpreted.areDuplicates(f, uf)) === undefined) {
                this.assembly.uninterpfunctions.push(uf);
            }
        });

        this.assembly.functions.push(...cgen.if);
        constructors.push(cgen.cons);
    }

    private processDestructorGenInfo(dgen: SMTDestructorGenCode) {
        dgen.uf.forEach((uf) => {
            if(this.assembly.uninterpfunctions.find((f) => SMTFunctionUninterpreted.areDuplicates(f, uf)) === undefined) {
                this.assembly.uninterpfunctions.push(uf);
            }
        });

        this.assembly.functions.push(...dgen.if);
    }
    
    private processListTypeDecl(ldecl: MIRPrimitiveListEntityTypeDecl) {
        const mtype = this.temitter.getMIRType(ldecl.tkey);
        const ltype = this.temitter.getSMTTypeFor(mtype);
        const ctype = this.temitter.getMIRType(ldecl.oftype);
        const nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));
        
        const linfo = this.bemitter.lopsManager.ops.get(ldecl.tkey) as ListOpsInfo;
        const constructors: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[] = [];

        ////
        //cons ops

        if(this.bemitter.lopsManager.rangenat && ctype.typeID == this.temitter.getMIRType("NSCore::Nat").typeID) {
            const crange = this.bemitter.lopsManager.emitConstructorRange(mtype, ltype, ctype);
            this.processConstructorGenInfo(crange, constructors);
        }

        if(this.bemitter.lopsManager.rangeint && ctype.typeID == this.temitter.getMIRType("NSCore::Int").typeID) {
            const crange = this.bemitter.lopsManager.emitConstructorRange(mtype, ltype, ctype);
            this.processConstructorGenInfo(crange, constructors);
        }

        const cempty = this.bemitter.lopsManager.emitConstructorEmpty(mtype, ltype);
        this.processConstructorGenInfo(cempty, constructors);

        const cslice = this.bemitter.lopsManager.emitConstructorSlice(mtype, ltype);
        this.processConstructorGenInfo(cslice, constructors);

        const cconcat2 = this.bemitter.lopsManager.emitConstructorConcat2(mtype, ltype);
        this.processConstructorGenInfo(cconcat2, constructors);

        if(linfo.consops.fill) {
            const cfill = this.bemitter.lopsManager.emitConstructorFill(mtype, ltype, ctype);
            this.processConstructorGenInfo(cfill, constructors);
        }

        if(linfo.consops.havoc) {
            const chavoc = this.bemitter.lopsManager.emitConstructorHavoc(mtype, ltype, ctype);
            this.processConstructorGenInfo(chavoc, constructors);
        }
            
        for (let i = 1; i <= 3; ++i) {
            const ck = this.bemitter.lopsManager.emitConstructorLiteralK(mtype, ltype, ctype, i);
            this.processConstructorGenInfo(ck, constructors);
        }

        linfo.consops.filter.forEach((pcode, code) => {
            const cfilter = this.bemitter.lopsManager.emitConstructorFilter(ltype, mtype, code);
            this.processConstructorGenInfo(cfilter, constructors);
        });

        linfo.consops.map.forEach((minfo, code) => {
            const cmap = this.bemitter.lopsManager.emitConstructorMap(this.temitter.getSMTTypeFor(minfo.fromtype), minfo.totype, minfo.isidx, code, minfo.code);
            this.processConstructorGenInfo(cmap, constructors);
        });
            
        ////
        //des ops

        const dget = this.bemitter.lopsManager.emitDestructorGet(ltype, ctype, linfo.consops);
        this.processDestructorGenInfo(dget);

        linfo.dops.safecheckpred.forEach((pcode, code) => {
            const dsafe = this.bemitter.lopsManager.emitSafeCheckPred(ltype, mtype, pcode.isidx, code, pcode.code);
            this.processDestructorGenInfo(dsafe);
        });

        linfo.dops.safecheckfn.forEach((cinfo, code) => {
            const dsafe = this.bemitter.lopsManager.emitSafeCheckFn(ltype, mtype, cinfo.rtype, cinfo.isidx, code, cinfo.code);
            this.processDestructorGenInfo(dsafe);
        });

        linfo.dops.isequence.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorISequence(ltype, pcode.isidx, code, pcode.code);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.haspredcheck.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorHasPredCheck(ltype, pcode.isidx, code, pcode.code);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.findIndexOf.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorFindIndexOf(ltype, pcode.isidx, code, pcode.code);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.findLastIndexOf.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorFindIndexOfLast(ltype, pcode.isidx, code, pcode.code);
            this.processDestructorGenInfo(disq);
        });

        if(linfo.dops.sum) {
            const disq = this.bemitter.lopsManager.emitDestructorSum(ltype, ctype);
            this.processDestructorGenInfo(disq);
        }

        const ttag = `TypeTag_${ltype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mtype, this.temitter.getMIRType("NSCore::KeyType"));

        const consfuncs = this.temitter.getSMTConstructorName(mtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: [
                { fname: `${ltype.name}@size`, ftype: nattype },
                { fname: `${ltype.name}@uli`, ftype: this.bemitter.lopsManager.generateULITypeFor(ltype) }
            ]
        };

        const emptyconst = `(declare-const ${this.temitter.lookupTypeName(ldecl.tkey)}@empty_const ${ltype.name}) (assert (= ${this.temitter.lookupTypeName(ldecl.tkey)}@empty_const (${this.bemitter.lopsManager.generateConsCallName_Direct(ltype, "empty")})))`;

        const smtdecl = new SMTListDecl(iskey, this.bemitter.lopsManager.generateULITypeFor(ltype).name, constructors, emptyconst, ltype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.listDecls.push(smtdecl);
    }

    private processEntityDecl(edecl: MIRObjectEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const ttag = `TypeTag_${smttype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: edecl.fields.map((fd) => {
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(fd.declaredType)) };
            })
        };

        const smtdecl = new SMTEntityDecl(iskey, smttype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processSpecialEntityDecl(edecl: MIRObjectEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const ttag = `TypeTag_${smttype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const smtdecl = new SMTEntityDecl(iskey, smttype.name, ttag, undefined, consfuncs.box, consfuncs.bfield);
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

        if (this.temitter.isKnownSafeHavocConstructorType(tt)) {
            //Don't need to do anything
        }
        else if (tt.options.length !== 1) {
            this.generateAPITypeConstructorFunction_Union(tt, havocfuncs, ufuncs);
        }
        else if (this.temitter.isUniqueTupleType(tt)) {
            this.generateAPITypeConstructorFunction_Tuple(tt, havocfuncs, ufuncs);
        }
        else if (this.temitter.isUniqueRecordType(tt)) {
            this.generateAPITypeConstructorFunction_Record(tt, havocfuncs, ufuncs);
        }
        else if (this.temitter.isUniqueEntityType(tt)) {
            const etype = tt.options[0] as MIREntityType;
            const edecl = this.temitter.assembly.entityDecls.get(etype.typeID) as MIREntityTypeDecl;

            if (this.temitter.isType(tt, "NSCore::BigNat")) {
                this.generateAPITypeConstructorFunction_BigNat(havocfuncs);
            }
            else if (this.temitter.isType(tt, "NSCore::Rational")) {
                //TODO: this needs to construct num/denom explicitly
                assert(false);
            }
            else if (this.temitter.isType(tt, "NSCore::String")) {
                this.generateAPITypeConstructorFunction_String(havocfuncs);
            }
            else if (this.temitter.isType(tt, "NSCore::ISOTime")) {
                assert(false);
            }
            else if (this.temitter.isType(tt, "NSCore::LogicalTime")) {
                assert(false);
            }
            else if (this.temitter.isType(tt, "NSCore::UUID")) {
                assert(false);
            }
            else if (this.temitter.isType(tt, "NSCore::ContentHash")) {
                assert(false);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
                this.generateAPITypeConstructorFunction_TypedNumber(tt, havocfuncs);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
                this.generateAPITypeConstructorFunction_ValidatedString(tt, havocfuncs);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                this.generateAPITypeConstructorFunction_List(tt, havocfuncs);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                this.generateAPITypeConstructorFunction_Set(tt, havocfuncs);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                this.generateAPITypeConstructorFunction_Map(tt, havocfuncs);
            }
            else if(edecl.specialDecls.has(MIRSpecialTypeCategory.EnumTypeDecl)) {
                this.generateAPITypeConstructorFunction_Enum(tt, havocfuncs);
            }
            else {
                //Don't need to do anything
            }
        }
        else {
            //Don't need to do anything
        }
    }

    private initializeSMTAssembly(assembly: MIRAssembly, entrypoint: MIRInvokeKey, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>) {
        const cinits = [...assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const cginfo = constructCallGraphInfo([entrypoint, ...cinits], assembly);
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
            if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({ hasFlag: false, rtname: tt.trkey, ctype: restype }));
            }
        });

        this.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => this.assembly.functions.push(this.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        this.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => this.assembly.functions.push(this.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        this.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => this.assembly.functions.push(this.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.assembly.functions.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.assembly.functions.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.assembly.functions.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        this.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => this.assembly.functions.push(this.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        this.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => this.assembly.functions.push(this.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        
        const iargs = mirep.params.map((param, i) => {
            const mirptype = this.temitter.getMIRType(param.type);
            const vname = this.temitter.mangle(param.name);

            this.walkAndGenerateHavocType(mirptype, this.assembly.havocfuncs);
            const vexp = this.temitter.generateHavocConstructorCall(mirptype, new SMTCallSimple("seq.unit", [new SMTConst(`(_ bv${0} ${this.assembly.vopts.ISize})`)]), new SMTConst(`(_ bv${i} ${this.assembly.vopts.ISize})`));

            return { vname: vname, vtype: this.temitter.generateResultType(mirptype), vinit: vexp, vchk: this.temitter.generateResultIsSuccessTest(mirptype, new SMTVar(vname)), callexp: this.temitter.generateResultGetSuccess(mirptype, new SMTVar(vname)) };
        });

        const restype = this.temitter.getMIRType(mirep.resultType);
        this.walkAndGenerateHavocType(restype, this.assembly.havocfuncs);
        const resvexp = this.temitter.generateHavocConstructorCall(restype, new SMTConst("(as seq.empty (Seq BNat))"), new SMTConst(`(_ bv${1} ${this.assembly.vopts.ISize})`));
        const rarg = { vname: "_@smtres@_arg", vtype: this.temitter.generateResultType(restype), vinit: resvexp, vchk: this.temitter.generateResultIsSuccessTest(restype, new SMTVar("_@smtres@_arg")), callexp: this.temitter.generateResultGetSuccess(restype, new SMTVar("_@smtres@_arg")) };

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = this.temitter.getMIRType(edcl.tkey);
            const ttag = this.temitter.getSMTTypeTag(mirtype);

            if (!this.assembly.typeTags.includes(ttag)) {
                this.assembly.typeTags.push(ttag);
            }

            if (!this.assembly.keytypeTags.includes(ttag)) {
                if (assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"))) {
                    this.assembly.keytypeTags.push(ttag);
                }
            }

            if (edcl.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
                this.processVectorTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                this.processListTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
                this.processStackTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
                this.processQueueTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                this.processSetTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                this.processMapTypeDecl(edcl);
            }
            else {
                if (edcl.ns !== "NSCore" || BuiltinEntityDeclNames.find((be) => be === edcl.name) === undefined) {
                    this.processEntityDecl(edcl);
                }
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
                        const ttag = this.temitter.getSMTTypeTag(mtype);

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
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype).name}`;

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
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype).name}`;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.name === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype).name}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }

            ttup.entries.filter((entry) => entry.isOptional).map((entry) => {
                const etype = this.temitter.getSMTTypeFor(entry.type);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === etype.name) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.type.trkey, ctype: etype }));
                }
            });
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.tupleDecls.push(new SMTTupleDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype).name}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }
            
            trec.entries.filter((entry) => entry.isOptional).map((entry) => {
                const etype = this.temitter.getSMTTypeFor(entry.type);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === etype.name) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.type.trkey, ctype: etype }));
                }
            });

            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.name), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.recordDecls.push(new SMTRecordDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.trkey);
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getSMTTypeFor(entry) };
            });

            this.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.name, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = this.temitter.lookupGlobalName(cdecl.gkey);
            const consf = this.temitter.lookupFunctionName(cdecl.ivalue);
            const ctype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(cdecl.declaredType));

            let optenumname: [string, string] | undefined = undefined;
            if(cdecl.attributes.includes("enum")) {
                optenumname = [cdecl.enclosingDecl as string, cdecl.gkey];
            }

            this.assembly.constantDecls.push(new SMTConstantDecl(smtname, optenumname, ctype, consf));
        });

        this.assembly.maskSizes = this.bemitter.maskSizes;

        const smtcall = this.temitter.mangle(mirep.key);
        const callargs = iargs.map((arg) => arg.callexp);
        const issafe = (callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

        let iexp: SMTExp | undefined = undefined;
        let argchk: SMTExp[] | undefined = undefined;
        let targeterrorcheck: SMTExp | undefined = undefined;
        let isvaluecheck: SMTExp | undefined = undefined;
        if(issafe) {
            iexp = this.temitter.generateResultTypeConstructorSuccess(restype, new SMTCallSimple(smtcall, callargs));

            targeterrorcheck = new SMTConst("false");
            isvaluecheck = new SMTConst("true");
        }
        else {
            iexp = new SMTCallGeneral(smtcall, callargs);
            if(mirep.preconditions !== undefined) {
                argchk = mirep.preconditions.map((pc) => {
                    const ispcsafe = (callsafety.get(pc) as {safe: boolean, trgt: boolean}).safe;
                    if(ispcsafe) {
                        return new SMTCallSimple(this.temitter.mangle(pc), callargs); 
                    }
                    else {
                        return new SMTLet(
                            "pcres",
                            new SMTCallGeneral(this.temitter.mangle(pc), callargs),
                            new SMTCallSimple("and", [
                                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres")),
                                this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres"))
                            ])
                        )
                    }
                });
            }

            targeterrorcheck = new SMTCallSimple("=", [new SMTVar("_@smtres@"), this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))]);
            isvaluecheck = this.temitter.generateResultIsSuccessTest(restype, new SMTVar("_@smtres@"));
        }
        
        this.bemitter.requiredUFConsts.forEach((ctype) => {
            const ufcc = new SMTFunctionUninterpreted(`${ctype.name}@uicons_UF`, [], ctype);
            this.assembly.uninterpfunctions.push(ufcc);
        });

        this.assembly.model = new SMTModelState(iargs, rarg, argchk, this.temitter.generateResultType(restype), iexp, targeterrorcheck, isvaluecheck);
        this.assembly.allErrors = this.bemitter.allErrors;
    }

    private generateAPIModule(entrypoint: MIRInvokeDecl, bvwidth: number, constants: object[]): APIModuleInfo {
        const apitype = this.temitter.assembly.typeMap.get("NSCore::APIType") as MIRType;

        const mirapitypes = [...this.temitter.assembly.typeMap].filter((tme) => this.temitter.assembly.subtypeOf(tme[1], apitype) && (tme[1].options.length > 1 || !(tme[1].options[0] instanceof MIRConceptType)))
        const apiout = mirapitypes.map((tme) => this.temitter.getAPITypeFor(tme[1]));

        let argnames: string[] = [];
        let smtargnames: string[] = [];
        let argtypes: string[] = [];
        for(let i = 0; i < entrypoint.params.length; ++i)
        {
            const param = entrypoint.params[i];
            argnames.push(param.name);
            smtargnames.push(this.temitter.mangle(param.name));
            argtypes.push(param.type);
        }

        const signature = {
            name: entrypoint.name,
            restype: entrypoint.resultType,
            argnames: argnames,
            smtargnames: smtargnames,
            argtypes: argtypes
        };

        return {
            apitypes: apiout,
            apisig: signature,
            bvwidth: bvwidth,
            constants: constants
        }
    }

    static generateSMTPayload(assembly: MIRAssembly, mode: "unreachable" | "witness" | "evaluate" | "invert",  timeout: number, runtime: string, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): Payload {
        const cinits = [...assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const callsafety = markSafeCalls([entrypoint, ...cinits], assembly, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts, temitter.mangle(entrypoint));

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety);

        ////////////
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        
        //
        //TODO: compute constants info here...
        //
        const constants: object[] = [];

        const apiinfo = smtemit.generateAPIModule(mirep, vopts.ISize, constants);
        const smtinfo = smtemit.assembly.buildSMT2file(mode, runtime);

        return {smt2decl: smtinfo, timeout: timeout, apimodule: apiinfo};
    }

    static generateSMTAssemblyAllErrors(assembly: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey): { file: string, line: number, pos: number, msg: string }[] {
        const cinits = [...assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const callsafety = markSafeCalls([entrypoint, ...cinits], assembly, {file: "[]", line: -1, pos: -1});

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, {file: "[]", line: -1, pos: -1});
        const smtassembly = new SMTAssembly(vopts, temitter.mangle(entrypoint));

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety);

        return smtemit.assembly.allErrors;
    }
}

export {
    SMTEmitter, APIModuleInfo, Payload
};
