//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { ListOpsInfo, SMTConstructorGenCode, SMTDestructorGenCode } from "./smtcollection_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEntityDecl, SMTEphemeralListDecl, SMTFunction, SMTFunctionUninterpreted, SMTListDecl, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

const BuiltinEntityDeclNames = [
    "None",
    "Bool",
    "Int",
    "Nat",
    "BigInt",
    "BigNat",
    "Rational",
    "Float",
    "Decimal",
    "String",
    "Regex",

    "ISequence"
];

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
    }

    private generateAPITypeConstructorFunction_TypedNumber(tt: MIRType, havocfuncs: Set<String>) {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
        const mf = tdecl.fields.find((ff) => ff.fname == "v") as MIRFieldDecl;
        const mftype = this.temitter.getMIRType(mf.declaredType);

        this.walkAndGenerateHavocType(mftype, havocfuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(mftype, new SMTVar("path"), new SMTConst("BNat@zero"));
        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        if (!this.bemitter.isSafeConstructorInvoke(tt)) {
            this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), bcreate));
        }
        else {
            this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), this.temitter.generateResultTypeConstructorSuccess(tt, bcreate)));
        }
    }

    private generateAPITypeConstructorFunction_String(havocfuncs: Set<String>) {
        const bcreate = new SMTCallSimple("BString@UFCons_API", [new SMTVar("path")]);

        let fbody: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.bemitter.vopts.StringOpt === "ASCII") {
            fbody = new SMTLet("str", bcreate,
                new SMTIf(new SMTCallSimple("<", [new SMTCallSimple("str.len", [new SMTVar("str")]), new SMTCallSimple("bv2nat", [new SMTConst("BNat@max")])]),
                    this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::String"))
                )
            );
        }
        else {
            fbody = new SMTLet("str", bcreate,
                new SMTIf(new SMTCallSimple("<", [new SMTCallSimple("seq.len", [new SMTVar("str")]), new SMTCallSimple("bv2nat", [new SMTConst("BNat@max")])]),
                    this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::String"))
                )
            );
        }

        havocfuncs.add(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::String")));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(this.temitter.getMIRType("NSCore::String")), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(this.temitter.getMIRType("NSCore::String")), fbody));
    }

    private generateAPITypeConstructorFunction_ValidatedString(tt: MIRType, havocfuncs: Set<String>) {
        this.walkAndGenerateHavocType(this.temitter.getMIRType("NSCore::String"), havocfuncs);
        const bcreate = this.temitter.generateHavocConstructorCall(this.temitter.getMIRType("NSCore::String"), new SMTVar("path"), new SMTConst("BNat@zero"));

        const vre = this.bemitter.assembly.validatorRegexs.get(tt.trkey) as BSQRegex;
        const lre = vre.compileToSMTValidator(this.bemitter.vopts.StringOpt === "ASCII");

        const accept = new SMTCallSimple("str.in.re", [new SMTConst(lre), this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str"))]);
        const construct = new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, [this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::String"), new SMTVar("str"))]);

        const fbody = new SMTLet("str", bcreate,
            new SMTIf(new SMTCallSimple("and", [this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::String"), new SMTVar("str")), accept]),
                this.temitter.generateResultTypeConstructorSuccess(tt, construct),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Tuple(tt: MIRType, havocfuncs: Set<String>) {
        const ttuple = tt.options[0] as MIRTupleType;

        const ctors = ttuple.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee.type, havocfuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee.type, new SMTVar("path"), new SMTConst(`(_ bv${i} ${this.bemitter.vopts.ISize})`));
            const ccvar = this.bemitter.generateTempName();
            const chkfun = this.temitter.generateResultIsSuccessTest(tt, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee.type, new SMTVar(ccvar));

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                new SMTCallSimple("and", ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)),
                new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Record(tt: MIRType, havocfuncs: Set<String>) {
        const trecord = tt.options[0] as MIRRecordType;

        const ctors = trecord.entries.map((ee, i) => {
            this.walkAndGenerateHavocType(ee.type, havocfuncs);
            const cc = this.temitter.generateHavocConstructorCall(ee.type, new SMTVar("path"), new SMTConst(`(_ bv${i} ${this.bemitter.vopts.ISize})`));
            const ccvar = this.bemitter.generateTempName();
            const chkfun = this.temitter.generateResultIsSuccessTest(tt, new SMTVar(ccvar));
            const access = this.temitter.generateResultGetSuccess(ee.type, new SMTVar(ccvar));

            return { pname: ee.name, ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const fbody = new SMTLetMulti(
            ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc }; }),
            new SMTIf(
                new SMTCallSimple("and", ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)),
                new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)),
                this.temitter.generateErrorResultAssert(tt)
            )
        );

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_List(tt: MIRType, havocfuncs: Set<String>) {
        const ldecl = this.temitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
        const ctype = this.temitter.getMIRType(((ldecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);
        
        this.walkAndGenerateHavocType(ctype, havocfuncs);

        const invop = this.bemitter.lopsManager.registerHavoc(tt);
        const fbody = new SMTCallGeneral(invop, [new SMTVar("path")]);

        havocfuncs.add(this.temitter.generateHavocConstructorName(tt));
        this.assembly.functions.push(SMTFunction.create(this.temitter.generateHavocConstructorName(tt), [{ vname: "path", vtype: new SMTType("(Seq BNat)") }], this.temitter.generateResultType(tt), fbody));
    }

    private generateAPITypeConstructorFunction_Set(tt: MIRType, havocfuncs: Set<String>) {
        //
        //TODO: not implemented yet
        //
        assert(false);
    }

    private generateAPITypeConstructorFunction_Map(tt: MIRType, havocfuncs: Set<String>) {
        //
        //TODO: not implemented yet
        //
        assert(false);
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
        
    private processVectorTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processListTypeDecl(ldecl: MIREntityTypeDecl) {
        const mtype = this.temitter.getMIRType(ldecl.tkey);
        const ltype = this.temitter.getSMTTypeFor(mtype);
        const ctype = this.temitter.getMIRType(((ldecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);
        const nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));
        
        const linfo = this.bemitter.lopsManager.ops.get(ldecl.tkey) as ListOpsInfo;
        const constructors: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[] = [];

        ////
        //cons ops

        if(this.bemitter.lopsManager.rangenat && ctype.trkey == this.temitter.getMIRType("NSCore::Nat").trkey) {
            const crange = this.bemitter.lopsManager.emitConstructorRange(mtype, ltype, ctype);
            this.processConstructorGenInfo(crange, constructors);
        }

        if(this.bemitter.lopsManager.rangeint && ctype.trkey == this.temitter.getMIRType("NSCore::Int").trkey) {
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
            
        linfo.consops.literalk.forEach((k) => {
            const ck = this.bemitter.lopsManager.emitConstructorLiteralK(mtype, ltype, ctype, k);
            this.processConstructorGenInfo(ck, constructors);
        });

        linfo.consops.filter.forEach((pcode, code) => {
            const cfilter = this.bemitter.lopsManager.emitConstructorFilter(ltype, mtype, ctype, code, pcode);
            this.processConstructorGenInfo(cfilter, constructors);
        });

        linfo.consops.map.forEach((minfo, code) => {
            const cmap = this.bemitter.lopsManager.emitConstructorMap(ltype, mtype, code, minfo[0]);
            this.processConstructorGenInfo(cmap, constructors);
        });
            
        ////
        //des ops

        const dget = this.bemitter.lopsManager.emitDestructorGet(ltype, ctype, linfo.consops);
        this.processDestructorGenInfo(dget);

        linfo.dops.safecheckpred.forEach((pcode, code) => {
            const dsafe = this.bemitter.lopsManager.emitSafeCheckPred(ltype, mtype, code, pcode);
            this.processDestructorGenInfo(dsafe);
        });

        linfo.dops.safecheckfn.forEach((cinfo, code) => {
            const dsafe = this.bemitter.lopsManager.emitSafeCheckFn(ltype, mtype, cinfo[1], code, cinfo[0]);
            this.processDestructorGenInfo(dsafe);
        });

        linfo.dops.isequence.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorISequence(ltype, code, pcode);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.haspredcheck.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorHasPredCheck(ltype, code, pcode);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.findIndexOf.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorFindIndexOf(ltype, code, pcode);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.findLastIndexOf.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorFindIndexOfLast(ltype, code, pcode);
            this.processDestructorGenInfo(disq);
        });

        linfo.dops.countIf.forEach((pcode, code) => {
            const disq = this.bemitter.lopsManager.emitDestructorCountIf(ltype, code, pcode);
            this.processDestructorGenInfo(disq);
        });

        const ttag = `TypeTag_${ltype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mtype, this.temitter.getMIRType("NSCore::KeyType"));
        const isapi = this.temitter.assembly.subtypeOf(mtype, this.temitter.getMIRType("NSCore::APIType"));

        const consfuncs = this.temitter.getSMTConstructorName(mtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: [
                { fname: `${ltype.name}@size`, ftype: nattype },
                { fname: `${ltype.name}@uli`, ftype: this.bemitter.lopsManager.generateULITypeFor(ltype) }
            ]
        };

        const smtdecl = new SMTListDecl(iskey, isapi, this.bemitter.lopsManager.generateULITypeFor(ltype).name, constructors, ltype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.listDecls.push(smtdecl);
    }
        
    private processStackTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processQueueTypeDecl(qdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
       
    private processSetTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processDynamicSetTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processMapTypeDecl(mdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processDynamicMapTypeDecl(mdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processEntityDecl(edecl: MIREntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const ttag = `TypeTag_${smttype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
        const isapi = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: edecl.fields.map((fd) => {
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd.fkey), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(fd.declaredType)) };
            })
        };

        const smtdecl = new SMTEntityDecl(iskey, isapi, smttype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield);
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

    private walkAndGenerateHavocType(tt: MIRType, havocfuncs: Set<String>) {
        assert(tt.options.length === 1)

        if (this.temitter.isKnownSafeHavocConstructorType(tt)) {
            //Don't need to do anything
        }
        else if (this.temitter.isUniqueTupleType(tt)) {
            this.generateAPITypeConstructorFunction_Tuple(tt, havocfuncs);
        }
        else if (this.temitter.isUniqueRecordType(tt)) {
            this.generateAPITypeConstructorFunction_Record(tt, havocfuncs);
        }
        else if (this.temitter.isUniqueEntityType(tt)) {
            const etype = tt.options[0] as MIREntityType;
            const edecl = this.temitter.assembly.entityDecls.get(etype.trkey) as MIREntityTypeDecl;

            if (edecl.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
                this.generateAPITypeConstructorFunction_TypedNumber(tt, havocfuncs);
            }
            else if (this.temitter.isType(tt, "NSCore::String")) {
                this.generateAPITypeConstructorFunction_String(havocfuncs);
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
            else {
                //Don't need to do anything
            }
        }
        else {
            //Don't need to do anything
        }
    }

    private initializeSMTAssembly(assembly: MIRAssembly, entrypoint: MIRInvokeKey, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>, maxgas: number) {
        let doneset = new Set<MIRInvokeKey>();

        const cinits = [...assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const cginfo = constructCallGraphInfo([entrypoint, ...cinits], assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? maxgas : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = this.bemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);
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

                    const rtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(idcl.resultType));
                    if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
                        this.assembly.resultTypes.push(({hasFlag: false, rtname: idcl.resultType, ctype: rtype}));
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }

        ["NSCore::None", "NSCore::Bool", "NSCore::Int", "NSCore::Nat", "NSCore::BigInt", "NSCore::BigNat", "NSCore::Float", "NSCore::Decimal", "NSCore::Rational", "NSCore::String", "NSCore::Regex"]
            .forEach((ptype) => {
                const rtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(ptype));
                if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
                    this.assembly.resultTypes.push(({hasFlag: false, rtname: ptype, ctype: rtype}));
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
            const vexp = this.temitter.generateHavocConstructorCall(mirptype, new SMTCallSimple("seq.unit", [new SMTConst("BNat@zero")]), new SMTConst(`(_ bv${i} ${this.assembly.vopts.ISize})`));
            
            
            return { vname: vname, vtype: this.temitter.generateResultType(mirptype), vinit: vexp, vchk: this.temitter.generateResultIsSuccessTest(mirptype, new SMTVar(vname)), callexp: this.temitter.generateResultGetSuccess(mirptype, new SMTVar(vname)) };
        });

        const restype = this.temitter.getMIRType(mirep.resultType);
        const rtype = this.temitter.getSMTTypeFor(restype);
        if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
            this.assembly.resultTypes.push(({ hasFlag: false, rtname: mirep.resultType, ctype: rtype }));
        }

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

            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(edcl.tkey));
            if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({ hasFlag: false, rtname: edcl.tkey, ctype: restype }));
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
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicSetTypeDecl)) {
                this.processDynamicSetTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                this.processMapTypeDecl(edcl);
            }
            else if (edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicMapTypeDecl)) {
                this.processDynamicMapTypeDecl(edcl);
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

            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(ttup.trkey));
            if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({hasFlag: false, rtname: ttup.trkey, ctype: restype}));
            }
            
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
            
            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(trec.trkey));
            if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({hasFlag: false, rtname: trec.trkey, ctype: restype}));
            }

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
            const smtname = this.temitter.mangle(cdecl.gkey);
            const consf = this.temitter.mangle(cdecl.value);
            const ctype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(cdecl.declaredType));
            this.assembly.constantDecls.push(new SMTConstantDecl(smtname, ctype, consf));
        });

        this.assembly.maskSizes = this.bemitter.maskSizes;

        const smtcall = this.temitter.mangle(mirep.key);
        const callargs = iargs.map((arg) => arg.callexp);
        const issafe = (callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

        let iexp: SMTExp | undefined = undefined;
        let argchk: SMTExp[] | undefined = undefined;
        if(issafe) {
            iexp = this.temitter.generateResultTypeConstructorSuccess(restype, new SMTCallSimple(smtcall, callargs));
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
        }
        
        this.bemitter.requiredUFConsts.forEach((ctype) => {
            const ufcc = new SMTFunctionUninterpreted(`${ctype.name}@uicons_UF`, [], ctype);
            this.assembly.uninterpfunctions.push(ufcc);
        });

        this.assembly.model = new SMTModelState(iargs, argchk, this.temitter.generateResultType(restype), iexp);
        this.assembly.allErrors = this.bemitter.allErrors;
    }

    static generateSMTAssemblyForValidate(assembly: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, maxgas: number): SMTAssembly {
        const cinits = [...assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const callsafety = markSafeCalls([entrypoint, ...cinits], assembly, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts, temitter.mangle(entrypoint));

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety, maxgas);

        ////////////
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        const restype = temitter.getMIRType(mirep.resultType);

        const eqerrexp = new SMTCallSimple("=", [new SMTVar("@smtres@"), smtemit.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))]);
        smtemit.assembly.modes = {
            refute: eqerrexp,
            generate: eqerrexp
        };

        return smtemit.assembly;
    }
}

export {
    SMTEmitter
};
