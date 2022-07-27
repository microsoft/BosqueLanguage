//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";
import { BSQRegex } from "../../../ast/bsqregex";

import { MIRAssembly, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREnumEntityTypeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRStringOfInternalEntityTypeDecl, } from "../../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../../compiler/mir_callg";
import { MIRInvokeKey } from "../../../compiler/mir_ops";
import { MorphirBodyEmitter } from "./morphirbody_emitter";
import { MorphirTypeEmitter } from "./morphirtype_emitter";
import { MorphirAssembly } from "./morphir_assembly";

class MorphirEmitter {
    readonly temitter: MorphirTypeEmitter;
    readonly bemitter: MorphirBodyEmitter;
    readonly assembly: MorphirAssembly;
    readonly callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: MorphirTypeEmitter, bemitter: MorphirBodyEmitter, assembly: MorphirAssembly,callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly
        this.callsafety = callsafety;
    }

    private processEntityDecl(edecl: MIRObjectEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: edecl.fields.map((fd) => {
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd), ftype: this.temitter.getMorphirTypeFor(this.temitter.getMIRType(fd.declaredType), true) };
            })
        };

        const smtdecl = new SMTEntityStdDecl(smttype.smttypename, smttype.smttypetag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }
    
    private processStringOfEntityDecl(edecl: MIRStringOfInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataStringEntityDecl(edecl: MIRDataStringInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataBufferEntityDecl(edecl: MIRDataBufferInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(false, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BByteBuffer");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processConstructableEntityDecl(edecl: MIRConstructableEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);
        const oftype = this.temitter.getMorphirTypeFor(this.temitter.getMIRType(edecl.basetype));
        const iskey = this.bemitter.assembly.subtypeOf(this.temitter.getMIRType(edecl.valuetype), this.temitter.getMIRType("KeyType"));

        const smtdecl = new SMTEntityOfTypeDecl(iskey, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, oftype.smttypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEntityInternalOfTypeDecl(edecl: MIRConstructableInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);
        const oftype = this.temitter.getMorphirTypeFor(this.temitter.getMIRType(edecl.fromtype));
        
        const smtdecl = new SMTEntityInternalOfTypeDecl(this.temitter.lookupTypeName(edecl.tkey), smttype.smttypetag, consfuncs.box, consfuncs.bfield, oftype.smttypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEnumEntityDecl(edecl: MIREnumEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new SMTEntityOfTypeDecl(true, smttype.smttypename, smttype.smttypetag, consfuncs.box, consfuncs.bfield, "BNat");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processPrimitiveListEntityDecl(edecl: MIRPrimitiveListEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

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
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

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

    private initializeMorphirAssembly(assembly: MIRAssembly, istestbuild: boolean, entrypoint: MIRInvokeKey) {
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
            const restype = this.temitter.getMorphirTypeFor(tt);
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
            const ttag = this.temitter.getMorphirTypeFor(mirtype).smttypetag;

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
            else if(edcl.attributes.includes("__seqlist_type")) {
                this.processPrimitiveSeqListEntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl);
            }
            else if(edcl.attributes.includes("__seqmap_type")) {
                this.processPrimitiveSeqMapEntityDecl(edcl as MIRPrimitiveInternalEntityTypeDecl);
            }
            else {
                //Don't need to do anything
            }
        });

        this.bemitter.requiredSubtypeTagChecks.forEach((stc) => {
            const occ = stc.oftype.options[0] as MIRConceptType;
            for(let i = 0; i < occ.ckeys.length; ++i) {
                const atname = `AbstractTypeTag_${this.temitter.getMorphirTypeFor(this.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!this.assembly.abstractTypes.includes(atname)) {
                    this.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = this.temitter.getMorphirTypeFor(mtype).smttypetag;

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
                    const ttag = this.temitter.getMorphirTypeFor(mtype).smttypetag;

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
                    const ttag = this.temitter.getMorphirTypeFor(mtype).smttypetag;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.pname === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.typeID);
            const ttag = this.temitter.getMorphirTypeFor(mirtype).smttypetag;

            this.assembly.typeTags.push(ttag);
            ttup.entries.map((entry) => {
                const etype = this.temitter.getMorphirTypeFor(entry);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.smttypename === etype.smttypename) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.typeID, ctype: etype }));
                }
            });
            
            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getMorphirTypeFor(entry, true) };
            });

            this.assembly.tupleDecls.push(new SMTTupleDecl(smttype.smttypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.typeID);
            const ttag = this.temitter.getMorphirTypeFor(mirtype).smttypetag;

            this.assembly.typeTags.push(ttag);
            trec.entries.map((entry) => {
                const etype = this.temitter.getMorphirTypeFor(entry.ptype);
                if (this.assembly.resultTypes.find((rtt) => rtt.ctype.smttypename === etype.smttypename) === undefined) {
                    this.assembly.resultTypes.push(({ hasFlag: true, rtname: entry.ptype.typeID, ctype: etype }));
                }
            });

            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.pname), ftype: this.temitter.getMorphirTypeFor(entry.ptype, true) };
            });

            this.assembly.recordDecls.push(new SMTRecordDecl(smttype.smttypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.typeID);
            
            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getMorphirTypeFor(entry, true) };
            });

            this.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.smttypename, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = this.temitter.lookupGlobalName(cdecl.gkey);
            const consf = this.temitter.lookupFunctionName(cdecl.ivalue);
            const ctype = this.temitter.getMorphirTypeFor(this.temitter.getMIRType(cdecl.declaredType));

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
    }

    static generateMorphirPayload(assembly: MIRAssembly, istestbuild: boolean, runtime: string, entrypoint: MIRInvokeKey): string {
        const callsafety = markSafeCalls([entrypoint], assembly, istestbuild, undefined);

        const temitter = new MorphirTypeEmitter(assembly);
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

        const bemitter = new MorphirBodyEmitter(assembly, temitter, callsafety);
        const smtassembly = new MorphirAssembly(temitter.lookupFunctionName(entrypoint));

        let morphiremit = new MorphirEmitter(temitter, bemitter, smtassembly, callsafety);
        morphiremit.initializeMorphirAssembly(assembly, istestbuild, entrypoint);

        ////////////
        const smtinfo = morphiremit.assembly.buildMorphir2file(runtime);

        return smtinfo;
    }
}

export {
    MorphirEmitter
};
