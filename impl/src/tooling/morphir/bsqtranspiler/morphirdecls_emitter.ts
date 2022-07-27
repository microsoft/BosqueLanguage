//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert  from "assert";

import { MIRAssembly, MIRConceptType, MIRConstructableEntityTypeDecl, MIRConstructableInternalEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIREnumEntityTypeDecl, MIRInvokeDecl, MIRObjectEntityTypeDecl, MIRPrimitiveListEntityTypeDecl, MIRPrimitiveMapEntityTypeDecl, MIRPrimitiveQueueEntityTypeDecl, MIRPrimitiveSetEntityTypeDecl, MIRPrimitiveStackEntityTypeDecl, MIRRecordType, MIRStringOfInternalEntityTypeDecl, MIRTupleType, } from "../../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../../compiler/mir_callg";
import { MIRInvokeKey } from "../../../compiler/mir_ops";
import { MorphirBodyEmitter } from "./morphirbody_emitter";
import { MorphirTypeEmitter } from "./morphirtype_emitter";
import { MorphirAssembly, MorphirConstantDecl, MorphirEntityCollectionTypeDecl, MorphirEntityInternalOfTypeDecl, MorphirEntityOfTypeDecl, MorphirEntityStdDecl, MorphirEphemeralListDecl, MorphirRecordDecl, MorphirTupleDecl } from "./morphir_assembly";
import { MorphirCallSimple, MorphirConst, MorphirIf, MorphirLet, MorphirVar } from "./morphir_exp";

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
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd), ftype: this.temitter.getMorphirTypeFor(this.temitter.getMIRType(fd.declaredType)) };
            })
        };

        const smtdecl = new MorphirEntityStdDecl(smttype.morphirtypename, smttype.morphirtypetag, consdecl, consfuncs.box, consfuncs.unbox);
        this.assembly.entityDecls.push(smtdecl);
    }
    
    private processStringOfEntityDecl(edecl: MIRStringOfInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new MorphirEntityOfTypeDecl(true, smttype.morphirtypename, smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataStringEntityDecl(edecl: MIRDataStringInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new MorphirEntityOfTypeDecl(true, smttype.morphirtypename, smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, "BString");
        this.assembly.entityDecls.push(smtdecl);
    }
            
    private processDataBufferEntityDecl(edecl: MIRDataBufferInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new MorphirEntityOfTypeDecl(false, smttype.morphirtypename, smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, "BByteBuffer");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processConstructableEntityDecl(edecl: MIRConstructableEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);
        const oftype = this.temitter.getMorphirTypeFor(this.temitter.getMIRType(edecl.basetype));
        const iskey = this.bemitter.assembly.subtypeOf(this.temitter.getMIRType(edecl.valuetype), this.temitter.getMIRType("KeyType"));

        const smtdecl = new MorphirEntityOfTypeDecl(iskey, smttype.morphirtypename, smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, oftype.morphirtypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEntityInternalOfTypeDecl(edecl: MIRConstructableInternalEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);
        const oftype = this.temitter.getMorphirTypeFor(this.temitter.getMIRType(edecl.fromtype));
        
        const smtdecl = new MorphirEntityInternalOfTypeDecl(this.temitter.lookupTypeName(edecl.tkey), smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, oftype.morphirtypename);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processEnumEntityDecl(edecl: MIREnumEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new MorphirEntityOfTypeDecl(true, smttype.morphirtypename, smttype.morphirtypetag, consfuncs.box, consfuncs.unbox, "BNat");
        this.assembly.entityDecls.push(smtdecl);
    }

    private processPrimitiveListEntityDecl(edecl: MIRPrimitiveListEntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getMorphirTypeFor(mirtype);

        const consfuncs = this.temitter.getMorphirConstructorName(mirtype);

        const smtdecl = new MorphirEntityCollectionTypeDecl(smttype.morphirtypename, smttype.morphirtypetag, `List ${this.temitter.getMorphirTypeFor(edecl.getTypeT()).morphirtypename}`, consfuncs.box, consfuncs.unbox);
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

        const smtdecl = new MorphirEntityCollectionTypeDecl(smttype.morphirtypename, smttype.morphirtypetag, `List (MapEntry ${this.temitter.getMorphirTypeFor(edecl.getTypeK()).morphirtypename} ${this.temitter.getMorphirTypeFor(edecl.getTypeV()).morphirtypename})`, consfuncs.box, consfuncs.unbox);
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
                const finfo = this.bemitter.generateMorphirInvoke(idcl);
                this.processVirtualInvokes();
                this.processVirtualEntityUpdates();

                if (finfo !== undefined) {
                    this.assembly.functions.push(finfo);
                }
            }
        }

        this.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => this.assembly.functions.push(this.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        this.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => this.assembly.functions.push(this.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        this.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => this.assembly.functions.push(this.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.assembly.functions.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.assembly.functions.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.assembly.functions.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        this.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => this.assembly.functions.push(this.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        this.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => this.assembly.functions.push(this.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = this.temitter.getMIRType(edcl.tkey);
            const ttag = this.temitter.getMorphirTypeFor(mirtype).morphirtypetag;

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
                const atname = `AbstractTypeTag_${this.temitter.getMorphirTypeFor(this.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!this.assembly.abstractTypes.includes(atname)) {
                    this.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = this.temitter.getMorphirTypeFor(mtype).morphirtypetag;

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
            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, itc.oftype)) {
                    const ttype = mtype.options[0] as MIRTupleType;
                    const ttag = this.temitter.getMorphirTypeFor(mtype).morphirtypetag;

                    if (this.assembly.hasIndexRelation.find((ee) => ee.idxtag === itag && ee.atype === ttag) === undefined) {
                        const hasidx = itc.idx < ttype.entries.length;
                        this.assembly.hasIndexRelation.push({ idxtag: itag, atype: ttag, value: hasidx });
                    }
                }
            });
        });

        this.bemitter.requiredRecordTagChecks.forEach((rtc) => {
            const ptag = `RecordPropertyTag_${rtc.pname}`;
            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, rtc.oftype)) {
                    const ttype = mtype.options[0] as MIRRecordType;
                    const ttag = this.temitter.getMorphirTypeFor(mtype).morphirtypetag;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.pname === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.typeID);
            const ttag = this.temitter.getMorphirTypeFor(mirtype).morphirtypetag;

            this.assembly.typeTags.push(ttag);
            
            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getMorphirTypeFor(entry) };
            });

            this.assembly.tupleDecls.push(new MorphirTupleDecl(smttype.morphirtypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.unbox));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.typeID);
            const ttag = this.temitter.getMorphirTypeFor(mirtype).morphirtypetag;

            this.assembly.typeTags.push(ttag);

            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.pname), ftype: this.temitter.getMorphirTypeFor(entry.ptype) };
            });

            this.assembly.recordDecls.push(new MorphirRecordDecl(smttype.morphirtypename, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.unbox));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.typeID);
            
            const smttype = this.temitter.getMorphirTypeFor(mirtype);
            const ops = this.temitter.getMorphirConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getMorphirTypeFor(entry) };
            });

            this.assembly.ephemeralDecls.push(new MorphirEphemeralListDecl(smttype.morphirtypename, { cname: ops.cons, cargs: consargs }));
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
                this.assembly.constantDecls.push(new MorphirConstantDecl(smtname, optenumname, ctype, consf, new MorphirCallSimple(consf, [])));
            }
            else {
                const rconsf = new MorphirLet("gval", new MorphirCallSimple(consf, []), 
                    new MorphirIf(
                        this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType(cdecl.declaredType), new MorphirVar("gval")),
                        this.temitter.generateResultGetSuccess(this.temitter.getMIRType(cdecl.declaredType), new MorphirVar("gval")),
                        new MorphirConst(`$bsq${ctype.morphirtypename.toLowerCase()}_default`)
                    )
                );

                this.assembly.constantDecls.push(new MorphirConstantDecl(smtname, optenumname, ctype, consf, rconsf));
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
