//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIREntityTypeDecl, MIRInvokeDecl } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { ICPPAssembly, ICPPConstDecl, ICPPParseTag, ICPPTypeEntity, ICPPTypeInlineUnion, ICPPTypeRecord, ICPPTypeRefUnion, TranspilerOptions } from "./icpp_assembly";
import { ICPPTypeEmitter } from "./icpptype_emitter";
import { ICPPBodyEmitter } from "./iccpbody_emitter";
import { constructCallGraphInfo } from "../../../compiler/mir_callg";
import { SourceInfo } from "../../../ast/parser";

class ICPPEmitter {
    readonly assembly: MIRAssembly;
    readonly temitter: ICPPTypeEmitter;
    readonly bemitter: ICPPBodyEmitter;
    readonly icppasm: ICPPAssembly;

    constructor(assembly: MIRAssembly, temitter: ICPPTypeEmitter, bemitter: ICPPBodyEmitter, icppasm: ICPPAssembly) {
        this.assembly = assembly;
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.icppasm = icppasm;
    }

    private static initializeICPPAssembly(assembly: MIRAssembly, temitter: ICPPTypeEmitter, entrypoint: MIRInvokeKey): ICPPAssembly {
        const alltypes = [...assembly.typeMap].map((v) => temitter.getICPPTypeData(temitter.getMIRType(v[1].trkey)));
        const decltypes = alltypes.filter((tt) => tt.ptag !== ICPPParseTag.BuiltinTag);

        const alltypenames = alltypes.map((tt) =>tt.tkey);
        const allproperties = new Set<string>(([] as string[]).concat(...decltypes.filter((tt) => tt instanceof ICPPTypeRecord).map((rt) => (rt as ICPPTypeRecord).propertynames)));
        const allfields = new Set<MIRFieldKey>(([] as string[]).concat(...decltypes.filter((tt) => tt instanceof ICPPTypeEntity).map((rt) => (rt as ICPPTypeEntity).fieldnames)));
        
        const allinvokes = new Set([...assembly.invokeDecls, ...assembly.primitiveInvokeDecls].map((v) => v[0]));
        const allvinvokes = new Set(...(([] as MIRVirtualMethodKey[]).concat(...[...assembly.entityDecls].map((edcl) => [...edcl[1].vcallMap].map((ee) => ee[0])))));

        return new ICPPAssembly(decltypes.length, alltypenames, [...allproperties].sort(), [...allfields].sort(), [...allinvokes].sort(), [...allvinvokes].sort(), entrypoint);
    }

    private processVirtualEntityUpdates() {
        //
        //TODO: not implemented yet -- see SMT implementation
        //
    }

    private processAssembly(entrypoint: MIRInvokeKey) {
        const cinits = [...this.assembly.constantDecls].map((cdecl) => cdecl[1].value);
        const cginfo = constructCallGraphInfo([entrypoint, ...cinits], this.assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            
            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            for (let mi = 0; mi < worklist.length; ++mi) {
                const ikey = worklist[mi];

                const idcl = (this.assembly.invokeDecls.get(ikey) || this.assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                const finfo = this.bemitter.generateICPPInvoke(idcl);

                this.processVirtualEntityUpdates();

                if (finfo !== undefined) {
                    this.icppasm.invdecls.push(finfo);
                }
            }
        }
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => {
            const vtype = rvpt.argflowtype;
            const opts = [...this.assembly.typeMap].filter((tme) => this.temitter.isUniqueTupleType(tme[1]) && this.assembly.subtypeOf(tme[1], vtype)).map((tme) => tme[1]);

            opts.forEach((ttup) => {
                const oper = this.bemitter.generateProjectTupleIndexVirtual(rvpt, new SourceInfo(-1, -1, -1 ,-1), ttup);
                this.icppasm.invdecls.push(oper);

                let vte = this.icppasm.vtable.find((v) => v.oftype === ttup.trkey);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpt.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: ttup.trkey, vtable: [{vcall: rvpt.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => {
            const vtype = rvpr.argflowtype;
            const opts = [...this.assembly.typeMap].filter((tme) => this.temitter.isUniqueRecordType(tme[1]) && this.assembly.subtypeOf(tme[1], vtype)).map((tme) => tme[1]);

            opts.forEach((trec) => {
                const oper = this.bemitter.generateProjectRecordPropertyVirtual(rvpr, new SourceInfo(-1, -1, -1 ,-1), trec);
                this.icppasm.invdecls.push(oper);

                let vte = this.icppasm.vtable.find((v) => v.oftype === trec.trkey);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpr.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: trec.trkey, vtable: [{vcall: rvpr.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => {
            const vtype = rvpe.argflowtype;
            const opts = [...this.assembly.typeMap].filter((tme) => this.temitter.isUniqueEntityType(tme[1]) && this.assembly.subtypeOf(tme[1], vtype)).map((tme) => tme[1]);

            opts.forEach((tentity) => {
                const oper = this.bemitter.generateProjectEntityFieldVirtual(rvpe, new SourceInfo(-1, -1, -1 ,-1), tentity);
                this.icppasm.invdecls.push(oper);

                let vte = this.icppasm.vtable.find((v) => v.oftype === tentity.trkey);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpe.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: tentity.trkey, vtable: [{vcall: rvpe.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.icppasm.cbuffsize = this.bemitter.constsize;
        this.icppasm.cmask = "11111";
        for(let i = 1; i < this.bemitter.constlayout.length; ++i) {
            this.icppasm.cmask += this.bemitter.constlayout[i].storage.allocinfo.inlinedmask;
        }

        this.assembly.constantDecls.forEach((cdecl) => {
            const decltype = this.temitter.getICPPTypeData(this.temitter.getMIRType(cdecl.declaredType));
            const offset = this.bemitter.constMap.get(cdecl.gkey) as number;
            new ICPPConstDecl(cdecl.gkey, offset, cdecl.value, decltype);

            this.icppasm.cbuffsize += decltype.allocinfo.inlinedatasize;
            this.icppasm.cmask += decltype.allocinfo.inlinedmask;
        });

        this.icppasm.litdecls = this.bemitter.constlayout.slice(1)
            .filter((cle) => cle.isliteral)
            .map((cle) => {
                return { offset: cle.offset, storage: cle.storage, value: cle.value };
            });


        const basetypes = [...this.assembly.typeMap].map((tt) => tt[1]).filter((tt) => tt.options.length === 1 && !(tt.options[0] instanceof MIRConceptType));
        this.icppasm.typenames.forEach((tt) => {
            const mirtype = this.temitter.getMIRType(tt);
            const icpptype = this.temitter.getICPPTypeData(mirtype);
            this.icppasm.typedecls.push(icpptype);

            if(icpptype instanceof ICPPTypeInlineUnion || icpptype instanceof ICPPTypeRefUnion) {
                const subtypes = basetypes.filter((btype) => this.assembly.subtypeOf(btype, mirtype)).map((tt) => tt.trkey).sort();
                this.icppasm.subtypes.set(mirtype.trkey, new Set<MIRResolvedTypeKey>(subtypes));
            }

            if(this.temitter.isUniqueEntityType(mirtype)) {
                const mdecl = this.assembly.entityDecls.get(mirtype.trkey) as MIREntityTypeDecl;
                let vte = this.icppasm.vtable.find((v) => v.oftype === mdecl.tkey);
                if(vte === undefined) {
                    vte = { oftype: mdecl.tkey, vtable: [] };
                    this.icppasm.vtable.push(vte);
                }

                mdecl.vcallMap.forEach((vc) => {
                    (vte as {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]}).vtable.push({vcall: vc[0], inv: vc[1]});
                });
            }
        });
    }

    static generateICPPAssembly(assembly: MIRAssembly, vopts: TranspilerOptions, entrypoint: MIRInvokeKey): ICPPAssembly {
        const temitter = new ICPPTypeEmitter(assembly, vopts);
        const bemitter = new ICPPBodyEmitter(assembly, temitter, vopts);

        const icppasm = ICPPEmitter.initializeICPPAssembly(assembly, temitter, entrypoint);
        let icppemit = new ICPPEmitter(assembly, temitter, bemitter, icppasm);

        icppemit.processAssembly(entrypoint);

        return icppemit.icppasm;
    }
}

export {
    ICPPEmitter
}