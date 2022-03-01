//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRConceptType, MIRFieldDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRObjectEntityTypeDecl, MIRPrimitiveInternalEntityTypeDecl } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { ICPPAssembly, ICPPConstDecl, ICPPEntityLayoutInfo, ICPPLayoutCategory, ICPPRecordLayoutInfo, TranspilerOptions } from "./icpp_assembly";
import { ICPPTypeEmitter } from "./icpptype_emitter";
import { ICPPBodyEmitter } from "./iccpbody_emitter";
import { constructCallGraphInfo } from "../../../compiler/mir_callg";
import { SourceInfo } from "../../../ast/parser";

enum ICPPParseTag {
    BuiltinTag = 0x0,
    ValidatorTag,
    BoxedStructTag,
    EnumTag,
    StringOfTag,
    DataStringTag,
    DataBufferTag,
    TupleStructTag,
    TupleRefTag,
    RecordStructTag,
    RecordRefTag,
    EntityObjectStructTag,
    EntityObjectRefTag,
    EntityConstructableStructTag,
    EntityConstructableRefTag,
    EphemeralListTag,
    EntityDeclOfTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    PartialVector4Tag,
    PartialVector8Tag,
    ListTreeTag,
    MapTreeTag,
    RefUnionTag,
    InlineUnionTag,
    UniversalUnionTag
}

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

    private static initializeICPPAssembly(assembly: MIRAssembly, temitter: ICPPTypeEmitter, entrypoints: MIRInvokeKey[]): ICPPAssembly {
        const decltypes = [...assembly.typeMap].filter((v) => !(assembly.entityDecls.get(v[0]) instanceof MIRPrimitiveInternalEntityTypeDecl)).map((v) => temitter.getICPPLayoutInfo(temitter.getMIRType(v[1].typeID)));

        const alltypenames = [...assembly.typeMap].map((tt) => tt[0]);
        const allproperties = new Set<string>(([] as string[]).concat(...decltypes.filter((tt) => tt instanceof ICPPRecordLayoutInfo).map((rt) => (rt as ICPPRecordLayoutInfo).propertynames)));
        const allfields = new Set<MIRFieldKey>(([] as string[]).concat(...decltypes.filter((tt) => tt instanceof ICPPEntityLayoutInfo).map((rt) => (rt as ICPPEntityLayoutInfo).fieldnames)));
        
        const allinvokes = new Set([...assembly.invokeDecls, ...assembly.primitiveInvokeDecls]
            .filter((iiv) => !(iiv[1] instanceof MIRInvokePrimitiveDecl) || (iiv[1] as MIRInvokePrimitiveDecl).implkey !== "default")
            .map((iiv) => iiv[0]));

        const vcallarray = [...assembly.entityDecls].filter((edcl) => edcl[1] instanceof MIRObjectEntityTypeDecl).map((edcl) => [...(edcl[1] as MIRObjectEntityTypeDecl).vcallMap].map((ee) => ee[0]));
        const allvinvokes = new Set<string>((([] as MIRVirtualMethodKey[]).concat(...vcallarray)));

        return new ICPPAssembly(alltypenames, [...allproperties].sort(), [...allfields].sort().map((fkey) => assembly.fieldDecls.get(fkey) as MIRFieldDecl), [...allinvokes].sort(), [...allvinvokes].sort());
    }

    private processVirtualEntityUpdates() {
        //
        //TODO: not implemented yet -- see SMT implementation
        //
    }

    private processAssembly(assembly: MIRAssembly, istestbuild: boolean, entrypoints: MIRInvokeKey[]) {
        const cginfo = constructCallGraphInfo(entrypoints, assembly, istestbuild);
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

            this.icppasm.vinvokenames.add(rvpt.inv);
            opts.forEach((ttup) => {
                const oper = this.bemitter.generateProjectTupleIndexVirtual(rvpt, new SourceInfo(-1, -1, -1 ,-1), ttup);
                this.icppasm.invdecls.push(oper);
                this.icppasm.invokenames.add(oper.ikey);

                let vte = this.icppasm.vtable.find((v) => v.oftype === ttup.typeID);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpt.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: ttup.typeID, vtable: [{vcall: rvpt.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => {
            const vtype = rvpr.argflowtype;
            const opts = [...this.assembly.typeMap].filter((tme) => this.temitter.isUniqueRecordType(tme[1]) && this.assembly.subtypeOf(tme[1], vtype)).map((tme) => tme[1]);

            this.icppasm.vinvokenames.add(rvpr.inv);
            opts.forEach((trec) => {
                const oper = this.bemitter.generateProjectRecordPropertyVirtual(rvpr, new SourceInfo(-1, -1, -1 ,-1), trec);
                this.icppasm.invdecls.push(oper);
                this.icppasm.invokenames.add(oper.ikey);

                let vte = this.icppasm.vtable.find((v) => v.oftype === trec.typeID);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpr.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: trec.typeID, vtable: [{vcall: rvpr.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => {
            const vtype = rvpe.argflowtype;
            const opts = [...this.assembly.typeMap].filter((tme) => this.temitter.isUniqueEntityType(tme[1]) && this.assembly.subtypeOf(tme[1], vtype)).map((tme) => tme[1]);

            this.icppasm.vinvokenames.add(rvpe.inv);
            opts.forEach((tentity) => {
                const oper = this.bemitter.generateProjectEntityFieldVirtual(rvpe, new SourceInfo(-1, -1, -1 ,-1), tentity);
                this.icppasm.invdecls.push(oper);
                this.icppasm.invokenames.add(oper.ikey);

                let vte = this.icppasm.vtable.find((v) => v.oftype === tentity.typeID);
                if(vte !== undefined) {
                    vte.vtable.push({vcall: rvpe.inv, inv: oper.ikey});
                }
                else {
                    vte = { oftype: tentity.typeID, vtable: [{vcall: rvpe.inv, inv: oper.ikey}] };
                    this.icppasm.vtable.push(vte);
                }
            });
        });

        this.bemitter.requiredSingletonConstructorsList.forEach((scl) => {
            this.icppasm.invdecls.push(this.bemitter.generateSingletonConstructorList(scl));
            this.icppasm.invokenames.add(scl.inv);
        });

        this.bemitter.requiredSingletonConstructorsMap.forEach((scm) => {
            this.icppasm.invdecls.push(this.bemitter.generateSingletonConstructorMap(scm));
            this.icppasm.invokenames.add(scm.inv);
        });

        this.icppasm.cbuffsize = this.bemitter.constsize;
        this.icppasm.cmask = "11111";
        for(let i = 1; i < this.bemitter.constlayout.length; ++i) {
            this.icppasm.cmask += this.bemitter.constlayout[i].storage.allocinfo.inlinedmask;
        }

        this.assembly.constantDecls.forEach((cdecl) => {
            const decltype = this.temitter.getICPPLayoutInfo(this.temitter.getMIRType(cdecl.declaredType));
            const offset = this.bemitter.constMap.get(cdecl.gkey) as number;

            let optenumname: [string, string] | undefined = undefined;
            if(cdecl.attributes.includes("enum")) {
                optenumname = [cdecl.enclosingDecl as string, cdecl.shortname];
            }

            const icppdecl = new ICPPConstDecl(cdecl.gkey, optenumname, offset, cdecl.ivalue, decltype.tkey);
            this.icppasm.constdecls.push(icppdecl);

            this.icppasm.cbuffsize += decltype.allocinfo.inlinedatasize;
            this.icppasm.cmask += decltype.allocinfo.inlinedmask;
        });

        this.icppasm.litdecls = this.bemitter.constlayout.slice(1)
            .filter((cle) => cle.isliteral)
            .map((cle) => {
                return { offset: cle.offset, storage: cle.storage.allocinfo, value: cle.value };
            });

        const basetypes = [...this.assembly.typeMap].map((tt) => tt[1]).filter((tt) => tt.options.length === 1 && !(tt.options[0] instanceof MIRConceptType));
        this.icppasm.typenames.forEach((tt) => {
            const mirtype = this.temitter.getMIRType(tt);
            const icpptype = this.temitter.getICPPLayoutInfo(mirtype);

            this.icppasm.typedecls.push(icpptype);

            if (icpptype.layout === ICPPLayoutCategory.UnionRef || icpptype.layout === ICPPLayoutCategory.UnionInline || icpptype.layout === ICPPLayoutCategory.UnionUniversal) {
                const subtypes = basetypes.filter((btype) => this.assembly.subtypeOf(btype, mirtype)).map((tt) => tt.typeID).sort();
                this.icppasm.subtypes.set(mirtype.typeID, new Set<MIRResolvedTypeKey>(subtypes));
            }

            if (this.temitter.isUniqueEntityType(mirtype) && (this.assembly.entityDecls.get(mirtype.typeID) instanceof MIRObjectEntityTypeDecl)) {
                const mdecl = this.assembly.entityDecls.get(mirtype.typeID) as MIRObjectEntityTypeDecl;
                let vte = this.icppasm.vtable.find((v) => v.oftype === mdecl.tkey);
                if (vte === undefined) {
                    vte = { oftype: mdecl.tkey, vtable: [] };
                    this.icppasm.vtable.push(vte);
                }

                mdecl.vcallMap.forEach((tinv, tvcall) => {
                    (vte as { oftype: MIRResolvedTypeKey, vtable: { vcall: MIRVirtualMethodKey, inv: MIRInvokeKey }[] }).vtable.push({ vcall: tvcall, inv: tinv });
                });
            }
        });
    }

    static generateICPPAssembly(assembly: MIRAssembly, istestbuild: boolean, vopts: TranspilerOptions, entrypoints: MIRInvokeKey[]): object {
        const temitter = new ICPPTypeEmitter(assembly, vopts);
        const bemitter = new ICPPBodyEmitter(assembly, temitter, vopts);

        const icppasm = ICPPEmitter.initializeICPPAssembly(assembly, temitter, entrypoints);
        let icppemit = new ICPPEmitter(assembly, temitter, bemitter, icppasm);

        icppemit.processAssembly(assembly, istestbuild, entrypoints);

        return icppemit.icppasm.jsonEmit(assembly, entrypoints);
    }
}

export {
    ICPPParseTag, ICPPEmitter
}