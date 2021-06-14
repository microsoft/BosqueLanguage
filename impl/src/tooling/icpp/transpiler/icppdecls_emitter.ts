//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRInvokeDecl } from "../../../compiler/mir_assembly";
import { MIRFieldKey, MIRInvokeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { ICPPAssembly, ICPPParseTag, ICPPTypeEntity, ICPPTypeRecord, TranspilerOptions } from "./icpp_assembly";
import { ICPPTypeEmitter } from "./icpptype_emitter";
import { ICPPBodyEmitter } from "./iccpbody_emitter";
import { constructCallGraphInfo } from "../../../compiler/mir_callg";

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
        
        /*
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.icppasm.invdecls.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.icppasm.invdecls.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.icppasm.invdecls.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));


    vtable: {oftype: MIRResolvedTypeKey, vtable: {vcall: MIRVirtualMethodKey, inv: MIRInvokeKey}[]}[] = [];

    typedecls: ICPPType[] = [];
    invdecls: ICPPInvokeDecl[] = [];

    litdecls: { offset: number, storage: ICPPType, value: string }[] = [];
    constdecls: ICPPConstDecl[] = [];

        xxxx;
        */
    }

    static generateSMTAssemblyForValidate(assembly: MIRAssembly, vopts: TranspilerOptions, entrypoint: MIRInvokeKey): ICPPAssembly {
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