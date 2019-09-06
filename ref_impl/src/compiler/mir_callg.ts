//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Compute the static call graph for an assembly
//

import * as assert from "assert";
import { MIRBasicBlock, MIROpTag, MIRInvokeKey, MIRInvokeFixedFunction, MIRBodyKey, MIRLoadConstTypedString, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRConstructorPrimary, MIRBody, MIRNominalTypeKey, MIRFieldKey } from "./mir_ops";
import { MIRAssembly, MIREntityTypeDecl, MIRConstantDecl, MIRFieldDecl } from "./mir_assembly";
import { MIRKeyGenerator } from "./mir_emitter";

type CallGNode = {
    invoke: MIRBodyKey,
    callees: Set<MIRBodyKey>,
    callers: Set<MIRBodyKey>
};

function computeCalleesInBlocks(blocks: Map<string, MIRBasicBlock>, invokeNode: CallGNode, assembly: MIRAssembly) {
    blocks.forEach((block) => {
        for (let i = 0; i < block.ops.length; ++i) {
            const op = block.ops[i];
            switch (op.tag) {
                case MIROpTag.MIRLoadConstTypedString: {
                    const pkey = MIRKeyGenerator.generateBodyKey("invoke", (op as MIRLoadConstTypedString).pfunckey);
                    invokeNode.callees.add(pkey);
                    break;
                }
                case MIROpTag.MIRAccessConstantValue: {
                    const constkey = MIRKeyGenerator.generateBodyKey("const", (op as MIRAccessConstantValue).ckey);
                    invokeNode.callees.add(constkey);
                    break;
                }
                case MIROpTag.MIRLoadFieldDefaultValue: {
                    const fdefaultkey = MIRKeyGenerator.generateBodyKey("fdefault", (op as MIRLoadFieldDefaultValue).fkey);
                    invokeNode.callees.add(fdefaultkey);
                    break;
                }
                case MIROpTag.MIRConstructorPrimary: {
                    const cop = op as MIRConstructorPrimary;
                    const edecl = assembly.entityDecls.get(cop.tkey) as MIREntityTypeDecl;
                    if (edecl.invariants.length !== 0) {
                        const invkey = MIRKeyGenerator.generateBodyKey("invariant", cop.tkey);
                        invokeNode.callees.add(invkey);
                    }
                    break;
                }
                case MIROpTag.MIRInvokeFixedFunction: {
                    const iop = op as MIRInvokeFixedFunction;
                    const ikey = MIRKeyGenerator.generateBodyKey("invoke", iop.mkey);
                    invokeNode.callees.add(ikey);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualTarget: {
                    //TODO lookup all possible vtargets and add them
                    assert(false);
                    break;
                }
                default: {
                    //ignore all other ops
                    break;
                }
            }
        }
    });
}

function sccVisit(cn: CallGNode, scc: Set<CallGNode>, marked: Set<MIRInvokeKey>, invokes: Map<MIRInvokeKey, CallGNode>) {
    if (marked.has(cn.invoke)) {
        return;
    }

    scc.add(cn);
    marked.add(cn.invoke);
    cn.callers.forEach((pred) => sccVisit(invokes.get(pred) as CallGNode, scc, marked, invokes));
}

function topoVisit(cn: CallGNode, tordered: CallGNode[], invokes: Map<MIRInvokeKey, CallGNode>) {
    if (tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
        return;
    }

    cn.callees.forEach((succ) => (invokes.get(succ) as CallGNode).callers.add(cn.invoke));
    cn.callees.forEach((succ) => topoVisit(invokes.get(succ) as CallGNode, tordered, invokes));

    tordered.push(cn);
}

function processBodyInfo(bkey: MIRBodyKey, binfo: MIRBody[], assembly: MIRAssembly): CallGNode {
    let cn = { invoke: bkey, callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
    binfo.forEach((b) => {
        computeCalleesInBlocks(b.body, cn, assembly);
    });
    return cn;
}

function constructCallGraphInfo(entryPoints: MIRInvokeKey[], assembly: MIRAssembly): { invokes: Map<MIRBodyKey, CallGNode>, topologicalOrder: CallGNode[], roots: CallGNode[], recursive: (Set<CallGNode>)[] } {
    let invokes = new Map<MIRBodyKey, CallGNode>();

    assembly.constantDecls.forEach((cdecl: MIRConstantDecl) => {
        invokes.set(cdecl.value.bkey, processBodyInfo(cdecl.value.bkey, [cdecl.value], assembly));
    });

    assembly.entityDecls.forEach((edecl: MIREntityTypeDecl, ekey: MIRNominalTypeKey) => {
        if (edecl.invariants.length !== 0) {
            const invkey = MIRKeyGenerator.generateBodyKey("invariant", ekey);
            invokes.set(invkey, processBodyInfo(invkey, edecl.invariants, assembly));
        }
    });

    assembly.fieldDecls.forEach((fdecl: MIRFieldDecl, fkey: MIRFieldKey) => {
        if (fdecl.value !== undefined) {
            const fdkey = MIRKeyGenerator.generateBodyKey("fdefault", fkey);
            invokes.set(fdkey, processBodyInfo(fdkey, [fdecl.value], assembly));
        }
    });

    assembly.invokeDecls.forEach((ivk, ikey) => {
        invokes.set(ivk.body.bkey, processBodyInfo(ivk.body.bkey, [ivk.body], assembly));

        if (ivk.preconditions.length !== 0) {
            const prekey = MIRKeyGenerator.generateBodyKey("pre", ikey);
            invokes.set(prekey, processBodyInfo(prekey, ivk.preconditions.map((pre) => pre[0]), assembly));
            (invokes.get(ivk.body.bkey) as CallGNode).callees.add(prekey);
        }
        if (ivk.postconditions.length !== 0) {
            const postkey = MIRKeyGenerator.generateBodyKey("post", ikey);
            invokes.set(postkey, processBodyInfo(postkey, ivk.postconditions, assembly));
            (invokes.get(ivk.body.bkey) as CallGNode).callees.add(postkey);
        }
    });

    assembly.primitiveInvokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: MIRKeyGenerator.generateBodyKey("invoke", ikey), callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
        ivk.pcodes.forEach((pc) => cn.callees.add(MIRKeyGenerator.generateBodyKey("invoke", pc.code)));
        invokes.set(cn.invoke, cn);

        if (ivk.preconditions.length !== 0) {
            const prekey = MIRKeyGenerator.generateBodyKey("pre", ikey);
            invokes.set(prekey, processBodyInfo(prekey, ivk.preconditions.map((pre) => pre[0]), assembly));
            cn.callees.add(prekey);
        }
        if (ivk.postconditions.length !== 0) {
            const postkey = MIRKeyGenerator.generateBodyKey("post", ikey);
            invokes.set(postkey, processBodyInfo(postkey, ivk.postconditions, assembly));
            cn.callees.add(postkey);
        }
    });

    let roots: CallGNode[] = [];
    let tordered: CallGNode[] = [];
    entryPoints.forEach((ivk) => {
        const ikey = MIRKeyGenerator.generateBodyKey("invoke", ivk);

        roots.push(invokes.get(ikey) as CallGNode);
        topoVisit(invokes.get(ikey) as CallGNode, tordered, invokes);
    });
    tordered = tordered.reverse();

    let marked = new Set<MIRInvokeKey>();
    let recursive: (Set<CallGNode>)[] = [];
    for (let i = 0; i < tordered.length; ++i) {
        let scc = new Set<CallGNode>();
        sccVisit(tordered[i], scc, marked, invokes);

        if (scc.size > 1) {
            recursive.push(scc);
        }
    }

    return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
}

export { constructCallGraphInfo };
