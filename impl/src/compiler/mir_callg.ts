//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Compute the static call graph for an assembly
//

import * as assert from "assert";
import { MIRBasicBlock, MIROpTag, MIRInvokeKey, MIRInvokeFixedFunction, MIRBody, MIRInvokeVirtualOperator, MIRInvokeVirtualFunction, MIREntityUpdate } from "./mir_ops";
import { MIRAssembly, MIRConstantDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRType } from "./mir_assembly";

type CallGNode = {
    invoke: MIRInvokeKey,
    callees: Set<MIRInvokeKey>,
    callers: Set<MIRInvokeKey>
};

type CallGInfo = {
    invokes: Map<MIRInvokeKey, CallGNode>,
    topologicalOrder: CallGNode[],
    roots: CallGNode[],
    recursive: (Set<MIRInvokeKey>)[]
};

function computeCalleesInBlocks(blocks: Map<string, MIRBasicBlock>, invokeNode: CallGNode, assembly: MIRAssembly) {
    blocks.forEach((block) => {
        for (let i = 0; i < block.ops.length; ++i) {
            const op = block.ops[i];
            switch (op.tag) {
                case MIROpTag.MIRInvokeFixedFunction: {
                    invokeNode.callees.add((op as MIRInvokeFixedFunction).mkey);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualFunction: {
                    const vcall = (op as MIRInvokeVirtualFunction).vresolve;
                    const rcvrtype = assembly.typeMap.get((op as MIRInvokeVirtualFunction).rcvrflowtype) as MIRType;
                    const trgts: MIRInvokeKey[] = [];
                    assembly.entityDecls.forEach((edcl) => {
                        if(assembly.subtypeOf(assembly.typeMap.get(edcl.tkey) as MIRType, rcvrtype)) {
                            assert(edcl.vcallMap.has(vcall));
                            trgts.push(edcl.vcallMap.get(vcall) as MIRInvokeKey);
                        }
                    });
                    break;
                }
                case MIROpTag.MIRInvokeVirtualOperator: {
                    const trgts = assembly.virtualOperatorDecls.get((op as MIRInvokeVirtualOperator).vresolve) as MIRInvokeKey[];
                    trgts.forEach((trgt) => invokeNode.callees.add(trgt));
                    break;
                }
                case MIROpTag.MIREntityUpdate: {
                    const rcvrtype = assembly.typeMap.get((op as MIREntityUpdate).argflowtype) as MIRType;
                    const trgts: MIRInvokeKey[] = [];
                    assembly.entityDecls.forEach((edcl) => {
                        if(assembly.subtypeOf(assembly.typeMap.get(edcl.tkey) as MIRType, rcvrtype)) {
                            trgts.push(`${edcl.tkey}@@constructor`);
                        }
                    });
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

function sccVisit(cn: CallGNode, scc: Set<MIRInvokeKey>, marked: Set<MIRInvokeKey>, invokes: Map<MIRInvokeKey, CallGNode>) {
    if (marked.has(cn.invoke)) {
        return;
    }

    scc.add(cn.invoke);
    marked.add(cn.invoke);
    cn.callers.forEach((pred) => sccVisit(invokes.get(pred) as CallGNode, scc, marked, invokes));
}

function topoVisit(cn: CallGNode, pending: CallGNode[], tordered: CallGNode[], invokes: Map<MIRInvokeKey, CallGNode>) {
    if (pending.findIndex((vn) => vn.invoke === cn.invoke) !== -1 || tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
        return;
    }

    pending.push(cn);

    cn.callees.forEach((succ) => (invokes.get(succ) as CallGNode).callers.add(cn.invoke));
    cn.callees.forEach((succ) => topoVisit(invokes.get(succ) as CallGNode, pending, tordered, invokes));

    tordered.push(cn);
}

function processBodyInfo(bkey: MIRInvokeKey, binfo: MIRBody[], assembly: MIRAssembly): CallGNode {
    let cn = { invoke: bkey, callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
    binfo.forEach((b) => {
        computeCalleesInBlocks(b.body, cn, assembly);
    });
    return cn;
}

function constructCallGraphInfo(entryPoints: MIRInvokeKey[], assembly: MIRAssembly): CallGInfo {
    let invokes = new Map<MIRInvokeKey, CallGNode>();

    assembly.invokeDecls.forEach((ivk, ikey) => {
        invokes.set(ikey, processBodyInfo(ikey, [ivk.body], assembly));
    });

    assembly.primitiveInvokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: ikey, callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
        ivk.pcodes.forEach((pc) => cn.callees.add(pc.code));
        invokes.set(cn.invoke, cn);
    });

    let roots: CallGNode[] = [];
    let tordered: CallGNode[] = [];
    entryPoints.forEach((ivk) => {
        roots.push(invokes.get(ivk) as CallGNode);
        topoVisit(invokes.get(ivk) as CallGNode, [], tordered, invokes);
    });

    assembly.constantDecls.forEach((cdecl: MIRConstantDecl) => {
        const civk = assembly.invokeDecls.get(cdecl.value) as MIRInvokeBodyDecl;
        invokes.set(cdecl.value, processBodyInfo(cdecl.value, [civk.body], assembly));
    });

    tordered = tordered.reverse();

    let marked = new Set<MIRInvokeKey>();
    let recursive: (Set<MIRInvokeKey>)[] = [];
    for (let i = 0; i < tordered.length; ++i) {
        let scc = new Set<MIRInvokeKey>();
        sccVisit(tordered[i], scc, marked, invokes);

        if (scc.size > 1 || tordered[i].callees.has(tordered[i].invoke)) {
            recursive.push(scc);
        }
    }

    return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
}

function isSafeInvoke(idecl: MIRInvokeDecl): boolean {
    return idecl.attributes.includes("__safe") || idecl.attributes.includes("__assume_safe");
}

function isBodySafe(ikey: MIRInvokeKey, masm: MIRAssembly, implicitAssumesEnabled: boolean, errorTrgtPos: { file: string, line: number, pos: number }, callg: CallGInfo, safeinfo: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>): { safe: boolean, trgt: boolean } {
    if(masm.primitiveInvokeDecls.has(ikey)) {
        const pinvk = masm.primitiveInvokeDecls.get(ikey) as MIRInvokePrimitiveDecl;
        const cn = callg.invokes.get(ikey) as CallGNode;

        if (isSafeInvoke(pinvk) && [...cn.callees].every((callee) => !safeinfo.has(callee) || isSafeInvoke((masm.primitiveInvokeDecls.get(callee) || masm.invokeDecls.get(callee)) as MIRInvokeDecl))) {
            return { safe: true, trgt: false };
        }
        else {
            const istrgt = [...cn.callees].every((callee) => safeinfo.has(callee) && (safeinfo.get(callee) as { safe: boolean, trgt: boolean }).trgt);
            return { safe: false, trgt: istrgt };
        }
    }
    else {
        const invk = masm.invokeDecls.get(ikey) as MIRInvokeBodyDecl;
        const haserrorop = [...invk.body.body].some((bb) => bb[1].ops.some((op) => {
            return op.canRaise(true);
        }));

        const hastrgt = (invk.srcFile === errorTrgtPos.file) && [...invk.body.body].some((bb) => bb[1].ops.some((op) => {
            return op.canRaise(true) && (op.sinfo.line === errorTrgtPos.line && op.sinfo.pos === errorTrgtPos.pos);
        }));

        if (hastrgt) {
            return { safe: false, trgt: true };
        }
        else {
            const cn = callg.invokes.get(ikey) as CallGNode;
            
            if (!haserrorop && [...cn.callees].every((callee) => !safeinfo.has(callee) || isSafeInvoke((masm.primitiveInvokeDecls.get(callee) || masm.invokeDecls.get(callee)) as MIRInvokeDecl))) {
                return { safe: true, trgt: false };
            }
            else {
                const istrgt = hastrgt || [...cn.callees].every((callee) => safeinfo.has(callee) && (safeinfo.get(callee) as { safe: boolean, trgt: boolean }).trgt);
                return { safe: false, trgt: istrgt };
            }
        }
    }
}

function markSafeCalls(entryPoints: MIRInvokeKey[], masm: MIRAssembly, implicitAssumesEnabled: boolean, errorTrgtPos?: { file: string, line: number, pos: number }): Map<MIRInvokeKey, { safe: boolean, trgt: boolean }> {
    const cginfo = constructCallGraphInfo(entryPoints, masm);
    const rcg = [...cginfo.topologicalOrder].reverse();

    const etrgt = errorTrgtPos || { file: "[IGNORE ERROR TARGETING]", line: -1, pos: -1 };
    let safeinfo = new Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>();

    for (let i = 0; i < rcg.length; ++i) {
        const cn = rcg[i];
        
        const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
        let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

        while (worklist.length !== 0) {
            const ikey = worklist.pop() as string;
            const issafe = isBodySafe(ikey, masm, implicitAssumesEnabled, etrgt, cginfo, safeinfo);

            const osafe = safeinfo.get(ikey);
            if(osafe === undefined || issafe.safe !== osafe.safe || issafe.trgt !== osafe.trgt) {
                safeinfo.set(ikey, issafe);

                if(cscc !== undefined) {
                    const ppn = cginfo.invokes.get(ikey) as CallGNode;
                    ppn.callers.forEach((caller) => {
                        if(!worklist.includes(caller)) {
                            worklist.push(caller);
                        }
                    });
                }
            }
        }
    }

    return safeinfo;
}

export {
    CallGNode,
    CallGInfo,
    constructCallGraphInfo,
    markSafeCalls
};
