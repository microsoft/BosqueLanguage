//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Compute the static call graph for an assembly
//

import * as assert from "assert";
import { MIRBasicBlock, MIROpTag, MIRInvokeKey, MIRInvokeFixedFunction, MIRBody, MIRInvokeVirtualOperator, MIRInvokeVirtualFunction, MIREntityUpdate } from "./mir_ops";
import { MIRAssembly, MIRConstantDecl, MIRConstructableEntityTypeDecl, MIRDataBufferInternalEntityTypeDecl, MIRDataStringInternalEntityTypeDecl, MIRInvokeBodyDecl, MIRInvokeDecl, MIRInvokePrimitiveDecl, MIRObjectEntityTypeDecl, MIRType } from "./mir_assembly";

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
                        if (edcl instanceof MIRObjectEntityTypeDecl) {
                            if (assembly.subtypeOf(assembly.typeMap.get(edcl.tkey) as MIRType, rcvrtype)) {
                                assert(edcl.vcallMap.has(vcall));
                                trgts.push(edcl.vcallMap.get(vcall) as MIRInvokeKey);
                            }
                        }
                    });
                    trgts.forEach((trgt) => invokeNode.callees.add(trgt));
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
                            trgts.push(`__i__${edcl.tkey}::@@constructor`);
                        }
                    });
                    trgts.forEach((trgt) => invokeNode.callees.add(trgt));
                    break;
                }
                default: {
                    //ignore all other ops
                    break;
                }
            }

            op.getUsedGlobals().forEach((gg) => {
                const constv = assembly.constantDecls.get(gg.gkey) as MIRConstantDecl;
                invokeNode.callees.add(constv.ivalue)
            });
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

function constructCallGraphInfo(entryPoints: MIRInvokeKey[], assembly: MIRAssembly, istestbuild: boolean): CallGInfo {
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

    assembly.constantDecls.forEach((cdecl: MIRConstantDecl) => {
        roots.push(invokes.get(cdecl.ivalue) as CallGNode);
        topoVisit(invokes.get(cdecl.ivalue) as CallGNode, [], tordered, invokes);
    });

    entryPoints.forEach((ivk) => {
        roots.push(invokes.get(ivk) as CallGNode);
        topoVisit(invokes.get(ivk) as CallGNode, [], tordered, invokes);
    });

    const apitype = assembly.typeMap.get("APIType") as MIRType;
    const testtype = assembly.typeMap.get("TestableType") as MIRType;
    assembly.entityDecls.forEach((ee) => {
        if(assembly.subtypeOf(assembly.typeMap.get(ee.tkey) as MIRType, apitype) || (istestbuild && assembly.subtypeOf(assembly.typeMap.get(ee.tkey) as MIRType, testtype))) {
            if (ee instanceof MIRObjectEntityTypeDecl) {
                if(ee.validatefunc !== undefined) {
                    roots.push(invokes.get(ee.validatefunc) as CallGNode);
                    topoVisit(invokes.get(ee.validatefunc) as CallGNode, [], tordered, invokes);
                }

                roots.push(invokes.get(ee.consfunc as MIRInvokeKey) as CallGNode);
                topoVisit(invokes.get(ee.consfunc as MIRInvokeKey) as CallGNode, [], tordered, invokes);
            }
            else if (ee instanceof MIRConstructableEntityTypeDecl) {
                if(ee.validatefunc !== undefined) {
                    roots.push(invokes.get(ee.validatefunc) as CallGNode);
                    topoVisit(invokes.get(ee.validatefunc) as CallGNode, [], tordered, invokes);
                }

                if(ee.usingcons !== undefined) {
                    roots.push(invokes.get(ee.usingcons) as CallGNode);
                    topoVisit(invokes.get(ee.usingcons) as CallGNode, [], tordered, invokes);
                }
            }
            else if (ee instanceof MIRDataStringInternalEntityTypeDecl) {
                roots.push(invokes.get(ee.accepts) as CallGNode);
                topoVisit(invokes.get(ee.accepts) as CallGNode, [], tordered, invokes);
            }
            else if (ee instanceof MIRDataBufferInternalEntityTypeDecl) {
                roots.push(invokes.get(ee.accepts) as CallGNode);
                topoVisit(invokes.get(ee.accepts) as CallGNode, [], tordered, invokes);
            }
            else {
                ;
            }
        }
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

function isBodySafe(ikey: MIRInvokeKey, masm: MIRAssembly, errorTrgtPos: { file: string, line: number, pos: number }, callg: CallGInfo, inscc: boolean, safeinfo: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>): { safe: boolean, trgt: boolean } {
    if(masm.primitiveInvokeDecls.has(ikey)) {
        const pinvk = masm.primitiveInvokeDecls.get(ikey) as MIRInvokePrimitiveDecl;
        const cn = callg.invokes.get(ikey) as CallGNode;

        if (isSafeInvoke(pinvk)) {
            return { safe: true, trgt: false };
        }
        else {
            const istrgt = [...cn.callees].every((callee) => safeinfo.has(callee) && (safeinfo.get(callee) as { safe: boolean, trgt: boolean }).trgt);
            if(!pinvk.attributes.includes("__conditional_safe")) {
                return { safe: false, trgt: istrgt };
            }
            else {
                const issafe = !inscc && [...cn.callees].every((callee) => safeinfo.has(callee) && (safeinfo.get(callee) as { safe: boolean, trgt: boolean }).safe);
                return { safe: issafe, trgt: istrgt };
            }
        }
    }
    else {
        const invk = masm.invokeDecls.get(ikey) as MIRInvokeBodyDecl;
        const haserrorop = [...invk.body.body].some((bb) => bb[1].ops.some((op) => {
            return op.canRaise();
        }));

        const hastrgt = (invk.srcFile === errorTrgtPos.file) && [...invk.body.body].some((bb) => bb[1].ops.some((op) => {
            return op.canRaise() && (op.sinfo.line === errorTrgtPos.line && op.sinfo.pos === errorTrgtPos.pos);
        }));

        if (hastrgt) {
            return { safe: false, trgt: true };
        }
        else {
            const cn = callg.invokes.get(ikey) as CallGNode;
            const allcalleesafe = [...cn.callees].every((callee) => {
                if(isSafeInvoke((masm.primitiveInvokeDecls.get(callee) || masm.invokeDecls.get(callee)) as MIRInvokeDecl)) {
                    return true;
                }
                else {
                    const sii = safeinfo.get(callee);
                    return sii !== undefined && sii.safe;
                }
            });
            
            if (!inscc && !haserrorop && allcalleesafe) {
                return { safe: true, trgt: false };
            }
            else {
                const istrgt = hastrgt || [...cn.callees].every((callee) => safeinfo.has(callee) && (safeinfo.get(callee) as { safe: boolean, trgt: boolean }).trgt);
                return { safe: false, trgt: istrgt };
            }
        }
    }
}

function markSafeCalls(entryPoints: MIRInvokeKey[], masm: MIRAssembly, istestbuild: boolean, errorTrgtPos?: { file: string, line: number, pos: number }): Map<MIRInvokeKey, { safe: boolean, trgt: boolean }> {
    const cginfo = constructCallGraphInfo(entryPoints, masm, istestbuild);
    const rcg = [...cginfo.topologicalOrder].reverse();

    const etrgt = errorTrgtPos || { file: "[IGNORE ERROR TARGETING]", line: -1, pos: -1 };
    let safeinfo = new Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>();

    for (let i = 0; i < rcg.length; ++i) {
        const cn = rcg[i];
        
        const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
        let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

        while (worklist.length !== 0) {
            const ikey = worklist.shift() as string;
            const issafe = isBodySafe(ikey, masm, etrgt, cginfo, cscc !== undefined, safeinfo);

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
