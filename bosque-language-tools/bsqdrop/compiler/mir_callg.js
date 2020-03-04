"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
//
//Compute the static call graph for an assembly
//
const assert = require("assert");
const mir_ops_1 = require("./mir_ops");
function computeCalleesInBlocks(blocks, invokeNode, assembly) {
    blocks.forEach((block) => {
        for (let i = 0; i < block.ops.length; ++i) {
            const op = block.ops[i];
            switch (op.tag) {
                case mir_ops_1.MIROpTag.MIRLoadConstSafeString: {
                    const lvs = op;
                    if (lvs.vfunckey !== undefined) {
                        invokeNode.callees.add(lvs.vfunckey);
                    }
                    break;
                }
                case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
                    const lcs = op;
                    if (lcs.pfunckey !== undefined) {
                        invokeNode.callees.add(lcs.pfunckey);
                    }
                    break;
                }
                case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
                    const cdecl = assembly.constantDecls.get(op.ckey);
                    invokeNode.callees.add(cdecl.value);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
                    const fdecl = assembly.fieldDecls.get(op.fkey);
                    invokeNode.callees.add(fdecl.value);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckDirect: {
                    const icd = op;
                    invokeNode.callees.add(icd.ikey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
                    //TODO lookup all possible vtargets and add them
                    assert(false);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                    invokeNode.callees.add(op.mkey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
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
function sccVisit(cn, scc, marked, invokes) {
    if (marked.has(cn.invoke)) {
        return;
    }
    scc.add(cn.invoke);
    marked.add(cn.invoke);
    cn.callers.forEach((pred) => sccVisit(invokes.get(pred), scc, marked, invokes));
}
function topoVisit(cn, pending, tordered, invokes) {
    if (pending.findIndex((vn) => vn.invoke === cn.invoke) !== -1 || tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
        return;
    }
    pending.push(cn);
    cn.callees.forEach((succ) => invokes.get(succ).callers.add(cn.invoke));
    cn.callees.forEach((succ) => topoVisit(invokes.get(succ), pending, tordered, invokes));
    tordered.push(cn);
}
function processBodyInfo(bkey, binfo, assembly) {
    let cn = { invoke: bkey, callees: new Set(), callers: new Set() };
    binfo.forEach((b) => {
        computeCalleesInBlocks(b.body, cn, assembly);
    });
    return cn;
}
function constructCallGraphInfo(entryPoints, assembly) {
    let invokes = new Map();
    assembly.invokeDecls.forEach((ivk, ikey) => {
        invokes.set(ikey, processBodyInfo(ikey, [ivk.body], assembly));
    });
    assembly.primitiveInvokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: ikey, callees: new Set(), callers: new Set() };
        ivk.pcodes.forEach((pc) => cn.callees.add(pc.code));
        invokes.set(cn.invoke, cn);
    });
    let roots = [];
    let tordered = [];
    entryPoints.forEach((ivk) => {
        roots.push(invokes.get(ivk));
        topoVisit(invokes.get(ivk), [], tordered, invokes);
    });
    assembly.constantDecls.forEach((cdecl) => {
        const civk = assembly.invokeDecls.get(cdecl.value);
        invokes.set(cdecl.value, processBodyInfo(cdecl.value, [civk.body], assembly));
    });
    tordered = tordered.reverse();
    let marked = new Set();
    let recursive = [];
    for (let i = 0; i < tordered.length; ++i) {
        let scc = new Set();
        sccVisit(tordered[i], scc, marked, invokes);
        if (scc.size > 1 || tordered[i].callees.has(tordered[i].invoke)) {
            recursive.push(scc);
        }
    }
    return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
}
exports.constructCallGraphInfo = constructCallGraphInfo;
//# sourceMappingURL=mir_callg.js.map