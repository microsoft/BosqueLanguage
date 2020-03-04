"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
//
//Some handy helpers for computing IR info
//
const mir_ops_1 = require("./mir_ops");
function computeBlockLinks(blocks) {
    let links = new Map();
    let done = new Set();
    let worklist = ["entry"];
    while (worklist.length !== 0) {
        const bb = worklist.shift();
        const block = blocks.get(bb);
        if (block.ops.length === 0) {
            continue;
        }
        let link = links.get(bb) || { label: bb, succs: new Set(), preds: new Set() };
        if (!links.has(bb)) {
            links.set(bb, link);
        }
        const jop = block.ops[block.ops.length - 1];
        if (jop.tag === mir_ops_1.MIROpTag.MIRJump) {
            const jmp = jop;
            link.succs.add(jmp.trgtblock);
        }
        else if (jop.tag === mir_ops_1.MIROpTag.MIRJumpCond) {
            const jmp = jop;
            link.succs.add(jmp.trueblock);
            link.succs.add(jmp.falseblock);
        }
        else if (jop.tag === mir_ops_1.MIROpTag.MIRJumpNone) {
            const jmp = jop;
            link.succs.add(jmp.someblock);
            link.succs.add(jmp.noneblock);
        }
        else {
            //nothing to do here
        }
        done.add(bb);
        link.succs.forEach((succ) => {
            if (!done.has(succ) && !worklist.includes(succ)) {
                worklist.push(succ);
            }
            if (!links.has(succ)) {
                links.set(succ, { label: succ, succs: new Set(), preds: new Set() });
            }
            let slink = links.get(succ);
            slink.preds.add(bb);
        });
    }
    return links;
}
exports.computeBlockLinks = computeBlockLinks;
function computeDominators(blocks) {
    let allNodes = [];
    let allNonEntryNodes = [];
    blocks.forEach((v, k) => {
        allNodes.push(v);
        if (k !== "entry") {
            allNonEntryNodes.push(v);
        }
    });
    const flow = computeBlockLinks(blocks);
    let dom = new Map().set("entry", [blocks.get("entry")]);
    allNonEntryNodes.forEach((n) => dom.set(n.label, [...allNodes]));
    let changed = true;
    while (changed) {
        for (let i = 0; i < allNonEntryNodes.length; ++i) {
            const n = allNonEntryNodes[i];
            const preds = flow.get(n.label).preds;
            let pdinter = [];
            preds.forEach((pred) => {
                const pdom = dom.get(pred);
                if (pdinter === undefined) {
                    pdinter = [...pdom];
                }
                else {
                    pdinter = pdinter.filter((v) => pdom.findIndex((dn) => dn.label === v.label) !== -1);
                }
            });
            const ndom = [n, ...pdinter];
            changed = changed || ndom.length !== dom.get(n.label).length;
            dom.set(n.label, ndom);
        }
    }
    return dom;
}
exports.computeDominators = computeDominators;
function topoVisit(n, tordered, flow, blocks) {
    if (tordered.findIndex((b) => b.label === n.label) !== -1) {
        return;
    }
    const succs = flow.get(n.label).succs;
    succs.forEach((succ) => topoVisit(blocks.get(succ), tordered, flow, blocks));
    tordered.push(n);
}
function topologicalOrder(blocks) {
    let tordered = [];
    const flow = computeBlockLinks(blocks);
    topoVisit(blocks.get("entry"), tordered, flow, blocks);
    return tordered.reverse();
}
exports.topologicalOrder = topologicalOrder;
function computeLiveVarsInBlock(ops, liveOnExit) {
    let live = new Set(liveOnExit);
    for (let i = ops.length - 1; i >= 0; --i) {
        const op = ops[i];
        const mod = op.getModVars().map((arg) => arg.nameID);
        mod.forEach((v) => live.delete(v));
        const use = op.getUsedVars().map((v) => v.nameID);
        use.forEach((v) => live.add(v));
    }
    return live;
}
function computeBlockLiveVars(blocks) {
    let liveInfo = new Map();
    const flow = computeBlockLinks(blocks);
    const worklist = topologicalOrder(blocks).reverse();
    for (let i = 0; i < worklist.length; ++i) {
        const bb = worklist[i];
        const finfo = flow.get(bb.label);
        let linfo = [];
        finfo.succs.forEach((succ) => linfo.push(liveInfo.get(succ)));
        let lexit = new Set();
        linfo.forEach((ls) => ls.liveEntry.forEach((lv) => lexit.add(lv)));
        if (bb.label === "exit") {
            lexit.add("_return_");
        }
        const lentry = computeLiveVarsInBlock(bb.ops, lexit);
        liveInfo.set(bb.label, { label: bb.label, liveEntry: lentry, liveExit: lexit });
    }
    return liveInfo;
}
exports.computeBlockLiveVars = computeBlockLiveVars;
//# sourceMappingURL=mir_info.js.map