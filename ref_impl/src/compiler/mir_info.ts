//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Some handy helpers for computing IR info
//

import * as assert from "assert";
import { MIRBasicBlock, MIROpTag, MIRJump, MIRJumpCond, MIRJumpNone, MIROp } from "./mir_ops";

type FlowLink = {
    label: string,
    succs: Set<string>,
    preds: Set<string>
};

type BlockLiveSet = {
    label: string,
    liveEntry: Set<string>,
    liveExit: Set<string>
};

function computeBlockLinks(blocks: Map<string, MIRBasicBlock>): Map<string, FlowLink> {
    let links = new Map<string, FlowLink>();
    let done = new Set<string>();
    let worklist = ["entry"];

    while (worklist.length !== 0) {
        const bb = worklist.shift() as string;
        const block = blocks.get(bb) as MIRBasicBlock;
        if (block.ops.length === 0) {
            continue;
        }

        let link = links.get(bb) || { label: bb, succs: new Set<string>(), preds: new Set<string>() };
        if (!links.has(bb)) {
            links.set(bb, link);
        }

        const jop = block.ops[block.ops.length - 1];
        if (jop.tag === MIROpTag.MIRJump) {
            const jmp = jop as MIRJump;
            link.succs.add(jmp.trgtblock);
        }
        else if (jop.tag === MIROpTag.MIRJumpCond) {
            const jmp = jop as MIRJumpCond;
            link.succs.add(jmp.trueblock);
            link.succs.add(jmp.falseblock);
        }
        else if (jop.tag === MIROpTag.MIRJumpNone) {
            const jmp = jop as MIRJumpNone;
            link.succs.add(jmp.someblock);
            link.succs.add(jmp.noneblock);

        }
        else {
            assert(block.label === "exit");
        }

        done.add(bb);
        link.succs.forEach((succ) => {
            if (!done.has(succ) && !worklist.includes(succ)) {
                worklist.push(succ);
            }

            if (!links.has(succ)) {
                links.set(succ, { label: succ, succs: new Set<string>(), preds: new Set<string>() });
            }

            let slink = links.get(succ) as FlowLink;
            slink.preds.add(bb);
        });
    }

    return links;
}

function computeDominators(blocks: Map<string, MIRBasicBlock>): Map<string, MIRBasicBlock[]> {
    let allNodes: MIRBasicBlock[] = [];
    let allNonEntryNodes: MIRBasicBlock[] = [];
    blocks.forEach((v, k) => {
        allNodes.push(v);
        if (k !== "entry") {
            allNonEntryNodes.push(v);
        }
    });

    const flow = computeBlockLinks(blocks);

    let dom = new Map<string, MIRBasicBlock[]>().set("entry", [blocks.get("entry") as MIRBasicBlock]);

    allNonEntryNodes.forEach((n) => dom.set(n.label, [...allNodes]));

    let changed = true;
    while (changed) {
        for (let i = 0; i < allNonEntryNodes.length; ++i) {
            const n = allNonEntryNodes[i];
            const preds = (flow.get(n.label) as FlowLink).preds;

            let pdinter: MIRBasicBlock[] | undefined = [];
            preds.forEach((pred) => {
                const pdom = dom.get(pred) as MIRBasicBlock[];
                if (pdinter === undefined) {
                    pdinter = [...pdom];
                }
                else {
                    pdinter = pdinter.filter((v) => pdom.findIndex((dn) => dn.label === v.label) !== -1);
                }
            });

            const ndom = [n, ...(pdinter as MIRBasicBlock[])];
            changed = changed || ndom.length !== (dom.get(n.label) as MIRBasicBlock[]).length;

            dom.set(n.label, ndom);
        }
    }

    return dom;
}

function topoVisit(n: MIRBasicBlock, tordered: MIRBasicBlock[], flow: Map<string, FlowLink>, blocks: Map<string, MIRBasicBlock>) {
    if (tordered.findIndex((b) => b.label === n.label) !== -1) {
        return;
    }

    const succs = (flow.get(n.label) as FlowLink).succs;
    succs.forEach((succ) => topoVisit(blocks.get(succ) as MIRBasicBlock, tordered, flow, blocks));

    tordered.push(n);
}

function topologicalOrder(blocks: Map<string, MIRBasicBlock>): MIRBasicBlock[] {
    let tordered: MIRBasicBlock[] = [];
    const flow = computeBlockLinks(blocks);

    topoVisit(blocks.get("entry") as MIRBasicBlock, tordered, flow, blocks);

    return tordered.reverse();
}

function computeLiveVarsInBlock(ops: MIROp[], liveOnExit: Set<string>): Set<string> {
    let live = new Set<string>(liveOnExit);

    for (let i = ops.length - 1; i >= 0; --i) {
        const op = ops[i];

        const mod = op.getModVars().map((arg) => arg.nameID);
        mod.forEach((v) => live.delete(v));

        const use = op.getUsedVars().map((v) => v.nameID);
        use.forEach((v) => live.add(v));
    }

    return live;
}

function computeBlockLiveVars(blocks: Map<string, MIRBasicBlock>): Map<string, BlockLiveSet> {
    let liveInfo = new Map<string, BlockLiveSet>();

    const flow = computeBlockLinks(blocks);
    const worklist = topologicalOrder(blocks).reverse();

    for (let i = 0; i < worklist.length; ++i) {
        const bb = worklist[i];
        const finfo = flow.get(bb.label) as FlowLink;

        let linfo: BlockLiveSet[] = [];
        finfo.succs.forEach((succ) => linfo.push(liveInfo.get(succ) as BlockLiveSet));

        let lexit = new Set<string>();
        linfo.forEach((ls) => ls.liveEntry.forEach((lv) => lexit.add(lv)));

        if (bb.label === "exit") {
            lexit.add("_return_");
        }

        const lentry = computeLiveVarsInBlock(bb.ops, lexit);

        liveInfo.set(bb.label, { label: bb.label, liveEntry: lentry, liveExit: lexit });
    }

    return liveInfo;
}

export { FlowLink, BlockLiveSet, computeDominators, topologicalOrder, computeBlockLinks, computeBlockLiveVars };
