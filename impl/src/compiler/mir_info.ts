//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Some handy helpers for computing IR info
//

import { MIRAssembly, MIRFunctionParameter, MIRType } from "./mir_assembly";
import { MIRBasicBlock, MIROpTag, MIRJump, MIRJumpCond, MIRJumpNone, MIROp, MIRRegisterArgument, MIRPhi, MIRLoadUnintVariableValue, MIRConvertValue, MIRLoadConst, MIRTupleHasIndex, MIRRecordHasProperty, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadField, MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral, MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRReturnAssignOfCons, MIRReturnAssign, MIRIsTypeOf, MIRPrefixNotOp, MIRBinKeyLess, MIRBinKeyEq, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionEmpty, MIREphemeralListExtend, MIRConstructorEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorRecordFromEphemeralList, MIRResolvedTypeKey, MIRArgGuard, MIRRegisterAssign, MIRArgument, MIRConstantArgument, MIRStatmentGuard, MIRInject, MIRGuardedOptionInject, MIRExtract } from "./mir_ops";

type FlowLink = {
    label: string,
    succs: Set<string>,
    preds: Set<string>
};

type BlockLiveSet = {
    label: string,
    liveEntry: Map<string, MIRRegisterArgument>,
    liveExit: Map<string, MIRRegisterArgument>
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
            //nothing to do here
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

function computeLiveVarsInBlock(ops: MIROp[], liveOnExit: Map<string, MIRRegisterArgument>): Map<string, MIRRegisterArgument> {
    let live = new Map<string, MIRRegisterArgument>(liveOnExit);

    for (let i = ops.length - 1; i >= 0; --i) {
        const op = ops[i];

        const mod = op.getModVars().map((arg) => arg.nameID);
        mod.forEach((v) => live.delete(v));

        const use = op.getUsedVars();
        use.forEach((v) => live.set(v.nameID, v));
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

        let lexit = new Map<string, MIRRegisterArgument>();
        linfo.forEach((ls) => ls.liveEntry.forEach((v, n) => lexit.set(n, v)));

        if (bb.label === "exit") {
            lexit.set("$$return", new MIRRegisterArgument("$$return"));
        }

        const lentry = computeLiveVarsInBlock(bb.ops, lexit);

        liveInfo.set(bb.label, { label: bb.label, liveEntry: lentry, liveExit: lexit });
    }

    return liveInfo;
}

function computeVarTypes(blocks: Map<string, MIRBasicBlock>, params: MIRFunctionParameter[], masm: MIRAssembly, booltype: MIRResolvedTypeKey): Map<string, MIRType> {
    let vinfo = new Map<string, string>();
    params.forEach((p) => vinfo.set(p.name, p.type));

    blocks.forEach((bb) => {
        bb.ops.forEach((op) => {
            switch (op.tag) {
                case MIROpTag.MIRNop: 
                case MIROpTag.MIRDeadFlow:
                case MIROpTag.MIRAbort:
                case MIROpTag.MIRDeclareGuardFlagLocation: 
                case MIROpTag.MIRSetConstantGuardFlag:
                case MIROpTag.MIRVarLifetimeStart:
                case MIROpTag.MIRVarLifetimeEnd:
                case MIROpTag.MIRAssertCheck:
                case MIROpTag.MIRDebug: {
                    break;
                }
                case MIROpTag.MIRLoadUnintVariableValue: {
                    const luv = op as MIRLoadUnintVariableValue;
                    vinfo.set(luv.trgt.nameID, luv.oftype);
                    break;
                }
                case MIROpTag.MIRConvertValue: {
                    const conv = op as MIRConvertValue;
                    vinfo.set(conv.trgt.nameID, conv.intotype);
                    break;
                }
                case MIROpTag.MIRInject: {
                    const inj = op as MIRInject;
                    vinfo.set(inj.trgt.nameID, inj.intotype);
                    break;
                }
                case MIROpTag.MIRGuardedOptionInject: {
                    const inj = op as MIRGuardedOptionInject;
                    vinfo.set(inj.trgt.nameID, inj.optiontype);
                    break;
                }
                case MIROpTag.MIRExtract: {
                    const ext = op as MIRExtract;
                    vinfo.set(ext.trgt.nameID, ext.intotype);
                    break;
                }
                case MIROpTag.MIRLoadConst: {
                    const lc = op as MIRLoadConst;
                    vinfo.set(lc.trgt.nameID, lc.consttype);
                    break;
                }
                case MIROpTag.MIRTupleHasIndex: {
                    const thi = op as MIRTupleHasIndex;
                    vinfo.set(thi.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRRecordHasProperty: {
                    const rhi = op as MIRRecordHasProperty;
                    vinfo.set(rhi.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndex: {
                    const lti = op as MIRLoadTupleIndex;
                    vinfo.set(lti.trgt.nameID, lti.resulttype);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndexSetGuard: {
                    const ltig = op as MIRLoadTupleIndexSetGuard;
                    vinfo.set(ltig.trgt.nameID, ltig.resulttype);
                    if(ltig.guard instanceof MIRArgGuard) {
                        if (ltig.guard.greg instanceof MIRRegisterArgument) {
                            vinfo.set(ltig.guard.greg.nameID, booltype);
                        }
                    }
                    break;
                }
                case MIROpTag.MIRLoadRecordProperty: {
                    const lrp = op as MIRLoadRecordProperty;
                    vinfo.set(lrp.trgt.nameID, lrp.resulttype);
                    break;
                }
                case MIROpTag.MIRLoadRecordPropertySetGuard: {
                    const lrpg = op as MIRLoadRecordPropertySetGuard;
                    vinfo.set(lrpg.trgt.nameID, lrpg.resulttype);
                    if(lrpg.guard instanceof MIRArgGuard) {
                        if (lrpg.guard.greg instanceof MIRRegisterArgument) {
                            vinfo.set(lrpg.guard.greg.nameID, booltype);
                        }
                    }
                    break;
                }
                case MIROpTag.MIRLoadField: {
                    const lmf = op as MIRLoadField;
                    vinfo.set(lmf.trgt.nameID, lmf.resulttype);
                    break;
                }
                case MIROpTag.MIRTupleProjectToEphemeral: {
                    const pte = op as MIRTupleProjectToEphemeral;
                    vinfo.set(pte.trgt.nameID, pte.epht);
                    break;
                }
                case MIROpTag.MIRRecordProjectToEphemeral: {
                    const pre = op as MIRRecordProjectToEphemeral;
                    vinfo.set(pre.trgt.nameID, pre.epht);
                    break;
                }
                case MIROpTag.MIREntityProjectToEphemeral: {
                    const pee = op as MIREntityProjectToEphemeral;
                    vinfo.set(pee.trgt.nameID, pee.epht);
                    break;
                }
                case MIROpTag.MIRTupleUpdate: {
                    const mi = op as MIRTupleUpdate;
                    vinfo.set(mi.trgt.nameID, mi.argflowtype);
                    break;
                }
                case MIROpTag.MIRRecordUpdate: {
                    const mp = op as MIRRecordUpdate;
                    vinfo.set(mp.trgt.nameID, mp.argflowtype);
                    break;
                }
                case MIROpTag.MIREntityUpdate: {
                    const mf = op as MIREntityUpdate;
                    vinfo.set(mf.trgt.nameID, mf.argflowtype);
                    break;
                }
                case MIROpTag.MIRLoadFromEpehmeralList: {
                    const mle = op as MIRLoadFromEpehmeralList;
                    vinfo.set(mle.trgt.nameID, mle.resulttype);
                    break;
                }
                case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                    const mle = op as MIRMultiLoadFromEpehmeralList;
                    mle.trgts.forEach((trgt) => {
                        vinfo.set(trgt.into.nameID, trgt.oftype);
                    });
                    break;
                }
                case MIROpTag.MIRSliceEpehmeralList: {
                    const mle = op as MIRSliceEpehmeralList;
                    vinfo.set(mle.trgt.nameID, mle.sltype);
                    break;
                }
                case MIROpTag.MIRInvokeFixedFunction: {
                    const invk = op as MIRInvokeFixedFunction;
                    vinfo.set(invk.trgt.nameID, invk.resultType);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualFunction: {
                    const invk = op as MIRInvokeVirtualFunction;
                    vinfo.set(invk.trgt.nameID, invk.resultType);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualOperator: {
                    const invk = op as MIRInvokeVirtualOperator;
                    vinfo.set(invk.trgt.nameID, invk.resultType);
                    break;
                }
                case MIROpTag.MIRConstructorTuple: {
                    const tc = op as MIRConstructorTuple;
                    vinfo.set(tc.trgt.nameID, tc.resultTupleType);
                    break;
                }
                case MIROpTag.MIRConstructorTupleFromEphemeralList: {
                    const tc = op as MIRConstructorTupleFromEphemeralList;
                    vinfo.set(tc.trgt.nameID, tc.resultTupleType);
                    break;
                }
                case MIROpTag.MIRConstructorRecord: {
                    const tc = op as MIRConstructorRecord;
                    vinfo.set(tc.trgt.nameID, tc.resultRecordType);
                    break;
                }
                case MIROpTag.MIRConstructorRecordFromEphemeralList: {
                    const tc = op as MIRConstructorRecordFromEphemeralList;
                    vinfo.set(tc.trgt.nameID, tc.resultRecordType);
                    break;
                }
                case MIROpTag.MIRStructuredAppendTuple: {
                    const at = op as MIRStructuredAppendTuple;
                    vinfo.set(at.trgt.nameID, at.resultTupleType);
                    break;
                }
                case MIROpTag.MIRStructuredJoinRecord: {
                    const sj = op as MIRStructuredJoinRecord;
                    vinfo.set(sj.trgt.nameID, sj.resultRecordType);
                    break;
                }
                case MIROpTag.MIRConstructorEphemeralList: {
                    const tc = op as MIRConstructorEphemeralList;
                    vinfo.set(tc.trgt.nameID, tc.resultEphemeralListType);
                    break;
                }
                case MIROpTag.MIREphemeralListExtend: {
                    const pse = op as MIREphemeralListExtend;
                    vinfo.set(pse.trgt.nameID, pse.resultType);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                    const cc = op as MIRConstructorPrimaryCollectionEmpty;
                    vinfo.set(cc.trgt.nameID, cc.tkey);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                    const cc = op as MIRConstructorPrimaryCollectionSingletons;
                    vinfo.set(cc.trgt.nameID, cc.tkey);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                    const cc = op as MIRConstructorPrimaryCollectionCopies;
                    vinfo.set(cc.trgt.nameID, cc.tkey);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                    const cc = op as MIRConstructorPrimaryCollectionMixed;
                    vinfo.set(cc.trgt.nameID, cc.tkey);
                    break;
                }
                case MIROpTag.MIRBinKeyEq: {
                    const beq = op as MIRBinKeyEq;
                    vinfo.set(beq.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRBinKeyLess: {
                    const bl = op as MIRBinKeyLess;
                    vinfo.set(bl.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRPrefixNotOp: {
                    const pfx = op as MIRPrefixNotOp;
                    vinfo.set(pfx.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRIsTypeOf: {
                    const it = op as MIRIsTypeOf;
                    vinfo.set(it.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRJump: 
                case MIROpTag.MIRJumpCond: 
                case MIROpTag.MIRJumpNone: {
                    break;
                }
                case MIROpTag.MIRRegisterAssign: {
                    const regop = op as MIRRegisterAssign;
                    vinfo.set(regop.trgt.nameID, regop.layouttype);
                    break;
                }
                case MIROpTag.MIRReturnAssign: {
                    const ra = op as MIRReturnAssign;
                    vinfo.set(ra.name.nameID, ra.oftype);
                    break;
                }
                case MIROpTag.MIRReturnAssignOfCons: {
                    const ra = op as MIRReturnAssignOfCons;
                    vinfo.set(ra.name.nameID, ra.oftype);
                    break;
                }
                default: {
                    const po = op as MIRPhi;
                    vinfo.set(po.trgt.nameID, po.layouttype);
                    break;
                }
            }
        });
    });

    let vresinfo = new Map<string, MIRType>();
    vinfo.forEach((v, k) => vresinfo.set(k, masm.typeMap.get(v) as MIRType));

    return vresinfo;
}

function maxConst(cc: bigint, vv: number): bigint {
    const bvv = BigInt(vv);
    return cc >= bvv ? cc : bvv;
}

function maxConsts(cc: bigint, vv: number[]): bigint {
    for (let i = 0; i < vv.length; ++i) {
        const bvv = BigInt(vv[i]);
        cc = cc >= bvv ? cc : bvv;
    }
    return cc;
}

function maxConstArg(cc: bigint, arg: MIRArgument): bigint {
    if(arg instanceof MIRConstantArgument) {
        const args = arg.constantSize();
        return cc >= args ? cc : args;
    }
    else {
        return cc;
    }
}

function maxConstArgs(cc: bigint, args: MIRArgument[]): bigint {
    for(let i = 0; i < args.length; ++i) {
        cc = maxConstArg(cc, args[i]);
    }

    return cc;
}


function maxStructuredArgs<T>(cc: bigint, args: T[], extract: (arg: T) => MIRArgument): bigint {
    for(let i = 0; i < args.length; ++i) {
        cc = maxConstArg(cc, extract(args[i]));
    }

    return cc;
}

function maxStatementGuard(cc: bigint, arg: MIRStatmentGuard | undefined): bigint {
    if(arg === undefined) {
        return cc;
    }
    else {
        if(arg.defaultvar === undefined) {
            return cc;
        } 
        else {
            return maxConstArg(cc, arg.defaultvar);
        }
    }
}

function computeMaxConstantSize(blocks: Map<string, MIRBasicBlock>): bigint {
    let cc = 0n;

    blocks.forEach((bb) => {
        bb.ops.forEach((op) => {
            switch (op.tag) {
                case MIROpTag.MIRConvertValue: {
                    const conv = op as MIRConvertValue;
                    cc = maxConstArg(cc, conv.src);
                    cc = maxStatementGuard(cc, conv.sguard);
                    break;
                }
                case MIROpTag.MIRInject: {
                    const inj = op as MIRInject;
                    cc = maxConstArg(cc, inj.src);
                    break;
                }
                case MIROpTag.MIRGuardedOptionInject: {
                    const inj = op as MIRGuardedOptionInject;
                    cc = maxConstArg(cc, inj.src);
                    cc = maxStatementGuard(cc, inj.sguard);
                    break;
                }
                case MIROpTag.MIRExtract: {
                    const ext = op as MIRExtract;
                    cc = maxConstArg(cc, ext.src);
                    break;
                }
                case MIROpTag.MIRTupleHasIndex: {
                    const thi = op as MIRTupleHasIndex;
                    cc = maxConst(cc, thi.idx);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndex: {
                    const lti = op as MIRLoadTupleIndex;
                    cc = maxConst(cc, lti.idx);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndexSetGuard: {
                    const ltig = op as MIRLoadTupleIndexSetGuard;
                    cc = maxConst(cc, ltig.idx);
                    break;
                }
                case MIROpTag.MIRTupleProjectToEphemeral: {
                    const pte = op as MIRTupleProjectToEphemeral;
                    cc = maxConsts(cc, pte.indecies);
                    break;
                }
                case MIROpTag.MIRTupleUpdate: {
                    const mi = op as MIRTupleUpdate;
                    cc = maxConsts(cc, mi.updates.map((uu) => uu[0]));
                    cc = maxStructuredArgs(cc, mi.updates, (uu) => uu[1]);
                    break;
                }
                case MIROpTag.MIRLoadFromEpehmeralList: {
                    const mle = op as MIRLoadFromEpehmeralList;
                    cc = maxConst(cc, mle.idx);
                    break;
                }
                case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                    const mle = op as MIRMultiLoadFromEpehmeralList;
                    cc = maxConsts(cc, mle.trgts.map((ll) => ll.pos));
                    break;
                }
                case MIROpTag.MIRInvokeFixedFunction: {
                    const invk = op as MIRInvokeFixedFunction;
                    cc = maxConstArgs(cc, invk.args);
                    cc = maxStatementGuard(cc, invk.sguard);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualFunction: {
                    const invk = op as MIRInvokeVirtualFunction;
                    cc = maxConstArgs(cc, invk.args);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualOperator: {
                    const invk = op as MIRInvokeVirtualOperator;
                    cc = maxStructuredArgs(cc, invk.args, (vv) => vv.arg);
                    break;
                }
                case MIROpTag.MIRConstructorTuple: {
                    const tc = op as MIRConstructorTuple;
                    cc = maxConstArgs(cc, tc.args);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                    const cps = op as MIRConstructorPrimaryCollectionSingletons;
                    cc = maxStructuredArgs(cc, cps.args, (vv) => vv[1]);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                    const cpc = op as MIRConstructorPrimaryCollectionCopies;
                    cc = maxStructuredArgs(cc, cpc.args, (vv) => vv[1]);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                    const cpm = op as MIRConstructorPrimaryCollectionMixed;
                    cc = maxStructuredArgs(cc, cpm.args, (vv) => vv[2]);
                    break;
                }
                case MIROpTag.MIRBinKeyEq: {
                    const beq = op as MIRBinKeyEq;
                    cc = maxConstArgs(cc, [beq.lhs, beq.rhs]);
                    cc = maxStatementGuard(cc, beq.sguard);
                    break;
                }
                case MIROpTag.MIRBinKeyLess: {
                    const bl = op as MIRBinKeyLess;
                    cc = maxConstArgs(cc, [bl.lhs, bl.rhs]);
                    cc = maxStatementGuard(cc, bl.sguard);
                    break;
                }
                case MIROpTag.MIRIsTypeOf: {
                    const it = op as MIRIsTypeOf;
                    cc = maxConstArg(cc, it.arg);
                    cc = maxStatementGuard(cc, it.sguard);
                    break;
                }
                case MIROpTag.MIRJumpNone: {
                    const njop = op as MIRJumpNone;
                    cc = maxConstArg(cc, njop.arg);
                    break;
                }
                case MIROpTag.MIRRegisterAssign: {
                    const regop = op as MIRRegisterAssign;
                    cc = maxConstArg(cc, regop.src);
                    cc = maxStatementGuard(cc, regop.sguard);
                    break;
                }
                case MIROpTag.MIRReturnAssign: {
                    const ra = op as MIRReturnAssign;
                    cc = maxConstArg(cc, ra.src);
                    break;
                }
                case MIROpTag.MIRReturnAssignOfCons: {
                    const ra = op as MIRReturnAssignOfCons;
                    cc = maxConstArgs(cc, ra.args);
                    break;
                }
                default: {
                    break;
                }
            }
        });
    });

   return cc;
}

export { FlowLink, BlockLiveSet, computeDominators, topologicalOrder, computeBlockLinks, computeBlockLiveVars, computeVarTypes, computeMaxConstantSize };
