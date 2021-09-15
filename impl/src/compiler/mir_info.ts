//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Some handy helpers for computing IR info
//

import { MIRAssembly, MIRFunctionParameter, MIRType } from "./mir_assembly";
import { MIRBasicBlock, MIROpTag, MIRJump, MIRJumpCond, MIRJumpNone, MIROp, MIRRegisterArgument, MIRPhi, MIRLoadUnintVariableValue, MIRConvertValue, MIRLoadConst, MIRTupleHasIndex, MIRRecordHasProperty, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadField, MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral, MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRReturnAssignOfCons, MIRReturnAssign, MIRIsTypeOf, MIRPrefixNotOp, MIRBinKeyLess, MIRBinKeyEq, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionEmpty, MIREphemeralListExtend, MIRConstructorEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorRecordFromEphemeralList, MIRResolvedTypeKey, MIRArgGuard, MIRRegisterAssign, MIRArgument, MIRConstantArgument } from "./mir_ops";

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
                    xxxx;
                }
                case MIROpTag.MIRGuardedOptionInject: {
                    xxxx;
                }
                case MIROpTag.MIRExtract: {
                    xxxx;
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

function maxconstarg(cc: bigint, arg: MIRArgument): bigint {
    if(arg instanceof MIRConstantArgument) {
        const args = arg.constantSize();
        return cc >= args ? cc : args;
    }
    else {
        return cc;
    }
}

function maxconstargs(cc: bigint, args: MIRArgument[]): bigint {
    xxxx;
}

function computeMaxConstantSize(blocks: Map<string, MIRBasicBlock>): bigint {
    let maxconst = 0n;

    blocks.forEach((bb) => {
        bb.ops.forEach((op) => {
            switch (op.tag) {
                case MIROpTag.MIRConvertValue: {
                    const conv = op as MIRConvertValue;
                    conv.src = propagateAssign_Remap(conv.src, propMap);
                    conv.sguard = propagateAssign_RemapStatementGuard(conv.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRInject: {
                    xxxx;
                }
                case MIROpTag.MIRGuardedOptionInject: {
                    xxxx;
                }
                case MIROpTag.MIRExtract: {
                    xxxx;
                }
                case MIROpTag.MIRTupleHasIndex: {
                    const thi = op as MIRTupleHasIndex;
                    thi.arg = propagateAssign_Remap(thi.arg, propMap);
                    break;
                }
                case MIROpTag.MIRRecordHasProperty: {
                    const rhi = op as MIRRecordHasProperty;
                    rhi.arg = propagateAssign_Remap(rhi.arg, propMap);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndex: {
                    const lti = op as MIRLoadTupleIndex;
                    lti.arg = propagateAssign_Remap(lti.arg, propMap);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndexSetGuard: {
                    const ltig = op as MIRLoadTupleIndexSetGuard;
                    ltig.arg = propagateAssign_Remap(ltig.arg, propMap);
                    break;
                }
                case MIROpTag.MIRLoadRecordProperty: {
                    const lrp = op as MIRLoadRecordProperty;
                    lrp.arg = propagateAssign_Remap(lrp.arg, propMap);
                    break;
                }
                case MIROpTag.MIRLoadRecordPropertySetGuard: {
                    const lrpg = op as MIRLoadRecordPropertySetGuard;
                    lrpg.arg = propagateAssign_Remap(lrpg.arg, propMap);
                    break;
                }
                case MIROpTag.MIRLoadField: {
                    const lmf = op as MIRLoadField;
                    lmf.arg = propagateAssign_Remap(lmf.arg, propMap);
                    break;
                }
                case MIROpTag.MIRTupleProjectToEphemeral: {
                    const pte = op as MIRTupleProjectToEphemeral;
                    pte.arg = propagateAssign_Remap(pte.arg, propMap);
                    break;
                }
                case MIROpTag.MIRRecordProjectToEphemeral: {
                    const pre = op as MIRRecordProjectToEphemeral;
                    pre.arg = propagateAssign_Remap(pre.arg, propMap);
                    break;
                }
                case MIROpTag.MIREntityProjectToEphemeral: {
                    const pee = op as MIREntityProjectToEphemeral;
                    pee.arg = propagateAssign_Remap(pee.arg, propMap);
                    break;
                }
                case MIROpTag.MIRTupleUpdate: {
                    const mi = op as MIRTupleUpdate;
                    mi.arg = propagateAssign_Remap(mi.arg, propMap);
                    mi.updates = propagateAssign_RemapStructuredArgs<[number, MIRArgument, MIRResolvedTypeKey]>(mi.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
                    break;
                }
                case MIROpTag.MIRRecordUpdate: {
                    const mp = op as MIRRecordUpdate;
                    mp.arg = propagateAssign_Remap(mp.arg, propMap);
                    mp.updates = propagateAssign_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mp.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
                    break;
                }
                case MIROpTag.MIREntityUpdate: {
                    const mf = op as MIREntityUpdate;
                    mf.arg = propagateAssign_Remap(mf.arg, propMap);
                    mf.updates = propagateAssign_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mf.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
                    break;
                }
                case MIROpTag.MIRLoadFromEpehmeralList: {
                    const mle = op as MIRLoadFromEpehmeralList;
                    mle.arg = propagateAssign_Remap(mle.arg, propMap);
                    break;
                }
                case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                    const mle = op as MIRMultiLoadFromEpehmeralList;
                    mle.arg = propagateAssign_Remap(mle.arg, propMap);
                    break;
                }
                case MIROpTag.MIRSliceEpehmeralList: {
                    const mle = op as MIRSliceEpehmeralList;
                    mle.arg = propagateAssign_Remap(mle.arg, propMap);
                    break;
                }
                case MIROpTag.MIRInvokeFixedFunction: {
                    const invk = op as MIRInvokeFixedFunction;
                    invk.args = propagateAssign_RemapArgs(invk.args, propMap);
                    invk.sguard = propagateAssign_RemapStatementGuard(invk.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualFunction: {
                    const invk = op as MIRInvokeVirtualFunction;
                    invk.args = propagateAssign_RemapArgs(invk.args, propMap);
                    break;
                }
                case MIROpTag.MIRInvokeVirtualOperator: {
                    const invk = op as MIRInvokeVirtualOperator;
                    invk.args = propagateAssign_RemapStructuredArgs<{ arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }>(invk.args, (u) => {
                        return { arglayouttype: u.arglayouttype, argflowtype: u.argflowtype, arg: propagateAssign_Remap(u.arg, propMap) };
                    });
                    break;
                }
                case MIROpTag.MIRConstructorTuple: {
                    const tc = op as MIRConstructorTuple;
                    tc.args = propagateAssign_RemapArgs(tc.args, propMap);
                    break;
                }
                case MIROpTag.MIRConstructorTupleFromEphemeralList: {
                    const tc = op as MIRConstructorTupleFromEphemeralList;
                    tc.arg = propagateAssign_Remap(tc.arg, propMap);
                    break;
                }
                case MIROpTag.MIRConstructorRecord: {
                    const tc = op as MIRConstructorRecord;
                    tc.args = propagateAssign_RemapStructuredArgs<[string, MIRArgument]>(tc.args, (v) => [v[0], propagateAssign_Remap(v[1], propMap)]);
                    break;
                }
                case MIROpTag.MIRConstructorRecordFromEphemeralList: {
                    const tc = op as MIRConstructorRecordFromEphemeralList;
                    tc.arg = propagateAssign_Remap(tc.arg, propMap);
                    break;
                }
                case MIROpTag.MIRStructuredAppendTuple: {
                    const at = op as MIRStructuredAppendTuple;
                    at.args = propagateAssign_RemapArgs(at.args, propMap);
                    break;
                }
                case MIROpTag.MIRStructuredJoinRecord: {
                    const sj = op as MIRStructuredJoinRecord;
                    sj.args = propagateAssign_RemapArgs(sj.args, propMap);
                    break;
                }
                case MIROpTag.MIRConstructorEphemeralList: {
                    const tc = op as MIRConstructorEphemeralList;
                    tc.args = propagateAssign_RemapArgs(tc.args, propMap);
                    break;
                }
                case MIROpTag.MIREphemeralListExtend: {
                    const pse = op as MIREphemeralListExtend;
                    pse.arg = propagateAssign_Remap(pse.arg, propMap);
                    pse.ext = propagateAssign_RemapArgs(pse.ext, propMap);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                    const cc = op as MIRConstructorPrimaryCollectionSingletons;
                    cc.args = propagateAssign_RemapStructuredArgs<[MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], propagateAssign_Remap(v[1], propMap)]);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                    const cc = op as MIRConstructorPrimaryCollectionCopies;
                    cc.args = propagateAssign_RemapStructuredArgs<[MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], propagateAssign_Remap(v[1], propMap)]);
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                    const cc = op as MIRConstructorPrimaryCollectionMixed;
                    cc.args = propagateAssign_RemapStructuredArgs<[boolean, MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], v[1], propagateAssign_Remap(v[2], propMap)]);
                    break;
                }
                case MIROpTag.MIRBinKeyEq: {
                    const beq = op as MIRBinKeyEq;
                    beq.lhs = propagateAssign_Remap(beq.lhs, propMap);
                    beq.rhs = propagateAssign_Remap(beq.rhs, propMap);
                    beq.sguard = propagateAssign_RemapStatementGuard(beq.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRBinKeyLess: {
                    const bl = op as MIRBinKeyLess;
                    bl.lhs = propagateAssign_Remap(bl.lhs, propMap);
                    bl.rhs = propagateAssign_Remap(bl.rhs, propMap);
                    bl.sguard = propagateAssign_RemapStatementGuard(bl.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRPrefixNotOp: {
                    const pfx = op as MIRPrefixNotOp;
                    pfx.arg = propagateAssign_Remap(pfx.arg, propMap);
                    break;
                }
                case MIROpTag.MIRIsTypeOf: {
                    const it = op as MIRIsTypeOf;
                    it.arg = propagateAssign_Remap(it.arg, propMap);
                    it.sguard = propagateAssign_RemapStatementGuard(it.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRJump: {
                    break;
                }
                case MIROpTag.MIRJumpCond: {
                    const cjop = op as MIRJumpCond;
                    cjop.arg = propagateAssign_Remap(cjop.arg, propMap);
                    break;
                }
                case MIROpTag.MIRJumpNone: {
                    const njop = op as MIRJumpNone;
                    njop.arg = propagateAssign_Remap(njop.arg, propMap);
                    break;
                }
                case MIROpTag.MIRRegisterAssign: {
                    const regop = op as MIRRegisterAssign;
                    regop.src = propagateAssign_Remap(regop.src, propMap);
                    regop.sguard = propagateAssign_RemapStatementGuard(regop.sguard, propMap);
                    break;
                }
                case MIROpTag.MIRReturnAssign: {
                    const ra = op as MIRReturnAssign;
                    ra.src = propagateAssign_Remap(ra.src, propMap);
                    break;
                }
                case MIROpTag.MIRReturnAssignOfCons: {
                    const ra = op as MIRReturnAssignOfCons;
                    ra.args = propagateAssign_RemapArgs(ra.args, propMap);
                    break;
                }
                case MIROpTag.MIRPhi: {
                    const mp = op as MIRPhi;
                    mp.src
                    break;
                }
                default: {
                    assert(false);
                    break;
                }
            }
        });
    });

    let vresinfo = new Map<string, MIRType>();
    vinfo.forEach((v, k) => vresinfo.set(k, masm.typeMap.get(v) as MIRType));

    return vresinfo;
}

export { FlowLink, BlockLiveSet, computeDominators, topologicalOrder, computeBlockLinks, computeBlockLiveVars, computeVarTypes, computeMaxConstantSize };
