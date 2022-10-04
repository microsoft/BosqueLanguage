//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Some handy helpers for computing IR info
//

import { assert } from "console";
import { MIRAssembly, MIRFunctionParameter, MIRType } from "./mir_assembly";
import { MIRBasicBlock, MIROpTag, MIRJump, MIRJumpCond, MIRJumpNone, MIROp, MIRRegisterArgument, MIRLoadUnintVariableValue, MIRConvertValue, MIRLoadConst, MIRTupleHasIndex, MIRRecordHasProperty, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadField, MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral, MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRReturnAssignOfCons, MIRReturnAssign, MIRIsTypeOf, MIRPrefixNotOp, MIRBinKeyLess, MIRBinKeyEq, MIRConstructorPrimaryCollectionOneElement, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionEmpty, MIREphemeralListExtend, MIRConstructorEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorRecordFromEphemeralList, MIRResolvedTypeKey, MIRArgGuard, MIRRegisterAssign, MIRInject, MIRGuardedOptionInject, MIRExtract, MIRLogicAction, MIRConstructorEntityDirect } from "./mir_ops";

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

function computeVarTypes(blocks: Map<string, MIRBasicBlock>, params: MIRFunctionParameter[], masm: MIRAssembly, booltype: MIRType): Map<string, Map<string, MIRType>> {
    let vinfo = new Map<string, Map<string, MIRType>>();
    let bexit = new Map<string, Map<string, MIRType>>();

    function tresolve(tt: MIRResolvedTypeKey): MIRType {
        return masm.typeMap.get(tt) as MIRType;
    }

    let entrytypes = new Map<string, MIRType>();
    params.forEach((p) => entrytypes.set(p.name, masm.typeMap.get(p.type) as MIRType));
    vinfo.set("entry", entrytypes);

    const links = computeBlockLinks(blocks);
    const liveinfo = computeBlockLiveVars(blocks);
    const ordered = topologicalOrder(blocks);
    for(let i = 0; i < ordered.length; ++i) {
        const bb = ordered[i];

        let ctypes = new Map<string, MIRType>();
        if(bb.label === "entry") {
            [...entrytypes].forEach((eti) => ctypes.set(eti[0], eti[1]));
        }
        else {
            [...(liveinfo.get(bb.label) as BlockLiveSet).liveEntry]
                .map((eti) => eti[0])
                .forEach((ev) => {
                    const rtl = [...(links.get(bb.label) as FlowLink).preds].map((pred) => ((bexit.get(pred) as Map<string, MIRType>).get(ev) as MIRType));
                    assert(rtl.length !== 0 && rtl.every((tt) => rtl.every((ott) => tt.typeID === ott.typeID)), "Should all be same type at join points!");

                    ctypes.set(ev, rtl[0]);
                });

            let bentrytypes = new Map<string, MIRType>();
            [...ctypes].forEach((ee) => bentrytypes.set(ee[0], ee[1]));
                
            vinfo.set(bb.label, ctypes)
        }

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
                    ctypes.set(luv.trgt.nameID, tresolve(luv.oftype));
                    break;
                }
                case MIROpTag.MIRConvertValue: {
                    const conv = op as MIRConvertValue;
                    ctypes.set(conv.trgt.nameID, tresolve(conv.intotype));
                    break;
                }
                case MIROpTag.MIRInject: {
                    const inj = op as MIRInject;
                    ctypes.set(inj.trgt.nameID, tresolve(inj.intotype));
                    break;
                }
                case MIROpTag.MIRGuardedOptionInject: {
                    const inj = op as MIRGuardedOptionInject;
                    ctypes.set(inj.trgt.nameID, tresolve(inj.optiontype));
                    break;
                }
                case MIROpTag.MIRExtract: {
                    const ext = op as MIRExtract;
                    ctypes.set(ext.trgt.nameID, tresolve(ext.intotype));
                    break;
                }
                case MIROpTag.MIRLoadConst: {
                    const lc = op as MIRLoadConst;
                    ctypes.set(lc.trgt.nameID, tresolve(lc.consttype));
                    break;
                }
                case MIROpTag.MIRTupleHasIndex: {
                    const thi = op as MIRTupleHasIndex;
                    ctypes.set(thi.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRRecordHasProperty: {
                    const rhi = op as MIRRecordHasProperty;
                    ctypes.set(rhi.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRLoadTupleIndex: {
                    const lti = op as MIRLoadTupleIndex;
                    ctypes.set(lti.trgt.nameID, tresolve(lti.resulttype));
                    break;
                }
                case MIROpTag.MIRLoadTupleIndexSetGuard: {
                    const ltig = op as MIRLoadTupleIndexSetGuard;
                    ctypes.set(ltig.trgt.nameID, tresolve(ltig.resulttype));
                    if(ltig.guard instanceof MIRArgGuard) {
                        if (ltig.guard.greg instanceof MIRRegisterArgument) {
                            ctypes.set(ltig.guard.greg.nameID, booltype);
                        }
                    }
                    break;
                }
                case MIROpTag.MIRLoadRecordProperty: {
                    const lrp = op as MIRLoadRecordProperty;
                    ctypes.set(lrp.trgt.nameID, tresolve(lrp.resulttype));
                    break;
                }
                case MIROpTag.MIRLoadRecordPropertySetGuard: {
                    const lrpg = op as MIRLoadRecordPropertySetGuard;
                    ctypes.set(lrpg.trgt.nameID, tresolve(lrpg.resulttype));
                    if(lrpg.guard instanceof MIRArgGuard) {
                        if (lrpg.guard.greg instanceof MIRRegisterArgument) {
                            ctypes.set(lrpg.guard.greg.nameID, booltype);
                        }
                    }
                    break;
                }
                case MIROpTag.MIRLoadField: {
                    const lmf = op as MIRLoadField;
                    ctypes.set(lmf.trgt.nameID, tresolve(lmf.resulttype));
                    break;
                }
                case MIROpTag.MIRTupleProjectToEphemeral: {
                    const pte = op as MIRTupleProjectToEphemeral;
                    ctypes.set(pte.trgt.nameID, tresolve(pte.epht));
                    break;
                }
                case MIROpTag.MIRRecordProjectToEphemeral: {
                    const pre = op as MIRRecordProjectToEphemeral;
                    ctypes.set(pre.trgt.nameID, tresolve(pre.epht));
                    break;
                }
                case MIROpTag.MIREntityProjectToEphemeral: {
                    const pee = op as MIREntityProjectToEphemeral;
                    ctypes.set(pee.trgt.nameID, tresolve(pee.epht));
                    break;
                }
                case MIROpTag.MIRTupleUpdate: {
                    const mi = op as MIRTupleUpdate;
                    ctypes.set(mi.trgt.nameID, tresolve(mi.argflowtype));
                    break;
                }
                case MIROpTag.MIRRecordUpdate: {
                    const mp = op as MIRRecordUpdate;
                    ctypes.set(mp.trgt.nameID, tresolve(mp.argflowtype));
                    break;
                }
                case MIROpTag.MIREntityUpdate: {
                    const mf = op as MIREntityUpdate;
                    ctypes.set(mf.trgt.nameID, tresolve(mf.argflowtype));
                    break;
                }
                case MIROpTag.MIRLoadFromEpehmeralList: {
                    const mle = op as MIRLoadFromEpehmeralList;
                    ctypes.set(mle.trgt.nameID, tresolve(mle.resulttype));
                    break;
                }
                case MIROpTag.MIRMultiLoadFromEpehmeralList: {
                    const mle = op as MIRMultiLoadFromEpehmeralList;
                    mle.trgts.forEach((trgt) => {
                        ctypes.set(trgt.into.nameID, tresolve(trgt.oftype));
                    });
                    break;
                }
                case MIROpTag.MIRSliceEpehmeralList: {
                    const mle = op as MIRSliceEpehmeralList;
                    ctypes.set(mle.trgt.nameID, tresolve(mle.sltype));
                    break;
                }
                case MIROpTag.MIRInvokeFixedFunction: {
                    const invk = op as MIRInvokeFixedFunction;
                    ctypes.set(invk.trgt.nameID, tresolve(invk.resultType));
                    break;
                }
                case MIROpTag.MIRInvokeVirtualFunction: {
                    const invk = op as MIRInvokeVirtualFunction;
                    ctypes.set(invk.trgt.nameID, tresolve(invk.resultType));
                    break;
                }
                case MIROpTag.MIRInvokeVirtualOperator: {
                    const invk = op as MIRInvokeVirtualOperator;
                    ctypes.set(invk.trgt.nameID, tresolve(invk.resultType));
                    break;
                }
                case MIROpTag.MIRConstructorTuple: {
                    const tc = op as MIRConstructorTuple;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.resultTupleType));
                    break;
                }
                case MIROpTag.MIRConstructorTupleFromEphemeralList: {
                    const tc = op as MIRConstructorTupleFromEphemeralList;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.resultTupleType));
                    break;
                }
                case MIROpTag.MIRConstructorRecord: {
                    const tc = op as MIRConstructorRecord;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.resultRecordType));
                    break;
                }
                case MIROpTag.MIRConstructorRecordFromEphemeralList: {
                    const tc = op as MIRConstructorRecordFromEphemeralList;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.resultRecordType));
                    break;
                }
                case MIROpTag.MIRStructuredAppendTuple: {
                    const at = op as MIRStructuredAppendTuple;
                    ctypes.set(at.trgt.nameID, tresolve(at.resultTupleType));
                    break;
                }
                case MIROpTag.MIRStructuredJoinRecord: {
                    const sj = op as MIRStructuredJoinRecord;
                    ctypes.set(sj.trgt.nameID, tresolve(sj.resultRecordType));
                    break;
                }
                case MIROpTag.MIRConstructorEphemeralList: {
                    const tc = op as MIRConstructorEphemeralList;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.resultEphemeralListType));
                    break;
                }
                case MIROpTag.MIRConstructorEntityDirect: {
                    const tc = op as MIRConstructorEntityDirect;
                    ctypes.set(tc.trgt.nameID, tresolve(tc.entityType));
                    break;
                }
                case MIROpTag.MIREphemeralListExtend: {
                    const pse = op as MIREphemeralListExtend;
                    ctypes.set(pse.trgt.nameID, tresolve(pse.resultType));
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                    const cc = op as MIRConstructorPrimaryCollectionEmpty;
                    ctypes.set(cc.trgt.nameID, tresolve(cc.tkey));
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionOneElement: {
                    const cc = op as MIRConstructorPrimaryCollectionOneElement;
                    ctypes.set(cc.trgt.nameID, tresolve(cc.tkey));
                    break;
                }
                case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                    const cc = op as MIRConstructorPrimaryCollectionSingletons;
                    ctypes.set(cc.trgt.nameID, tresolve(cc.tkey));
                    break;
                }
                case MIROpTag.MIRBinKeyEq: {
                    const beq = op as MIRBinKeyEq;
                    ctypes.set(beq.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRBinKeyLess: {
                    const bl = op as MIRBinKeyLess;
                    ctypes.set(bl.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRPrefixNotOp: {
                    const pfx = op as MIRPrefixNotOp;
                    ctypes.set(pfx.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRLogicAction: {
                    const it = op as MIRLogicAction;
                    ctypes.set(it.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRIsTypeOf: {
                    const it = op as MIRIsTypeOf;
                    ctypes.set(it.trgt.nameID, booltype);
                    break;
                }
                case MIROpTag.MIRJump: 
                case MIROpTag.MIRJumpCond: 
                case MIROpTag.MIRJumpNone: {
                    break;
                }
                case MIROpTag.MIRRegisterAssign: {
                    const regop = op as MIRRegisterAssign;
                    ctypes.set(regop.trgt.nameID, tresolve(regop.layouttype));
                    break;
                }
                case MIROpTag.MIRReturnAssign: {
                    const ra = op as MIRReturnAssign;
                    ctypes.set(ra.name.nameID, tresolve(ra.oftype));
                    break;
                }
                case MIROpTag.MIRReturnAssignOfCons: {
                    const ra = op as MIRReturnAssignOfCons;
                    ctypes.set(ra.name.nameID, tresolve(ra.oftype));
                    break;
                }
                default: {
                    assert(false, "Shouldn't be phi nodes yet!!!");
                    break;
                }
            }
        });

        bexit.set(bb.label, ctypes);
    }

    return vinfo;
}

export { FlowLink, BlockLiveSet, computeDominators, topologicalOrder, computeBlockLinks, computeBlockLiveVars, computeVarTypes };
