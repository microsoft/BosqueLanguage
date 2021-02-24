//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRArgument, MIRAssertCheck, MIRConvertValue, MIRDebug, MIRGuard, MIRMaskGuard, MIROp, MIROpTag, MIRRegisterArgument, MIRArgGuard, MIRLoadConst, MIRTupleHasIndex, MIRRecordHasProperty, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadField, MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral, MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate, MIRResolvedTypeKey, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorEphemeralList, MIREphemeralListExtend, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRBinKeyEq, MIRBinKeyLess, MIRPrefixNotOp, MIRAllTrue, MIRIsTypeOf, MIRJumpCond, MIRJumpNone, MIRRegisterAssign, MIRReturnAssign, MIRReturnAssignOfCons, MIRPhi, MIRBody, MIRBasicBlock, MIRStatmentGuard, MIRJump, MIRSomeTrue } from "./mir_ops";

function getEmptyBlocks(b: MIRBody): MIRBasicBlock[] {
    return [...b.body].filter((b) => b[0] !== "entry" && b[0] !== "exit" && b[0] !== "returnassign" && b[1].ops.length === 0).map((b) => b[1]);
}

function cleanDeadBlocks(b: MIRBody) {
    const allempty = getEmptyBlocks(b);
    allempty.forEach((bb) => b.body.delete(bb.label));

    let dblock = [...b.body].find((bb) => bb[1].ops.some((op) => op.tag === MIROpTag.MIRDeadFlow));
    while(dblock !== undefined) {
        const rblock = dblock;
        b.body.delete(rblock[0]);

        b.body.forEach((bb) => {
            const jidx = bb.ops.length - 1;
            if(jidx >= 0) {
                const jop = bb.ops[jidx];
                if(jop instanceof MIRJumpCond && (jop.trueblock === rblock[0] || jop.falseblock === rblock[0])) {
                    const ujop = new MIRJump(jop.sinfo, jop.trueblock !== rblock[0] ? jop.trueblock : jop.falseblock);
                    bb.ops[jidx] = ujop;
                }
                else if(jop instanceof MIRJumpNone && (jop.noneblock === rblock[0] || jop.someblock === rblock[0])) {
                    const ujop = new MIRJump(jop.sinfo, jop.noneblock !== rblock[0] ? jop.noneblock : jop.someblock);
                    bb.ops[jidx] = ujop;
                }
                else {
                    ;
                }
            }
        });

        dblock = [...b.body].find((bb) => bb[1].ops.some((op) => op.tag === MIROpTag.MIRDeadFlow));
    }
}

function propagateAssign_Bind(treg: MIRRegisterArgument, arg: MIRArgument, propMap: Map<string, MIRArgument>) {
    assert(!propMap.has(treg.nameID));
    propMap.set(treg.nameID, arg);
}

function propagateAssign_Kill(arg: MIRRegisterArgument, propMap: Map<string, MIRArgument>) {
    let killset = new Set<string>();
    propMap.forEach((v, k) => {
        if (v instanceof MIRRegisterArgument && v.nameID === arg.nameID) {
            killset.add(k);
        }
    });

    killset.forEach((k) => propMap.delete(k));
}

function propagateAssign_Remap(arg: MIRArgument, propMap: Map<string, MIRArgument>): MIRArgument {
    return (arg instanceof MIRRegisterArgument && propMap.has(arg.nameID)) ? propMap.get(arg.nameID) as MIRArgument : arg;
}

function propagateAssign_RemapGuard(arg: MIRGuard | undefined, propMap: Map<string, MIRArgument>): MIRGuard | undefined {
    if(arg === undefined) {
        return arg;
    }
    else if (arg instanceof MIRMaskGuard) {
        return arg;
    }
    else {
        return new MIRArgGuard(propagateAssign_Remap((arg as MIRArgGuard).greg, propMap));
    }
}

function propagateAssign_RemapStatementGuard(arg: MIRStatmentGuard | undefined, propMap: Map<string, MIRArgument>): MIRStatmentGuard | undefined {
    if(arg === undefined) {
        return arg;
    }
    else {
        const rguard = propagateAssign_RemapGuard(arg.guard, propMap) as MIRGuard;
        const ralt = arg.altvalue !== undefined ? propagateAssign_Remap(arg.altvalue, propMap) : undefined;

        return new MIRStatmentGuard(rguard, ralt);
    }
}

function propagateAssign_RemapArgs(args: MIRArgument[], propMap: Map<string, MIRArgument>): MIRArgument[] {
    return args.map((v) => propagateAssign_Remap(v, propMap));
}

function propagateAssign_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function propagateAssignForOp(op: MIROp, propMap: Map<string, MIRArgument>) {
    switch (op.tag) {
        case MIROpTag.MIRNop: 
        case MIROpTag.MIRDeadFlow:
        case MIROpTag.MIRAbort: 
        case MIROpTag.MIRLoadUnintVariableValue: 
        case MIROpTag.MIRDeclareGuardFlagLocation: 
        case MIROpTag.MIRSetConstantGuardFlag:
        case MIROpTag.MIRLoadConst:
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            break;
        }
        case MIROpTag.MIRAssertCheck: {
            const asrt = op as MIRAssertCheck;
            asrt.arg = propagateAssign_Remap(asrt.arg, propMap);
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = propagateAssign_Remap(dbg.value, propMap);
            }
            break;
        }
        case MIROpTag.MIRConvertValue: {
            const conv = op as MIRConvertValue;
            conv.src = propagateAssign_Remap(conv.src, propMap);
            conv.guard = propagateAssign_RemapStatementGuard(conv.guard, propMap);
            break;
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
            invk.guard = propagateAssign_RemapStatementGuard(invk.guard, propMap);
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
            break;
        }
        case MIROpTag.MIRBinKeyLess: {
            const bl = op as MIRBinKeyLess;
            bl.lhs = propagateAssign_Remap(bl.lhs, propMap);
            bl.rhs = propagateAssign_Remap(bl.rhs, propMap);
            break;
        }
        case MIROpTag.MIRPrefixNotOp: {
            const pfx = op as MIRPrefixNotOp;
            pfx.arg = propagateAssign_Remap(pfx.arg, propMap);
            break;
        }
        case MIROpTag.MIRAllTrue: {
            const at = op as MIRAllTrue;
            at.args = propagateAssign_RemapArgs(at.args, propMap);
            break;
        }
        case MIROpTag.MIRSomeTrue: {
            const at = op as MIRSomeTrue;
            at.args = propagateAssign_RemapArgs(at.args, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOf: {
            const it = op as MIRIsTypeOf;
            it.arg = propagateAssign_Remap(it.arg, propMap);
            it.guard = propagateAssign_RemapStatementGuard(it.guard, propMap);
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
            regop.guard = propagateAssign_RemapStatementGuard(regop.guard, propMap);
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

    const ks = op.getModVars();
    ks.forEach((kv) => propagateAssign_Kill(kv, propMap));

    switch (op.tag) {
        case MIROpTag.MIRLoadConst: {
            const lc = op as MIRLoadConst;
            propagateAssign_Bind(lc.trgt, lc.src, propMap);
            break;
        }
        case MIROpTag.MIRRegisterAssign: {
            const regop = op as MIRRegisterAssign;
            if(regop.guard === undefined) {
                propagateAssign_Bind(regop.trgt, regop.src, propMap);
            }
            break;
        }
        default: {
            break;
        }
    }
}

function propagateAssignForBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        let propMap = new Map<string, MIRArgument>();
        for (let i = 0; i < blk.ops.length; ++i) {
            propagateAssignForOp(blk.ops[i], propMap);
        }
    });
}

function computeTempUseForBody(body: MIRBody): Set<string> {
    if (typeof (body) === "string") {
        return new Set<string>();
    }

    let usedTemps = new Set<string>();
    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        for (let i = 0; i < blk.ops.length; ++i) {
            const optmps = blk.ops[i].getUsedVars().filter((arg) => arg instanceof MIRRegisterArgument);
            for (let j = 0; j < optmps.length; ++j) {
                usedTemps.add((optmps[j] as MIRRegisterArgument).nameID);
            }
        }
    });

    return usedTemps;
}

function removeSelfAssigns(body: MIRBody) {
    (body.body as Map<string, MIRBasicBlock>).forEach((blk, tag) => {
        const nblock = blk.ops.filter((op) => {
            if(op instanceof MIRRegisterAssign) {
                return op.trgt.nameID !== op.src.nameID;
            }
            else {
                return true;
            }
        });

        blk.ops = nblock;
    });
}

function isDeadTempAssign(op: MIROp, liveTemps: Set<string>): boolean {
    switch (op.tag) {
        case MIROpTag.MIRLoadConst:
        case MIROpTag.MIRRegisterAssign: {
            return op.getModVars().every((mv) => mv instanceof MIRRegisterArgument && mv.nameID.startsWith("#tmp") && !liveTemps.has(mv.nameID));
        }
        default:
            return false;
    }
}

function removeDeadTempAssignsFromBody(body: MIRBody) {
    let oldLiveSize = Number.MAX_SAFE_INTEGER;
    let liveTemps = computeTempUseForBody(body);
    while (liveTemps.size < oldLiveSize) {
        let nbody = new Map<string, MIRBasicBlock>();
        (body.body as Map<string, MIRBasicBlock>).forEach((blk, id) => {
            const ops = blk.ops.filter((op) => !isDeadTempAssign(op, liveTemps));
            nbody.set(id, new MIRBasicBlock(id, ops));
        });
        body.body = nbody;

        oldLiveSize = liveTemps.size;
        liveTemps = computeTempUseForBody(body);
    }
}

function simplifyBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    cleanDeadBlocks(body);
    propagateAssignForBody(body);
    removeSelfAssigns(body);
    removeDeadTempAssignsFromBody(body);
}

export { simplifyBody };
