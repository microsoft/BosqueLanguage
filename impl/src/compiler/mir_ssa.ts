//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRArgGuard, MIRArgument, MIRAssertCheck, MIRConvertValue, MIRDebug, MIREntityProjectToEphemeral, MIREntityUpdate, MIRGuard, MIRLoadConst, MIRLoadField, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIROp, MIROpTag, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRResolvedTypeKey, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionEmpty, MIREphemeralListExtend, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRBinKeyEq, MIRBinKeyLess, MIRPrefixNotOp, MIRAllTrue, MIRIsTypeOf, MIRJumpCond, MIRJumpNone, MIRReturnAssign, MIRReturnAssignOfCons, MIRPhi, MIRBody, MIRBasicBlock, MIRStatmentGuard, MIRRegisterAssign, MIRSomeTrue } from "./mir_ops";
import { SourceInfo } from "../ast/parser";
import { FlowLink, BlockLiveSet, computeBlockLinks, computeBlockLiveVars, topologicalOrder } from "./mir_info";
import { MIRAssembly, MIRType } from "./mir_assembly";

type SSAState = {
    booltype: MIRResolvedTypeKey,

    remap: Map<string, MIRRegisterArgument>,
    ctrs: Map<string, number>,
    vartypes: Map<string, MIRResolvedTypeKey>
};

function convertToSSA(reg: MIRRegisterArgument, oftype: MIRResolvedTypeKey, ssastate: SSAState): MIRRegisterArgument {
    if (!ssastate.ctrs.has(reg.nameID)) {
        ssastate.ctrs.set(reg.nameID, 0);
        ssastate.remap.set(reg.nameID, reg);
        ssastate.vartypes.set(reg.nameID, oftype);

        return reg;
    }
    else {
        const ssaCtr = ssastate.ctrs.get(reg.nameID) as number + 1;
        ssastate.ctrs.set(reg.nameID, ssaCtr);

        const vname = reg.nameID + `$${ssaCtr}`;
        ssastate.remap.set(reg.nameID, new MIRRegisterArgument(vname, reg.nameID));

        ssastate.vartypes.set(vname, oftype);

        return ssastate.remap.get(reg.nameID) as MIRRegisterArgument;
    }
}

function convertToSSA_Guard(guard: MIRGuard, ssastate: SSAState): MIRGuard {
    if(guard instanceof MIRMaskGuard) {
        return guard;
    }
    else {
        const vg = guard as MIRArgGuard;
        if(vg.greg instanceof MIRRegisterArgument) {
            return new MIRArgGuard(convertToSSA(vg.greg as MIRRegisterArgument, ssastate.booltype, ssastate));
        }
        else {
            return vg;
        }
    }
}

function processSSA_Use(arg: MIRArgument, ssastate: SSAState): MIRArgument {
    if (arg instanceof MIRRegisterArgument) {
        return ssastate.remap.get(arg.nameID) || arg;
    }
    else {
        return arg;
    }
}

function processSSAUse_RemapGuard(guard: MIRGuard | undefined, ssastate: SSAState): MIRGuard | undefined {
    if(guard === undefined) {
        return undefined;
    }
    else if(guard instanceof MIRMaskGuard) {
        return guard;
    }
    else {
        return new MIRArgGuard(processSSA_Use((guard as MIRArgGuard).greg, ssastate));
    }
}

function processSSAUse_RemapStatementGuard(sguard: MIRStatmentGuard | undefined, ssastate: SSAState): MIRStatmentGuard | undefined {
    if(sguard === undefined) {
        return undefined;
    }
    else {
        const rguard = processSSAUse_RemapGuard(sguard.guard, ssastate) as MIRGuard;
        const ralt = sguard.altvalue !== undefined ? processSSA_Use(sguard.altvalue, ssastate) : undefined;

        return new MIRStatmentGuard(rguard, ralt);
    }
}

function processSSAUse_RemapArgs(args: MIRArgument[], ssastate: SSAState): MIRArgument[] {
    return args.map((v) => processSSA_Use(v, ssastate));
}

function processSSAUse_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function assignSSA(op: MIROp, ssastate: SSAState): MIROp {
    switch (op.tag) {
        case MIROpTag.MIRNop: 
        case MIROpTag.MIRDeadFlow:
        case MIROpTag.MIRAbort:
        case MIROpTag.MIRDeclareGuardFlagLocation: 
        case MIROpTag.MIRSetConstantGuardFlag:
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            return op;
        }
        case MIROpTag.MIRAssertCheck: {
            const asrt = op as MIRAssertCheck;
            asrt.arg = processSSA_Use(asrt.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = processSSA_Use(dbg.value, ssastate);
            }
            return op;
        }
        case MIROpTag.MIRLoadUnintVariableValue: {
            const luv = op as MIRLoadUnintVariableValue;
            luv.trgt = convertToSSA(luv.trgt, luv.oftype, ssastate);
            return op;
        }
        case MIROpTag.MIRConvertValue: {
            const conv = op as MIRConvertValue;
            conv.src = processSSA_Use(conv.src, ssastate);
            conv.guard = processSSAUse_RemapStatementGuard(conv.guard, ssastate);
            conv.trgt = convertToSSA(conv.trgt, conv.intotype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadConst: {
            const lc = op as MIRLoadConst;
            lc.trgt = convertToSSA(lc.trgt, lc.consttype, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleHasIndex: {
            const thi = op as MIRTupleHasIndex;
            thi.arg = processSSA_Use(thi.arg, ssastate);
            thi.trgt = convertToSSA(thi.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordHasProperty: {
            const rhi = op as MIRRecordHasProperty;
            rhi.arg = processSSA_Use(rhi.arg, ssastate);
            rhi.trgt = convertToSSA(rhi.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadTupleIndex: {
            const lti = op as MIRLoadTupleIndex;
            lti.arg = processSSA_Use(lti.arg, ssastate);
            lti.trgt = convertToSSA(lti.trgt, lti.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadTupleIndexSetGuard: {
            const ltig = op as MIRLoadTupleIndexSetGuard;
            ltig.arg = processSSA_Use(ltig.arg, ssastate);
            ltig.guard = convertToSSA_Guard(ltig.guard, ssastate);
            ltig.trgt = convertToSSA(ltig.trgt, ltig.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadRecordProperty: {
            const lrp = op as MIRLoadRecordProperty;
            lrp.arg = processSSA_Use(lrp.arg, ssastate);
            lrp.trgt = convertToSSA(lrp.trgt, lrp.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadRecordPropertySetGuard: {
            const lrpg = op as MIRLoadRecordPropertySetGuard;
            lrpg.arg = processSSA_Use(lrpg.arg, ssastate);
            lrpg.guard = convertToSSA_Guard(lrpg.guard, ssastate);
            lrpg.trgt = convertToSSA(lrpg.trgt, lrpg.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadField: {
            const lmf = op as MIRLoadField;
            lmf.arg = processSSA_Use(lmf.arg, ssastate);
            lmf.trgt = convertToSSA(lmf.trgt, lmf.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleProjectToEphemeral: {
            const pte = op as MIRTupleProjectToEphemeral;
            pte.arg = processSSA_Use(pte.arg, ssastate);
            pte.trgt = convertToSSA(pte.trgt, pte.epht, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordProjectToEphemeral: {
            const pre = op as MIRRecordProjectToEphemeral;
            pre.arg = processSSA_Use(pre.arg, ssastate);
            pre.trgt = convertToSSA(pre.trgt, pre.epht, ssastate);
            return op;
        }
        case MIROpTag.MIREntityProjectToEphemeral: {
            const pee = op as MIREntityProjectToEphemeral;
            pee.arg = processSSA_Use(pee.arg, ssastate);
            pee.trgt = convertToSSA(pee.trgt, pee.epht, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleUpdate: {
            const mi = op as MIRTupleUpdate;
            mi.arg = processSSA_Use(mi.arg, ssastate);
            mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument, MIRResolvedTypeKey]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mi.trgt = convertToSSA(mi.trgt, mi.argflowtype, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordUpdate: {
            const mp = op as MIRRecordUpdate;
            mp.arg = processSSA_Use(mp.arg, ssastate);
            mp.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mp.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mp.trgt = convertToSSA(mp.trgt, mp.argflowtype, ssastate);
            return op;
        }
        case MIROpTag.MIREntityUpdate: {
            const mf = op as MIREntityUpdate;
            mf.arg = processSSA_Use(mf.arg, ssastate);
            mf.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mf.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mf.trgt = convertToSSA(mf.trgt, mf.argflowtype, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadFromEpehmeralList: {
            const mle = op as MIRLoadFromEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgt = convertToSSA(mle.trgt, mle.resulttype, ssastate);
            return op;
        }
        case MIROpTag.MIRMultiLoadFromEpehmeralList: {
            const mle = op as MIRMultiLoadFromEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgts.forEach((trgt) => {
                trgt.into = convertToSSA(trgt.into, trgt.oftype, ssastate);
            });
            return op;
        }
        case MIROpTag.MIRSliceEpehmeralList: {
            const mle = op as MIRSliceEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgt = convertToSSA(mle.trgt, mle.sltype, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeFixedFunction: {
            const invk = op as MIRInvokeFixedFunction;
            invk.args = processSSAUse_RemapArgs(invk.args, ssastate);
            invk.guard = processSSAUse_RemapStatementGuard(invk.guard, ssastate);
            invk.trgt = convertToSSA(invk.trgt, invk.resultType, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeVirtualFunction: {
            const invk = op as MIRInvokeVirtualFunction;
            invk.args = processSSAUse_RemapArgs(invk.args, ssastate);
            invk.trgt = convertToSSA(invk.trgt, invk.resultType, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeVirtualOperator: {
            const invk = op as MIRInvokeVirtualOperator;
            invk.args = processSSAUse_RemapStructuredArgs<{ arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }>(invk.args, (u) => {
                return { arglayouttype: u.arglayouttype, argflowtype: u.argflowtype, arg: processSSA_Use(u.arg, ssastate) };
            });
            invk.trgt = convertToSSA(invk.trgt, invk.resultType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            tc.args = processSSAUse_RemapArgs(tc.args, ssastate);
            tc.trgt = convertToSSA(tc.trgt, tc.resultTupleType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorTupleFromEphemeralList: {
            const tc = op as MIRConstructorTupleFromEphemeralList;
            tc.arg = processSSA_Use(tc.arg, ssastate);
            tc.trgt = convertToSSA(tc.trgt, tc.resultTupleType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorRecord: {
            const tc = op as MIRConstructorRecord;
            tc.args = processSSAUse_RemapStructuredArgs<[string, MIRArgument]>(tc.args, (v) => [v[0], processSSA_Use(v[1], ssastate)]);
            tc.trgt = convertToSSA(tc.trgt, tc.resultRecordType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorRecordFromEphemeralList: {
            const tc = op as MIRConstructorRecordFromEphemeralList;
            tc.arg = processSSA_Use(tc.arg, ssastate);
            tc.trgt = convertToSSA(tc.trgt, tc.resultRecordType, ssastate);
            return op;
        }
        case MIROpTag.MIRStructuredAppendTuple: {
            const at = op as MIRStructuredAppendTuple;
            at.args = processSSAUse_RemapArgs(at.args, ssastate);
            at.trgt = convertToSSA(at.trgt, at.resultTupleType, ssastate);
            return op;
        }
        case MIROpTag.MIRStructuredJoinRecord: {
            const sj = op as MIRStructuredJoinRecord;
            sj.args = processSSAUse_RemapArgs(sj.args, ssastate);
            sj.trgt = convertToSSA(sj.trgt, sj.resultRecordType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorEphemeralList: {
            const tc = op as MIRConstructorEphemeralList;
            tc.args = processSSAUse_RemapArgs(tc.args, ssastate);
            tc.trgt = convertToSSA(tc.trgt, tc.resultEphemeralListType, ssastate);
            return op;
        }
        case MIROpTag.MIREphemeralListExtend: {
            const pse = op as MIREphemeralListExtend;
            pse.arg = processSSA_Use(pse.arg, ssastate);
            pse.ext = processSSAUse_RemapArgs(pse.ext, ssastate);
            pse.trgt = convertToSSA(pse.trgt, pse.resultType, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            const cc = op as MIRConstructorPrimaryCollectionEmpty;
            cc.trgt = convertToSSA(cc.trgt, cc.tkey, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cc = op as MIRConstructorPrimaryCollectionSingletons;
            cc.args = processSSAUse_RemapStructuredArgs<[MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], processSSA_Use(v[1], ssastate)]);
            cc.trgt = convertToSSA(cc.trgt, cc.tkey, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cc = op as MIRConstructorPrimaryCollectionCopies;
            cc.args = processSSAUse_RemapStructuredArgs<[MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], processSSA_Use(v[1], ssastate)]);
            cc.trgt = convertToSSA(cc.trgt, cc.tkey, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cc = op as MIRConstructorPrimaryCollectionMixed;
            cc.args = processSSAUse_RemapStructuredArgs<[boolean, MIRResolvedTypeKey, MIRArgument]>(cc.args, (v) => [v[0], v[1], processSSA_Use(v[2], ssastate)]);
            cc.trgt = convertToSSA(cc.trgt, cc.tkey, ssastate);
            return op;
        }
        case MIROpTag.MIRBinKeyEq: {
            const beq = op as MIRBinKeyEq;
            beq.lhs = processSSA_Use(beq.lhs, ssastate);
            beq.rhs = processSSA_Use(beq.rhs, ssastate);
            beq.trgt = convertToSSA(beq.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRBinKeyLess: {
            const bl = op as MIRBinKeyLess;
            bl.lhs = processSSA_Use(bl.lhs, ssastate);
            bl.rhs = processSSA_Use(bl.rhs, ssastate);
            bl.trgt = convertToSSA(bl.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRPrefixNotOp: {
            const pfx = op as MIRPrefixNotOp;
            pfx.arg = processSSA_Use(pfx.arg, ssastate);
            pfx.trgt = convertToSSA(pfx.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRAllTrue: {
            const at = op as MIRAllTrue;
            at.args = processSSAUse_RemapArgs(at.args, ssastate);
            at.trgt = convertToSSA(at.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRSomeTrue: {
            const at = op as MIRSomeTrue;
            at.args = processSSAUse_RemapArgs(at.args, ssastate);
            at.trgt = convertToSSA(at.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRIsTypeOf: {
            const it = op as MIRIsTypeOf;
            it.arg = processSSA_Use(it.arg, ssastate);
            it.guard = processSSAUse_RemapStatementGuard(it.guard, ssastate);
            it.trgt = convertToSSA(it.trgt, ssastate.booltype, ssastate);
            return op;
        }
        case MIROpTag.MIRJump: {
            return op;
        }
        case MIROpTag.MIRJumpCond: {
            const cjop = op as MIRJumpCond;
            cjop.arg = processSSA_Use(cjop.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRJumpNone: {
            const njop = op as MIRJumpNone;
            njop.arg = processSSA_Use(njop.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRRegisterAssign: {
            const regop = op as MIRRegisterAssign;
            regop.src = processSSA_Use(regop.src, ssastate);
            regop.guard = processSSAUse_RemapStatementGuard(regop.guard, ssastate);
            regop.trgt = convertToSSA(regop.trgt, regop.layouttype, ssastate);
            return op;
        }
        case MIROpTag.MIRReturnAssign: {
            const ra = op as MIRReturnAssign;
            ra.src = processSSA_Use(ra.src, ssastate);
            ra.name = convertToSSA(ra.name, ra.oftype, ssastate);
            return op;
        }
        case MIROpTag.MIRReturnAssignOfCons: {
            const ra = op as MIRReturnAssignOfCons;
            ra.args = processSSAUse_RemapArgs(ra.args, ssastate);
            ra.name = convertToSSA(ra.name, ra.oftype, ssastate);
            return op;
        }
        case MIROpTag.MIRPhi: {
           assert(false);
           return op;
        }
        default: {
            assert(false);
            return op;
        }
    }
}

function generatePhi(sinfo: SourceInfo, lv: MIRRegisterArgument, opts: [string, MIRRegisterArgument][], ssastate: SSAState): MIRPhi {
    let vassign = new Map<string, MIRRegisterArgument>();
    opts.forEach((e) => vassign.set(e[0], e[1]));

    const ptype = ssastate.vartypes.get(opts[0][1].nameID) as MIRResolvedTypeKey;
    assert(opts.every((opt) => (ssastate.vartypes.get(opt[1].nameID) as MIRResolvedTypeKey) === ptype));

    const nlv = convertToSSA(lv, ptype, ssastate);
    return new MIRPhi(sinfo, vassign, ptype, nlv);
}

function computePhis(sinfo: SourceInfo, block: string, ssastate: SSAState, remapped: Map<string, Map<string, MIRRegisterArgument>>, links: Map<string, FlowLink>, live: Map<string, BlockLiveSet>): [MIRPhi[], Map<string, MIRRegisterArgument>] {
    let remap = new Map<string, MIRRegisterArgument>();
    let phis: MIRPhi[] = [];

    (live.get(block) as BlockLiveSet).liveEntry.forEach((v, n) => {
        const preds = (links.get(block) as FlowLink).preds;

        let phiOpts: [string, MIRRegisterArgument][] = [];
        let uniqueOpts = new Map<string, MIRRegisterArgument>();
        preds.forEach((pred) => {
            const pm = remapped.get(pred) as Map<string, MIRRegisterArgument>;
            const mreg = pm.get(n) as MIRRegisterArgument;
            uniqueOpts.set(mreg.nameID, mreg);
            phiOpts.push([pred, mreg]);
        });

        if (uniqueOpts.size === 1) {
            const rmp = [...uniqueOpts][0][1];
            remap.set(n, rmp);
        }
        else {
            const phi = generatePhi(sinfo, v, phiOpts, ssastate);

            phis.push(phi);
            remap.set(n, phi.trgt);
        }
    });

    return [phis, remap];
}

function convertBodyToSSA(body: MIRBody, booltype: MIRType, args: Map<string, MIRType>) {
    const blocks = body.body as Map<string, MIRBasicBlock>;
    const links = computeBlockLinks(blocks);
    const live = computeBlockLiveVars(blocks);
    const torder = topologicalOrder(blocks);

    let remapped = new Map<string, Map<string, MIRRegisterArgument>>();
    let ssastate = {
        booltype: booltype.trkey,
        
        remap: new Map<string, MIRRegisterArgument>(),
        ctrs: new Map<string, number>(),
        vartypes: new Map<string, MIRResolvedTypeKey>()
    };

    for (let j = 0; j < torder.length; ++j) {
        const block = torder[j];

        if (block.label === "entry") {
            args.forEach((arg, name) => ssastate.remap.set(name, new MIRRegisterArgument(name)));
            ssastate.remap.set("$__ir_ret__", new MIRRegisterArgument("$__ir_ret__"));
            ssastate.remap.set("$$return", new MIRRegisterArgument("$$return"));

            for (let i = 0; i < block.ops.length; ++i) {
                block.ops[i] = assignSSA(block.ops[i], ssastate);
            }

            remapped.set(block.label, ssastate.remap);
        }
        else {
            const [phis, remap] = computePhis(body.sinfo, block.label, ssastate, remapped, links, live);
            ssastate.remap = remap;

            for (let i = 0; i < block.ops.length; ++i) {
                assignSSA(block.ops[i], ssastate);
            }

            block.ops.unshift(...phis);
            remapped.set(block.label, ssastate.remap);
        }
    }
}

function ssaConvertInvokes(masm: MIRAssembly) {
    masm.invokeDecls.forEach((inv) => {
        let args = new Map<string, MIRType>();
        inv.params.forEach((p) => {
            args.set(p.name, masm.typeMap.get(p.type) as MIRType);
        });
        
        convertBodyToSSA(inv.body, masm.typeMap.get("NSCore::Bool") as MIRType, args);
    });
}

export { ssaConvertInvokes };
