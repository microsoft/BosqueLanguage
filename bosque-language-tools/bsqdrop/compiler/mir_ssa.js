"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const assert = require("assert");
const mir_ops_1 = require("./mir_ops");
const mir_info_1 = require("./mir_info");
//
//Convert MIR into SSA form
//
function convertToSSA(reg, remap, ctrs) {
    if (!ctrs.has(reg.nameID)) {
        ctrs.set(reg.nameID, 0);
        remap.set(reg.nameID, reg);
        return reg;
    }
    else {
        const ssaCtr = ctrs.get(reg.nameID) + 1;
        ctrs.set(reg.nameID, ssaCtr);
        const vname = reg.nameID + `$${ssaCtr}`;
        if (reg instanceof mir_ops_1.MIRTempRegister) {
            remap.set(reg.nameID, new mir_ops_1.MIRTempRegister(reg.regID, vname));
        }
        else {
            assert(reg instanceof mir_ops_1.MIRVariable);
            remap.set(reg.nameID, new mir_ops_1.MIRVariable(reg.nameID, vname));
        }
        return remap.get(reg.nameID);
    }
}
function processSSA_Use(arg, remap) {
    if (arg instanceof mir_ops_1.MIRRegisterArgument) {
        return remap.get(arg.nameID) || arg;
    }
    else {
        return arg;
    }
}
function processSSAUse_RemapArgs(args, remap) {
    return args.map((v) => processSSA_Use(v, remap));
}
function processSSAUse_RemapStructuredArgs(args, remap) {
    return args.map((v) => remap(v));
}
function processValueOpTempSSA(op, remap, ctrs) {
    op.trgt = convertToSSA(op.trgt, remap, ctrs);
}
function assignSSA(op, remap, ctrs) {
    switch (op.tag) {
        case mir_ops_1.MIROpTag.MIRLoadConst:
        case mir_ops_1.MIROpTag.MIRLoadConstRegex:
        case mir_ops_1.MIROpTag.MIRLoadConstSafeString:
        case mir_ops_1.MIROpTag.MIRLoadConstTypedString:
        case mir_ops_1.MIROpTag.MIRAccessConstantValue:
        case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
            processValueOpTempSSA(op, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessArgVariable: {
            processValueOpTempSSA(op, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
            const llv = op;
            llv.name = processSSA_Use(llv.name, remap);
            processValueOpTempSSA(llv, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckDirect: {
            const ic = op;
            ic.rcvr = processSSA_Use(ic.rcvr, remap);
            processValueOpTempSSA(ic, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
            const ic = op;
            ic.rcvr = processSSA_Use(ic.rcvr, remap);
            processValueOpTempSSA(ic, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
            const cp = op;
            cp.args = processSSAUse_RemapArgs(cp.args, remap);
            processValueOpTempSSA(cp, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            processValueOpTempSSA(op, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cc = op;
            cc.args = processSSAUse_RemapArgs(cc.args, remap);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cc = op;
            cc.args = processSSAUse_RemapArgs(cc.args, remap);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cc = op;
            cc.args = processSSAUse_RemapStructuredArgs(cc.args, (v) => [v[0], processSSA_Use(v[1], remap)]);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorTuple: {
            const tc = op;
            tc.args = processSSAUse_RemapArgs(tc.args, remap);
            processValueOpTempSSA(tc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorRecord: {
            const tc = op;
            tc.args = processSSAUse_RemapStructuredArgs(tc.args, (v) => [v[0], processSSA_Use(v[1], remap)]);
            processValueOpTempSSA(tc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorEphemeralValueList: {
            const elc = op;
            elc.args = processSSAUse_RemapArgs(elc.args, remap);
            processValueOpTempSSA(elc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
            const ai = op;
            ai.arg = processSSA_Use(ai.arg, remap);
            processValueOpTempSSA(ai, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
            const pi = op;
            pi.arg = processSSA_Use(pi.arg, remap);
            processValueOpTempSSA(pi, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
            const ap = op;
            ap.arg = processSSA_Use(ap.arg, remap);
            processValueOpTempSSA(ap, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
            const pi = op;
            pi.arg = processSSA_Use(pi.arg, remap);
            processValueOpTempSSA(pi, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromField: {
            const af = op;
            af.arg = processSSA_Use(af.arg, remap);
            processValueOpTempSSA(af, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromFields: {
            const pf = op;
            pf.arg = processSSA_Use(pf.arg, remap);
            processValueOpTempSSA(pf, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: {
            const pt = op;
            pt.arg = processSSA_Use(pt.arg, remap);
            processValueOpTempSSA(pt, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: {
            const pr = op;
            pr.arg = processSSA_Use(pr.arg, remap);
            processValueOpTempSSA(pr, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeNominal: {
            const pc = op;
            pc.arg = processSSA_Use(pc.arg, remap);
            processValueOpTempSSA(pc, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithIndecies: {
            const mi = op;
            mi.arg = processSSA_Use(mi.arg, remap);
            mi.updates = processSSAUse_RemapStructuredArgs(mi.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mi, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithProperties: {
            const mp = op;
            mp.arg = processSSA_Use(mp.arg, remap);
            mp.updates = processSSAUse_RemapStructuredArgs(mp.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mp, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithFields: {
            const mf = op;
            mf.arg = processSSA_Use(mf.arg, remap);
            mf.updates = processSSAUse_RemapStructuredArgs(mf.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mf, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: {
            const st = op;
            st.arg = processSSA_Use(st.arg, remap);
            st.update = processSSA_Use(st.update, remap);
            processValueOpTempSSA(st, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: {
            const sr = op;
            sr.arg = processSSA_Use(sr.arg, remap);
            sr.update = processSSA_Use(sr.update, remap);
            processValueOpTempSSA(sr, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendObject: {
            const so = op;
            so.arg = processSSA_Use(so.arg, remap);
            so.update = processSSA_Use(so.update, remap);
            processValueOpTempSSA(so, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadFromEpehmeralList: {
            const el = op;
            el.arg = processSSA_Use(el.arg, remap);
            processValueOpTempSSA(el, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
            const invk = op;
            invk.args = processSSAUse_RemapArgs(invk.args, remap);
            processValueOpTempSSA(invk, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
            const invk = op;
            invk.args = processSSAUse_RemapArgs(invk.args, remap);
            processValueOpTempSSA(invk, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPrefixOp: {
            const pfx = op;
            pfx.arg = processSSA_Use(pfx.arg, remap);
            processValueOpTempSSA(pfx, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinOp: {
            const bop = op;
            bop.lhs = processSSA_Use(bop.lhs, remap);
            bop.rhs = processSSA_Use(bop.rhs, remap);
            processValueOpTempSSA(bop, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinEq: {
            const beq = op;
            beq.lhs = processSSA_Use(beq.lhs, remap);
            beq.rhs = processSSA_Use(beq.rhs, remap);
            processValueOpTempSSA(beq, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinLess: {
            const bl = op;
            bl.lhs = processSSA_Use(bl.lhs, remap);
            bl.rhs = processSSA_Use(bl.rhs, remap);
            processValueOpTempSSA(bl, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinCmp: {
            const bcp = op;
            bcp.lhs = processSSA_Use(bcp.lhs, remap);
            bcp.rhs = processSSA_Use(bcp.rhs, remap);
            processValueOpTempSSA(bcp, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
            const ton = op;
            ton.arg = processSSA_Use(ton.arg, remap);
            processValueOpTempSSA(ton, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
            const tos = op;
            tos.arg = processSSA_Use(tos.arg, remap);
            processValueOpTempSSA(tos, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOf: {
            const tog = op;
            tog.arg = processSSA_Use(tog.arg, remap);
            processValueOpTempSSA(tog, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRRegAssign: {
            const regop = op;
            regop.src = processSSA_Use(regop.src, remap);
            regop.trgt = convertToSSA(regop.trgt, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRTruthyConvert: {
            const tcop = op;
            tcop.src = processSSA_Use(tcop.src, remap);
            tcop.trgt = convertToSSA(tcop.trgt, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRVarStore: {
            const vs = op;
            vs.src = processSSA_Use(vs.src, remap);
            vs.name = convertToSSA(vs.name, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackSlice: {
            const pso = op;
            pso.src = processSSA_Use(pso.src, remap);
            pso.trgt = convertToSSA(pso.trgt, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackExtend: {
            const pse = op;
            pse.basepack = processSSA_Use(pse.basepack, remap);
            pse.ext = processSSAUse_RemapArgs(pse.ext, remap);
            pse.trgt = convertToSSA(pse.trgt, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRReturnAssign: {
            const ra = op;
            ra.src = processSSA_Use(ra.src, remap);
            ra.name = convertToSSA(ra.name, remap, ctrs);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAbort: {
            break;
        }
        case mir_ops_1.MIROpTag.MIRDebug: {
            const dbg = op;
            if (dbg.value !== undefined) {
                dbg.value = processSSA_Use(dbg.value, remap);
            }
            break;
        }
        case mir_ops_1.MIROpTag.MIRJump: {
            break;
        }
        case mir_ops_1.MIROpTag.MIRJumpCond: {
            const cjop = op;
            cjop.arg = processSSA_Use(cjop.arg, remap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRJumpNone: {
            const njop = op;
            njop.arg = processSSA_Use(njop.arg, remap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRVarLifetimeStart:
        case mir_ops_1.MIROpTag.MIRVarLifetimeEnd: {
            break;
        }
        default:
            assert(false);
            break;
    }
}
function generatePhi(sinfo, lv, opts, ctrs) {
    let vassign = new Map();
    opts.forEach((e) => vassign.set(e[0], e[1]));
    const ssaCtr = ctrs.get(lv) + 1;
    ctrs.set(lv, ssaCtr);
    const vname = lv + `$${ssaCtr}`;
    if (lv.startsWith("#tmp_")) {
        return new mir_ops_1.MIRPhi(sinfo, vassign, new mir_ops_1.MIRTempRegister(Number.parseInt(lv.substr(5)), vname));
    }
    else {
        return new mir_ops_1.MIRPhi(sinfo, vassign, new mir_ops_1.MIRVariable(lv, vname));
    }
}
function computePhis(sinfo, block, ctrs, remapped, links, live) {
    let remap = new Map();
    let phis = [];
    live.get(block).liveEntry.forEach((v, n) => {
        const preds = links.get(block).preds;
        let phiOpts = [];
        let uniqueOpts = new Map();
        preds.forEach((pred) => {
            const pm = remapped.get(pred);
            const mreg = pm.get(n);
            uniqueOpts.set(mreg.nameID, mreg);
            phiOpts.push([pred, mreg]);
        });
        if (uniqueOpts.size === 1) {
            const rmp = [...uniqueOpts][0][1];
            remap.set(n, rmp);
        }
        else {
            const phi = generatePhi(sinfo, n, phiOpts, ctrs);
            phis.push(phi);
            remap.set(n, phi.trgt);
        }
    });
    return [phis, remap];
}
function convertBodyToSSA(body, args) {
    const blocks = body.body;
    const links = mir_info_1.computeBlockLinks(blocks);
    const live = mir_info_1.computeBlockLiveVars(blocks);
    const torder = mir_info_1.topologicalOrder(blocks);
    let remapped = new Map();
    let ctrs = new Map();
    for (let j = 0; j < torder.length; ++j) {
        const block = torder[j];
        if (block.label === "entry") {
            let remap = new Map();
            args.forEach((arg, name) => remap.set(name, new mir_ops_1.MIRVariable(name)));
            remap.set("$__ir_ret__", new mir_ops_1.MIRVariable("$__ir_ret__"));
            remap.set("$$return", new mir_ops_1.MIRVariable("$$return"));
            for (let i = 0; i < block.ops.length; ++i) {
                assignSSA(block.ops[i], remap, ctrs);
            }
            remapped.set(block.label, remap);
        }
        else {
            const [phis, remap] = computePhis(body.sinfo, block.label, ctrs, remapped, links, live);
            for (let i = 0; i < block.ops.length; ++i) {
                assignSSA(block.ops[i], remap, ctrs);
            }
            block.ops.unshift(...phis);
            remapped.set(block.label, remap);
        }
    }
}
exports.convertBodyToSSA = convertBodyToSSA;
//# sourceMappingURL=mir_ssa.js.map