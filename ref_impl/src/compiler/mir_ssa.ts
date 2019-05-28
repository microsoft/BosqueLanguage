//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRBody, MIRRegisterArgument, MIRBasicBlock, MIROpTag, MIRJumpNone, MIRJumpCond, MIROp, MIRValueOp, MIRTempRegister, MIRAccessCapturedVariable, MIRAccessArgVariable, MIRArgument, MIRVarLocal, MIRAccessLocalVariable, MIRConstructorPrimary, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord, MIRConstructorLambda, MIRCallNamespaceFunction, MIRCallStaticFunction, MIRProjectFromFields, MIRAccessFromField, MIRProjectFromProperties, MIRAccessFromProperty, MIRProjectFromIndecies, MIRAccessFromIndex, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeKnownTarget, MIRInvokeVirtualTarget, MIRCallLambda, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRRegAssign, MIRTruthyConvert, MIRVarStore, MIRReturnAssign, MIRDebug, MIRPhi, MIRVarParameter, MIRVarCaptured, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf, MIRLogicStore } from "./mir_ops";
import { SourceInfo } from "../ast/parser";
import { FlowLink, BlockLiveSet, computeBlockLinks, computeBlockLiveVars, topologicalOrder } from "./mir_info";

//
//Convert MIR into SSA form
//

function convertToSSA(reg: MIRRegisterArgument, remap: Map<string, MIRRegisterArgument>, ctrs: Map<string, number>): MIRRegisterArgument {
    if (!ctrs.has(reg.nameID)) {
        ctrs.set(reg.nameID, 0);
        remap.set(reg.nameID, reg);

        return reg;
    }
    else {
        const ssaCtr = ctrs.get(reg.nameID) as number + 1;
        ctrs.set(reg.nameID, ssaCtr);

        const vname = reg.nameID + `$${ssaCtr}`;

        if (reg instanceof MIRTempRegister) {
            remap.set(reg.nameID, new MIRTempRegister(reg.regID, vname));
        }
        else {
            assert(reg instanceof MIRVarLocal);
            remap.set(reg.nameID, new MIRVarLocal(reg.nameID, vname));
        }

        return remap.get(reg.nameID) as MIRRegisterArgument;
    }
}

function processSSA_Use(arg: MIRArgument, remap: Map<string, MIRRegisterArgument>) {
    if (arg instanceof MIRRegisterArgument) {
        return remap.get(arg.nameID) || arg;
    }
    else {
        return arg;
    }
}

function processSSAUse_RemapArgs(args: MIRArgument[], remap: Map<string, MIRRegisterArgument>): MIRArgument[] {
    return args.map((v) => processSSA_Use(v, remap));
}

function processSSAUse_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function processValueOpTempSSA(op: MIRValueOp, remap: Map<string, MIRRegisterArgument>, ctrs: Map<string, number>) {
    op.trgt = convertToSSA(op.trgt, remap, ctrs) as MIRTempRegister;
}

function assignSSA(op: MIROp, remap: Map<string, MIRRegisterArgument>, ctrs: Map<string, number>) {
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            processValueOpTempSSA(op as MIRValueOp, remap, ctrs);
            break;
        }
        case MIROpTag.AccessCapturedVariable: {
            processValueOpTempSSA(op as MIRAccessCapturedVariable, remap, ctrs);
            break;
        }
        case MIROpTag.AccessArgVariable: {
            processValueOpTempSSA(op as MIRAccessArgVariable, remap, ctrs);
            break;
        }
        case MIROpTag.AccessLocalVariable: {
            const llv = op as MIRAccessLocalVariable;
            llv.name = processSSA_Use(llv.name, remap) as MIRVarLocal;
            processValueOpTempSSA(llv, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorPrimary: {
            const cp = op as MIRConstructorPrimary;
            cp.args = processSSAUse_RemapArgs(cp.args, remap);
            processValueOpTempSSA(cp, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            processValueOpTempSSA(op as MIRConstructorPrimaryCollectionEmpty, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            const cc = op as MIRConstructorPrimaryCollectionSingletons;
            cc.args = processSSAUse_RemapArgs(cc.args, remap);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            const cc = op as MIRConstructorPrimaryCollectionCopies;
            cc.args = processSSAUse_RemapArgs(cc.args, remap);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            const cc = op as MIRConstructorPrimaryCollectionMixed;
            cc.args = processSSAUse_RemapStructuredArgs(cc.args, (v) => [v[0], processSSA_Use(v[1], remap)] as [boolean, MIRArgument]);
            processValueOpTempSSA(cc, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            tc.args = processSSAUse_RemapArgs(tc.args, remap);
            processValueOpTempSSA(tc, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorRecord: {
            const tc = op as MIRConstructorRecord;
            tc.args = processSSAUse_RemapStructuredArgs(tc.args, (v) => [v[0], processSSA_Use(v[1], remap)] as [string, MIRArgument]);
            processValueOpTempSSA(tc, remap, ctrs);
            break;
        }
        case MIROpTag.ConstructorLambda: {
            const lc = op as MIRConstructorLambda;
            let ncaptured = new Map<string, MIRRegisterArgument>();
            lc.captured.forEach((v, k) => ncaptured.set(k, processSSA_Use(v, remap)));
            lc.captured = ncaptured;
            processValueOpTempSSA(lc, remap, ctrs);
            break;
        }
        case MIROpTag.CallNamespaceFunction: {
            const fc = op as MIRCallNamespaceFunction;
            fc.args = processSSAUse_RemapArgs(fc.args, remap);
            processValueOpTempSSA(fc, remap, ctrs);
            break;
        }
        case MIROpTag.CallStaticFunction: {
            const fc = op as MIRCallStaticFunction;
            fc.args = processSSAUse_RemapArgs(fc.args, remap);
            processValueOpTempSSA(fc, remap, ctrs);
            break;
        }
        case MIROpTag.MIRAccessFromIndex: {
            const ai = op as MIRAccessFromIndex;
            ai.arg = processSSA_Use(ai.arg, remap);
            processValueOpTempSSA(ai, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            const pi = op as MIRProjectFromIndecies;
            pi.arg = processSSA_Use(pi.arg, remap);
            processValueOpTempSSA(pi, remap, ctrs);
            break;
        }
        case MIROpTag.MIRAccessFromProperty: {
            const ap = op as MIRAccessFromProperty;
            ap.arg = processSSA_Use(ap.arg, remap);
            processValueOpTempSSA(ap, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromProperties: {
            const pi = op as MIRProjectFromProperties;
            pi.arg = processSSA_Use(pi.arg, remap);
            processValueOpTempSSA(pi, remap, ctrs);
            break;
        }
        case MIROpTag.MIRAccessFromField: {
            const af = op as MIRAccessFromField;
            af.arg = processSSA_Use(af.arg, remap);
            processValueOpTempSSA(af, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromFields: {
            const pf = op as MIRProjectFromFields;
            pf.arg = processSSA_Use(pf.arg, remap);
            processValueOpTempSSA(pf, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            const pt = op as MIRProjectFromTypeTuple;
            pt.arg = processSSA_Use(pt.arg, remap);
            processValueOpTempSSA(pt, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            const pr = op as MIRProjectFromTypeRecord;
            pr.arg = processSSA_Use(pr.arg, remap);
            processValueOpTempSSA(pr, remap, ctrs);
            break;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            const pc = op as MIRProjectFromTypeConcept;
            pc.arg = processSSA_Use(pc.arg, remap);
            processValueOpTempSSA(pc, remap, ctrs);
            break;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            const mi = op as MIRModifyWithIndecies;
            mi.arg = processSSA_Use(mi.arg, remap);
            mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mi, remap, ctrs);
            break;
        }
        case MIROpTag.MIRModifyWithProperties: {
            const mp = op as MIRModifyWithProperties;
            mp.arg = processSSA_Use(mp.arg, remap);
            mp.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument]>(mp.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mp, remap, ctrs);
            break;
        }
        case MIROpTag.MIRModifyWithFields: {
            const mf = op as MIRModifyWithFields;
            mf.arg = processSSA_Use(mf.arg, remap);
            mf.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument]>(mf.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
            processValueOpTempSSA(mf, remap, ctrs);
            break;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            const st = op as MIRStructuredExtendTuple;
            st.arg = processSSA_Use(st.arg, remap);
            st.update = processSSA_Use(st.update, remap);
            processValueOpTempSSA(st, remap, ctrs);
            break;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            const sr = op as MIRStructuredExtendRecord;
            sr.arg = processSSA_Use(sr.arg, remap);
            sr.update = processSSA_Use(sr.update, remap);
            processValueOpTempSSA(sr, remap, ctrs);
            break;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            const so = op as MIRStructuredExtendObject;
            so.arg = processSSA_Use(so.arg, remap);
            so.update = processSSA_Use(so.update, remap);
            processValueOpTempSSA(so, remap, ctrs);
            break;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            const invk = op as MIRInvokeKnownTarget;
            invk.args = processSSAUse_RemapArgs(invk.args, remap);
            processValueOpTempSSA(invk, remap, ctrs);
            break;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            const invk = op as MIRInvokeVirtualTarget;
            invk.args = processSSAUse_RemapArgs(invk.args, remap);
            processValueOpTempSSA(invk, remap, ctrs);
            break;
        }
        case MIROpTag.MIRCallLambda: {
            const cl = op as MIRCallLambda;
            cl.lambda = processSSA_Use(cl.lambda, remap);
            cl.args = processSSAUse_RemapArgs(cl.args, remap);
            processValueOpTempSSA(cl, remap, ctrs);
            break;
        }
        case MIROpTag.MIRPrefixOp: {
            const pfx = op as MIRPrefixOp;
            pfx.arg = processSSA_Use(pfx.arg, remap);
            processValueOpTempSSA(pfx, remap, ctrs);
            break;
        }
        case MIROpTag.MIRBinOp: {
            const bop = op as MIRBinOp;
            bop.lhs = processSSA_Use(bop.lhs, remap);
            bop.rhs = processSSA_Use(bop.rhs, remap);
            processValueOpTempSSA(bop, remap, ctrs);
            break;
        }
        case MIROpTag.MIRBinEq: {
            const beq = op as MIRBinEq;
            beq.lhs = processSSA_Use(beq.lhs, remap);
            beq.rhs = processSSA_Use(beq.rhs, remap);
            processValueOpTempSSA(beq, remap, ctrs);
            break;
        }
        case MIROpTag.MIRBinCmp: {
            const bcp = op as MIRBinCmp;
            bcp.lhs = processSSA_Use(bcp.lhs, remap);
            bcp.rhs = processSSA_Use(bcp.rhs, remap);
            processValueOpTempSSA(bcp, remap, ctrs);
            break;
        }
        case MIROpTag.MIRIsTypeOfNone: {
            const ton = op as MIRIsTypeOfNone;
            ton.arg = processSSA_Use(ton.arg, remap);
            processValueOpTempSSA(ton, remap, ctrs);
            break;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            const tos = op as MIRIsTypeOfSome;
            tos.arg = processSSA_Use(tos.arg, remap);
            processValueOpTempSSA(tos, remap, ctrs);
            break;
        }
        case MIROpTag.MIRIsTypeOf: {
            const tog = op as MIRIsTypeOf;
            tog.arg = processSSA_Use(tog.arg, remap);
            processValueOpTempSSA(tog, remap, ctrs);
            break;
        }
        case MIROpTag.MIRRegAssign: {
            const regop = op as MIRRegAssign;
            regop.src = processSSA_Use(regop.src, remap);
            regop.trgt = convertToSSA(regop.trgt, remap, ctrs) as MIRTempRegister;
            break;
        }
        case MIROpTag.MIRTruthyConvert: {
            const tcop = op as MIRTruthyConvert;
            tcop.src = processSSA_Use(tcop.src, remap);
            tcop.trgt = convertToSSA(tcop.trgt, remap, ctrs) as MIRTempRegister;
            break;
        }
        case MIROpTag.MIRLogicStore: {
            const llop = op as MIRLogicStore;
            llop.lhs = processSSA_Use(llop.lhs, remap);
            llop.rhs = processSSA_Use(llop.rhs, remap);
            llop.trgt = convertToSSA(llop.trgt, remap, ctrs) as MIRTempRegister;
            break;
        }
        case MIROpTag.MIRVarStore: {
            const vs = op as MIRVarStore;
            vs.src = processSSA_Use(vs.src, remap);
            vs.name = convertToSSA(vs.name, remap, ctrs) as MIRVarLocal;
            break;
        }
        case MIROpTag.MIRReturnAssign: {
            const ra = op as MIRReturnAssign;
            ra.src = processSSA_Use(ra.src, remap);
            ra.name = convertToSSA(ra.name, remap, ctrs) as MIRVarLocal;
            break;
        }
        case MIROpTag.MIRAbort: {
            break;
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = processSSA_Use(dbg.value, remap);
            }
            break;
        }
        case MIROpTag.MIRJump: {
            break;
        }
        case MIROpTag.MIRJumpCond: {
            const cjop = op as MIRJumpCond;
            cjop.arg = processSSA_Use(cjop.arg, remap);
            break;
        }
        case MIROpTag.MIRJumpNone: {
            const njop = op as MIRJumpNone;
            njop.arg = processSSA_Use(njop.arg, remap);
            break;
        }
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            break;
        }
        default:
            assert(false);
            break;
    }
}

function generatePhi(sinfo: SourceInfo, lv: string, opts: [string, MIRRegisterArgument][], ctrs: Map<string, number>): MIRPhi {
    let vassign = new Map<string, MIRRegisterArgument>();
    opts.forEach((e) => vassign.set(e[0], e[1]));

    const ssaCtr = ctrs.get(lv) as number + 1;
    ctrs.set(lv, ssaCtr);

    const vname = lv + `$${ssaCtr}`;
    if (lv.startsWith("#tmp_")) {
        return new MIRPhi(sinfo, vassign, new MIRTempRegister(Number.parseInt(lv.substr(5)), vname));
    }
    else {
        return new MIRPhi(sinfo, vassign, new MIRVarLocal(lv, vname));
    }
}

function computePhis(sinfo: SourceInfo, block: string, ctrs: Map<string, number>, remapped: Map<string, Map<string, MIRRegisterArgument>>, links: Map<string, FlowLink>, live: Map<string, BlockLiveSet>): [MIRPhi[], Map<string, MIRRegisterArgument>] {
    let remap = new Map<string, MIRRegisterArgument>();
    let phis: MIRPhi[] = [];

    (live.get(block) as BlockLiveSet).liveEntry.forEach((lv) => {
        const preds = (links.get(block) as FlowLink).preds;

        let phiOpts: [string, MIRRegisterArgument][] = [];
        let uniqueOpts = new Map<string, MIRRegisterArgument>();
        preds.forEach((pred) => {
            const pm = remapped.get(pred) as Map<string, MIRRegisterArgument>;
            const mreg = pm.get(lv) as MIRRegisterArgument;
            uniqueOpts.set(mreg.nameID, mreg);
            phiOpts.push([pred, mreg]);
        });

        if (uniqueOpts.size === 1) {
            const rmp = [...uniqueOpts][0][1];
            remap.set(lv, rmp);
        }
        else {
            const phi = generatePhi(sinfo, lv, phiOpts, ctrs);

            phis.push(phi);
            remap.set(lv, phi.trgt);
        }
    });

    return [phis, remap];
}

function convertBodyToSSA(body: MIRBody, args: string[], captured: string[]) {
    if (typeof (body) === "string") {
        return;
    }

    const blocks = body.body as Map<string, MIRBasicBlock>;
    const links = computeBlockLinks(blocks);
    const live = computeBlockLiveVars(blocks);
    const torder = topologicalOrder(blocks);

    let remapped = new Map<string, Map<string, MIRRegisterArgument>>();
    let ctrs = new Map<string, number>();

    for (let j = 0; j < torder.length; ++j) {
        const block = torder[j];

        if (block.label === "entry") {
            let remap = new Map<string, MIRRegisterArgument>();
            args.forEach((arg) => remap.set(arg, new MIRVarParameter(arg)));
            captured.forEach((capture) => remap.set(capture, new MIRVarCaptured(capture)));
            remap.set("_ir_ret_", new MIRVarLocal("_ir_ret_"));

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

export { convertBodyToSSA };
