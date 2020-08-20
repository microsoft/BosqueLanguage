"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_ops_1 = require("./mir_ops");
const mir_info_1 = require("./mir_info");
const mir_assembly_1 = require("./mir_assembly");
const parser_1 = require("../ast/parser");
const mir_vartype_1 = require("./mir_vartype");
const sinfo_undef = new parser_1.SourceInfo(-1, -1, -1, -1);
class FunctionalizeEnv {
    constructor(rtype, invid, largs, trgtphis, jlabel) {
        this.tmpctr = 100000;
        this.nbbl = [];
        this.rphimap = new Map();
        this.rtype = rtype;
        this.invid = invid;
        this.largs = largs;
        this.trgtphis = trgtphis;
        this.jlabel = jlabel;
    }
    generateTempRegister() {
        return new mir_ops_1.MIRTempRegister(this.tmpctr++);
    }
    setResultPhiEntry(srcblock, v) {
        this.rphimap.set(srcblock, v);
    }
}
function generateTargetFunctionName(cinvoke, trgtlbl) {
    return (cinvoke + "$$" + trgtlbl);
}
function generateTailCall(bblabel, fenv) {
    const phiargs = fenv.trgtphis.map((phi) => phi.src.get(bblabel));
    const args = [...fenv.largs, ...phiargs];
    return new mir_ops_1.MIRInvokeFixedFunction(sinfo_undef, fenv.rtype, fenv.invid, args, fenv.generateTempRegister());
}
function updateJumpOp(bb, fenv) {
    const jop = bb.ops[bb.ops.length - 1];
    if (jop.trgtblock === fenv.jlabel) {
        const tc = generateTailCall(bb.label, fenv);
        bb.ops[bb.ops.length - 1] = tc;
        bb.ops.push(new mir_ops_1.MIRJump(sinfo_undef, "exit"));
        fenv.setResultPhiEntry(bb.label, tc.trgt);
    }
}
function updateCondJumpOp(bb, fenv, nbb) {
    const jop = bb.ops[bb.ops.length - 1];
    if (jop.trueblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1];
        const tc = generateTailCall(bb.label, fenv);
        const ntb = new mir_ops_1.MIRBasicBlock(bb.label + "tbb", [tc, new mir_ops_1.MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new mir_ops_1.MIRJumpCond(tjop.sinfo, tjop.arg, ntb.label, tjop.falseblock);
        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
    if (jop.falseblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1];
        const tc = generateTailCall(bb.label, fenv);
        const ntb = new mir_ops_1.MIRBasicBlock(bb.label + "fbb", [tc, new mir_ops_1.MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new mir_ops_1.MIRJumpCond(fjop.sinfo, fjop.arg, fjop.trueblock, ntb.label);
        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}
function updateNoneJumpOp(bb, fenv, nbb) {
    const jop = bb.ops[bb.ops.length - 1];
    if (jop.noneblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1];
        const tc = generateTailCall(bb.label, fenv);
        const ntb = new mir_ops_1.MIRBasicBlock(bb.label + "tbb", [tc, new mir_ops_1.MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new mir_ops_1.MIRJumpNone(tjop.sinfo, tjop.arg, ntb.label, tjop.someblock);
        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
    if (jop.someblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1];
        const tc = generateTailCall(bb.label, fenv);
        const ntb = new mir_ops_1.MIRBasicBlock(bb.label + "fbb", [tc, new mir_ops_1.MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new mir_ops_1.MIRJumpNone(fjop.sinfo, fjop.arg, fjop.noneblock, ntb.label);
        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}
function replaceJumpsWithCalls(bbl, fenv) {
    let nbb = [];
    bbl
        .filter((bb) => bb.ops.length !== 0)
        .forEach((bb) => {
        const lop = bb.ops[bb.ops.length - 1];
        switch (lop.tag) {
            case mir_ops_1.MIROpTag.MIRJump: {
                updateJumpOp(bb, fenv);
                break;
            }
            case mir_ops_1.MIROpTag.MIRJumpCond: {
                updateCondJumpOp(bb, fenv, nbb);
                break;
            }
            case mir_ops_1.MIROpTag.MIRJumpNone: {
                updateNoneJumpOp(bb, fenv, nbb);
                break;
            }
        }
    });
    return nbb;
}
function rebuildExitPhi(bbl, fenv, deadlabels) {
    const exit = bbl.find((bb) => bb.label === "exit");
    if (exit.ops.length === 0 || !(exit.ops[0] instanceof mir_ops_1.MIRPhi)) {
        const phi = new mir_ops_1.MIRPhi(sinfo_undef, new Map(fenv.rphimap), new mir_ops_1.MIRVariable("$$return"));
        exit.ops = [phi, ...exit.ops];
    }
    else {
        const phi = exit.ops[0];
        deadlabels.forEach((dl) => {
            if (phi.src.has(dl)) {
                phi.src.delete(dl);
            }
        });
        fenv.rphimap.forEach((v, lbl) => phi.src.set(lbl, v));
    }
}
function processBody(invid, b, rtype) {
    const links = mir_info_1.computeBlockLinks(b.body);
    const bo = mir_info_1.topologicalOrder(b.body);
    const lv = mir_info_1.computeBlockLiveVars(b.body);
    const vtypes = b.vtypes;
    const lidx = bo.findIndex((bb) => bb.label === "returnassign");
    const fjidx = bo.findIndex((bb) => links.get(bb.label).preds.size > 1);
    if (fjidx === -1 || lidx <= fjidx) {
        return undefined;
    }
    const jidx = (bo.length - 1) - [...bo].reverse().findIndex((bb) => links.get(bb.label).preds.size > 1);
    const jlabel = bo[jidx].label;
    const phis = bo[jidx].ops.filter((op) => op instanceof mir_ops_1.MIRPhi);
    const phivargs = phis.map((op) => op.trgt.nameID);
    const phivkill = new Set([].concat(...phis.map((op) => [...op.src].map((src) => src[1].nameID))));
    const rblocks = [...bo.slice(0, jidx), new mir_ops_1.MIRBasicBlock("exit", [])];
    const fblocks = [new mir_ops_1.MIRBasicBlock("entry", bo[jidx].ops.slice(phis.length)), ...bo.slice(jidx + 1)];
    const jvars = [...lv.get(bo[jidx].label).liveEntry].filter((lvn) => !phivkill.has(lvn[0])).sort((a, b) => a[0].localeCompare(b[0]));
    const oparams = jvars.map((lvn) => new mir_assembly_1.MIRFunctionParameter(lvn[0], vtypes.get(lvn[0])));
    const phiparams = phivargs.map((pv) => new mir_assembly_1.MIRFunctionParameter(pv, vtypes.get(pv)));
    const nparams = [...oparams, ...phiparams];
    const ninvid = generateTargetFunctionName(invid, jlabel);
    let fenv = new FunctionalizeEnv(rtype.trkey, ninvid, jvars.map((lvn) => lvn[1]), phis, jlabel);
    const nbb = replaceJumpsWithCalls(rblocks, fenv);
    rebuildExitPhi(rblocks, fenv, bo.slice(jidx).map((bb) => bb.label));
    b.body = new Map();
    [...rblocks, ...nbb].forEach((bb) => b.body.set(bb.label, bb));
    return { nname: ninvid, nparams: nparams, nblocks: fblocks };
}
function processInvoke(inv, masm) {
    const f1 = processBody(inv.key, inv.body, masm.typeMap.get(inv.resultType));
    if (f1 === undefined) {
        return [];
    }
    const invargs = new Map();
    inv.params.forEach((param) => invargs.set(param.name, masm.typeMap.get(param.type)));
    mir_vartype_1.computeVarTypesForInvoke(inv.body, invargs, masm.typeMap.get(inv.resultType), masm);
    let rbl = [];
    let wl = [{ nbi: f1, post: inv.postconditions }];
    while (wl.length !== 0) {
        const item = wl.shift();
        const bproc = item.nbi;
        const bmap = new Map();
        bproc.nblocks.map((bb) => bmap.set(bb.label, bb));
        const ninv = new mir_assembly_1.MIRInvokeBodyDecl(inv.enclosingDecl, "[FUNCTIONALIZE_SPECIAL]", bproc.nname, bproc.nname, [...inv.attributes], inv.recursive, [...inv.pragmas], inv.sourceLocation, inv.srcFile, bproc.nparams, inv.resultType, undefined, item.post, new mir_ops_1.MIRBody(inv.srcFile, inv.sourceLocation, bmap));
        rbl.push(ninv);
        let ninvargs = new Map();
        ninv.params.forEach((param) => ninvargs.set(param.name, masm.typeMap.get(param.type)));
        mir_vartype_1.computeVarTypesForInvoke(ninv.body, ninvargs, masm.typeMap.get(ninv.resultType), masm);
        const ff = processBody(inv.key, inv.body, masm.typeMap.get(ninv.resultType));
        if (ff !== undefined) {
            let invargs = new Map();
            inv.params.forEach((param) => invargs.set(param.name, masm.typeMap.get(param.type)));
            mir_vartype_1.computeVarTypesForInvoke(inv.body, invargs, masm.typeMap.get(inv.resultType), masm);
            wl.push({ nbi: ff, post: undefined });
        }
    }
    return rbl;
}
function functionalizeInvokes(masm) {
    const oinvokes = [...masm.invokeDecls].map((iv) => iv[1]);
    oinvokes.forEach((iiv) => {
        const nil = processInvoke(iiv, masm);
        nil.forEach((niv) => masm.invokeDecls.set(niv.key, niv));
    });
}
exports.functionalizeInvokes = functionalizeInvokes;
//# sourceMappingURL=functionalize.js.map