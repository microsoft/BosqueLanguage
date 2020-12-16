//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBody, MIRResolvedTypeKey, MIRPhi, MIRBasicBlock, MIRInvokeKey, MIRRegisterArgument, MIROpTag, MIRJump, MIRInvokeFixedFunction, MIRJumpCond, MIRJumpNone } from "./mir_ops";
import { computeBlockLinks, topologicalOrder, FlowLink, computeBlockLiveVars, BlockLiveSet, computeVarTypes } from "./mir_info";
import { MIRFunctionParameter, MIRType, MIRInvokeBodyDecl, MIRAssembly } from "./mir_assembly";
import { SourceInfo } from "../ast/parser";

type NBodyInfo = {
    nname: MIRInvokeKey;
    nparams: MIRFunctionParameter[];
    nblocks: MIRBasicBlock[];
};

const sinfo_undef = new SourceInfo(-1, -1, -1, -1);

class FunctionalizeEnv
{
    tmpctr: number = 200000;
    readonly rtype: MIRResolvedTypeKey;
    readonly invid: MIRInvokeKey;
    readonly largs: MIRRegisterArgument[];
    readonly trgtphis: MIRPhi[];
    readonly jlabel: string;

    nbbl: MIRBasicBlock[] = [];
    rphimap: Map<string, MIRRegisterArgument> = new Map<string, MIRRegisterArgument>();

    constructor(rtype: MIRResolvedTypeKey, invid: MIRInvokeKey, largs: MIRRegisterArgument[], trgtphis: MIRPhi[], jlabel: string) {
        this.rtype = rtype;
        this.invid = invid;
        this.largs = largs;
        this.trgtphis = trgtphis;
        this.jlabel = jlabel;
    }

    generateTempRegister(): MIRRegisterArgument {
        return new MIRRegisterArgument(`#tmp_${this.tmpctr++}`);
    }

    setResultPhiEntry(srcblock: string, v: MIRRegisterArgument) {
        this.rphimap.set(srcblock, v);
    }
}

function generateTargetFunctionName(cinvoke: MIRInvokeKey, trgtlbl: string): MIRInvokeKey {
    return (cinvoke + "$$" + trgtlbl) as MIRInvokeKey;
}


function generateTailCall(bblabel: string, fenv: FunctionalizeEnv): MIRInvokeFixedFunction {
    const phiargs = fenv.trgtphis.map((phi) => phi.src.get(bblabel) as MIRRegisterArgument);
    const args = [...fenv.largs, ...phiargs];

    return new MIRInvokeFixedFunction(sinfo_undef, fenv.rtype, fenv.invid, args, undefined, fenv.generateTempRegister(), undefined);
}

function updateJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJump;
    if (jop.trgtblock === fenv.jlabel) {
        const tc = generateTailCall(bb.label, fenv);
        bb.ops[bb.ops.length - 1] = tc;
        bb.ops.push(new MIRJump(sinfo_undef, "exit")); 
        
        fenv.setResultPhiEntry(bb.label, tc.trgt);
    }
}

function updateCondJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv, nbb: MIRBasicBlock[]) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

    if(jop.trueblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(tjop.sinfo, tjop.arg, ntb.label, tjop.falseblock);

        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }

    if(jop.falseblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(fjop.sinfo, fjop.arg, fjop.trueblock, ntb.label);

        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}

function updateNoneJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv, nbb: MIRBasicBlock[]) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

    if(jop.noneblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(tjop.sinfo, tjop.arg, tjop.arglayouttype, ntb.label, tjop.someblock);

        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }

    if(jop.someblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(fjop.sinfo, fjop.arg, fjop.arglayouttype, fjop.noneblock, ntb.label);

        nbb.push(ntb);
        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}

function replaceJumpsWithCalls(bbl: MIRBasicBlock[], fenv: FunctionalizeEnv): MIRBasicBlock[] {
    let nbb: MIRBasicBlock[] = [];
    bbl
        .filter((bb) => bb.ops.length !== 0)
        .forEach((bb) => {
            const lop = bb.ops[bb.ops.length - 1];
            switch (lop.tag) {
                case MIROpTag.MIRJump: {
                    updateJumpOp(bb, fenv);
                    break;
                }
                case MIROpTag.MIRJumpCond: {
                    updateCondJumpOp(bb, fenv, nbb);
                    break;
                }
                case MIROpTag.MIRJumpNone: {
                    updateNoneJumpOp(bb, fenv, nbb);
                    break;
                }
            }
        });

    return nbb;
}

function rebuildExitPhi(bbl: MIRBasicBlock[], fenv: FunctionalizeEnv, deadlabels: string[]) {
    const exit = bbl.find((bb) => bb.label === "exit") as MIRBasicBlock;

    if(exit.ops.length === 0 || !(exit.ops[0] instanceof MIRPhi)) {
        const phi = new MIRPhi(sinfo_undef, new Map<string, MIRRegisterArgument>(fenv.rphimap), fenv.rtype, new MIRRegisterArgument("$$return"));
        exit.ops = [phi, ...exit.ops];
    }
    else {
        const phi = exit.ops[0] as MIRPhi;
        deadlabels.forEach((dl) => {
            if(phi.src.has(dl)) {
                phi.src.delete(dl);
            }
        });

        fenv.rphimap.forEach((v, lbl) => phi.src.set(lbl, v));
    }
}

function processBody(invid: string, masm: MIRAssembly, b: MIRBody, params: MIRFunctionParameter[], rtype: MIRType): NBodyInfo | undefined {
    const links = computeBlockLinks(b.body);
    const bo = topologicalOrder(b.body);
    const lv = computeBlockLiveVars(b.body);
    const vtypes = computeVarTypes(b.body, params, masm, "NSCore::Bool");

    const lidx = bo.findIndex((bb) => bb.label === "returnassign");
    const fjidx = bo.findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1);

    if(fjidx === -1 || lidx <= fjidx) {
        return undefined;
    }

    const jidx = (bo.length - 1) - [...bo].reverse().findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1);
    const jlabel = bo[jidx].label;

    const phis = bo[jidx].ops.filter((op) => op instanceof MIRPhi) as MIRPhi[];
    const phivargs = phis.map((op) => op.trgt.nameID);
    const phivkill = new Set(([] as string[]).concat(...phis.map((op) => [...op.src].map((src) => src[1].nameID))));

    const rblocks = [...bo.slice(0, jidx), new MIRBasicBlock("exit", [])];
    const fblocks = [new MIRBasicBlock("entry", bo[jidx].ops.slice(phis.length)), ...bo.slice(jidx + 1)];

    const jvars = [...(lv.get(bo[jidx].label) as BlockLiveSet).liveEntry].filter((lvn) => !phivkill.has(lvn[0])).sort((a, b) => a[0].localeCompare(b[0]));
    const oparams = jvars.map((lvn) => new MIRFunctionParameter(lvn[0], (vtypes.get(lvn[0]) as MIRType).trkey));
    const phiparams = phivargs.map((pv) => new MIRFunctionParameter(pv, (vtypes.get(pv) as MIRType).trkey));

    const nparams = [...oparams, ...phiparams];
    const ninvid = generateTargetFunctionName(invid, jlabel);

    let fenv = new FunctionalizeEnv(rtype.trkey, ninvid, jvars.map((lvn) => lvn[1]), phis, jlabel);
    const nbb = replaceJumpsWithCalls(rblocks, fenv);
    rebuildExitPhi(rblocks, fenv, bo.slice(jidx).map((bb) => bb.label));

    b.body = new Map<string, MIRBasicBlock>();
    [...rblocks, ...nbb].forEach((bb) => b.body.set(bb.label, bb));

    return {nname: ninvid, nparams: nparams, nblocks: fblocks};
}

function processInvoke(inv: MIRInvokeBodyDecl, masm: MIRAssembly): MIRInvokeBodyDecl[] {
    const f1 = processBody(inv.key, masm, inv.body, inv.params, masm.typeMap.get(inv.resultType) as MIRType);
    if(f1 === undefined) {
        return [];
    }

    let rbl: MIRInvokeBodyDecl[] = [];
    let wl = [{ nbi: f1, post: inv.postconditions }];
    while (wl.length !== 0) {
        const item = wl.shift() as { nbi: NBodyInfo, post: MIRInvokeKey[] | undefined };
        const bproc = item.nbi;

        const bmap = new Map<string, MIRBasicBlock>();
        bproc.nblocks.map((bb) => bmap.set(bb.label, bb));
        const ninv = new MIRInvokeBodyDecl(inv.enclosingDecl, "[FUNCTIONALIZE_SPECIAL]", bproc.nname, bproc.nname, [...inv.attributes], inv.recursive, inv.sourceLocation, inv.srcFile, bproc.nparams, false, inv.resultType, undefined, item.post, new MIRBody(inv.srcFile, inv.sourceLocation, bmap));
        rbl.push(ninv);

        const ff = processBody(inv.key, masm, inv.body, inv.params, masm.typeMap.get(ninv.resultType) as MIRType);
        if (ff !== undefined) {
            wl.push({ nbi: ff, post: undefined })
        }
    }

    return rbl;
}

function functionalizeInvokes(masm: MIRAssembly) {
    const oinvokes = [...masm.invokeDecls].map((iv) => iv[1]);
    oinvokes.forEach((iiv) => {
        const nil = processInvoke(iiv, masm);
        nil.forEach((niv) => masm.invokeDecls.set(niv.key, niv));
    });
}

export { functionalizeInvokes };
