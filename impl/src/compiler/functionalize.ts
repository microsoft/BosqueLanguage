//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBody, MIRResolvedTypeKey, MIRBasicBlock, MIRInvokeKey, MIRRegisterArgument, MIROpTag, MIRJump, MIRInvokeFixedFunction, MIRJumpCond, MIRJumpNone, MIRRegisterAssign } from "./mir_ops";
import { computeBlockLinks, topologicalOrder, FlowLink, computeBlockLiveVars, BlockLiveSet, computeVarTypes } from "./mir_info";
import { MIRFunctionParameter, MIRType, MIRInvokeBodyDecl, MIRAssembly } from "./mir_assembly";
import { SourceInfo } from "../ast/parser";
import { MIREmitter } from "./mir_emitter";

type NBodyInfo = {
    nname: MIRInvokeKey;
    nparams: MIRFunctionParameter[];
    nblocks: MIRBasicBlock[];
};

const sinfo_undef = new SourceInfo(-1, -1, -1, -1);

class FunctionalizeEnv
{
    readonly emitter: MIREmitter;
    readonly rtype: MIRResolvedTypeKey;
    readonly invid: MIRInvokeKey;
    readonly tailargs: MIRRegisterArgument[];
    readonly jlabel: string;

    nbbl: MIRBasicBlock[] = [];

    constructor(emitter: MIREmitter, rtype: MIRResolvedTypeKey, invid: MIRInvokeKey, tailargs: MIRRegisterArgument[], jlabel: string) {
        this.emitter = emitter;
        this.rtype = rtype;
        this.invid = invid;
        this.tailargs = tailargs;
        this.jlabel = jlabel;
    }
}

function generateTargetFunctionName(cinvoke: MIRInvokeKey, trgtlbl: string): MIRInvokeKey {
    return (cinvoke + "$$" + trgtlbl) as MIRInvokeKey;
}

function generateTailCall(fenv: FunctionalizeEnv): MIRInvokeFixedFunction {
    return new MIRInvokeFixedFunction(sinfo_undef, fenv.rtype, fenv.invid, fenv.tailargs, undefined, new MIRRegisterArgument("$__ir_ret__"), undefined);
}

function updateJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJump;
    if (jop.trgtblock === fenv.jlabel) {
        const tc = generateTailCall(fenv);
        bb.ops[bb.ops.length - 1] = tc;
        bb.ops.push(new MIRJump(sinfo_undef, "returnassign"));
    }
}

function updateCondJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv, nbb: MIRBasicBlock[]) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

    if(jop.trueblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "returnassign")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(tjop.sinfo, tjop.arg, ntb.label, tjop.falseblock);

        nbb.push(ntb);
    }

    if(jop.falseblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "returnassign")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(fjop.sinfo, fjop.arg, fjop.trueblock, ntb.label);

        nbb.push(ntb);
    }
}

function updateNoneJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv, nbb: MIRBasicBlock[]) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

    if(jop.noneblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "returnassign")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(tjop.sinfo, tjop.arg, tjop.arglayouttype, ntb.label, tjop.someblock);

        nbb.push(ntb);
    }

    if(jop.someblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "returnassign")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(fjop.sinfo, fjop.arg, fjop.arglayouttype, fjop.noneblock, ntb.label);

        nbb.push(ntb);
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

function computeBodySplits(jidx: number, bo: MIRBasicBlock[], struct: Map<string, FlowLink>): { rblocks: MIRBasicBlock[], cblocks: MIRBasicBlock[] } {
    let continuationblocks: MIRBasicBlock[] = [bo[jidx]];

    const getRBB = (cblocks: MIRBasicBlock[]) => {
        return bo.find((bb) => {
            if(bb.label === "returnassign" || cblocks.find((obb) => obb.label === bb.label) !== undefined) {
                return false;
            }

            let preds = (struct.get(bb.label) as FlowLink).preds;
            return cblocks.some((obb) => preds.has(obb.label));
        });
    }

    let rbb = getRBB(continuationblocks);
    while(rbb !== undefined) {
        continuationblocks.push(rbb);

        rbb = getRBB(continuationblocks);
    }

    const rblocks: MIRBasicBlock[] = bo.filter((bb) => continuationblocks.find((rbb) => rbb.label === bb.label) === undefined);

    return { rblocks: rblocks, cblocks: continuationblocks.slice(1) };
}

function processBody(emitter: MIREmitter, invid: string, masm: MIRAssembly, b: MIRBody, params: MIRFunctionParameter[]): NBodyInfo | undefined {
    const links = computeBlockLinks(b.body);
    const bo = topologicalOrder(b.body);
    const lv = computeBlockLiveVars(b.body);
    const vtypes = computeVarTypes(b.body, params, masm, "NSCore::Bool");
    const rtype = vtypes.get("$__ir_ret__") as MIRType;

    if(bo.find((bb) => (links.get(bb.label) as FlowLink).preds.size > 1 && bb.label !== "returnassign") === undefined) {
        return undefined;
    }

    const jidx = (bo.length - 1) - [...bo].reverse().findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1 && bb.label !== "returnassign");
    const jlabel = bo[jidx].label;
    
    let {rblocks, cblocks} = computeBodySplits(jidx, bo, links);
    const tailvars = [...(lv.get(bo[jidx].label) as BlockLiveSet).liveEntry].sort((a, b) => a[0].localeCompare(b[0]));
    const nparams = tailvars.map((lvn) => new MIRFunctionParameter(lvn[0], (vtypes.get(lvn[0]) as MIRType).trkey));

    const ninvid = generateTargetFunctionName(invid, jlabel);

    let fenv = new FunctionalizeEnv(emitter, rtype.trkey, ninvid, tailvars.map((lvn) => lvn[1]), jlabel);
    const nbb = replaceJumpsWithCalls(rblocks, fenv);

    cblocks = [
        new MIRBasicBlock("entry", [...bo[jidx].ops]), 
        ...cblocks,
        new MIRBasicBlock("returnassign", [
            new MIRRegisterAssign(sinfo_undef, new MIRRegisterArgument("$__ir_ret__"), new MIRRegisterArgument("$$return"), rtype.trkey, undefined),
            new MIRJump(sinfo_undef, "exit")
        ]),
        new MIRBasicBlock("exit", [])
    ];

    b.body = new Map<string, MIRBasicBlock>();
    [...rblocks, ...nbb].forEach((bb) => b.body.set(bb.label, bb));

    return {nname: ninvid, nparams: nparams, nblocks: cblocks};
}

function processInvoke(emitter: MIREmitter, inv: MIRInvokeBodyDecl, masm: MIRAssembly): MIRInvokeBodyDecl[] {
    const f1 = processBody(emitter, inv.key, masm, inv.body, inv.params);
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
        const ninv = new MIRInvokeBodyDecl(inv.enclosingDecl, "[FUNCTIONALIZE_SPECIAL]", bproc.nname, bproc.nname, [...inv.attributes], inv.recursive, inv.sourceLocation, inv.srcFile, bproc.nparams, 0, inv.resultType, undefined, item.post, new MIRBody(inv.srcFile, inv.sourceLocation, bmap));
        rbl.push(ninv);

        const ff = processBody(emitter, inv.key, masm, inv.body, inv.params);
        if (ff !== undefined) {
            wl.push({ nbi: ff, post: undefined })
        }
    }

    return rbl;
}

function functionalizeInvokes(emitter: MIREmitter, masm: MIRAssembly) {
    const oinvokes = [...masm.invokeDecls].map((iv) => iv[1]);
    oinvokes.forEach((iiv) => {
        const nil = processInvoke(emitter, iiv, masm);
        nil.forEach((niv) => masm.invokeDecls.set(niv.key, niv));
    });
}

export { functionalizeInvokes };
