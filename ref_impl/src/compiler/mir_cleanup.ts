//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIRBody, MIRArgument, MIROpTag, MIRTempRegister, MIRLoadConst, MIRAccessCapturedVariable, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorPrimary, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord, MIRCallNamespaceFunction, MIRCallStaticFunction, MIRAccessFromIndex, MIRProjectFromIndecies, MIRAccessFromProperty, MIRProjectFromProperties, MIRAccessFromField, MIRProjectFromFields, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeKnownTarget, MIRInvokeVirtualTarget, MIRCallLambda, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRRegAssign, MIRTruthyConvert, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJumpCond, MIRJumpNone, MIRBasicBlock, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf, MIRLogicStore } from "./mir_ops";

//
//Implement cleanup passes for the MIR after translation from the AST representation:
//  (1) Remove redundant temp register use
//  (2) Convert to SSA form
//

function propagateTmpAssign_Bind(treg: MIRTempRegister, arg: MIRArgument, propMap: Map<number, MIRArgument>) {
    assert(!propMap.has(treg.regID));
    propMap.set(treg.regID, arg);
}

function propagateTmpAssign_Remap(arg: MIRArgument, propMap: Map<number, MIRArgument>): MIRArgument {
    return (arg instanceof MIRTempRegister && propMap.has(arg.regID)) ? propMap.get(arg.regID) as MIRArgument : arg;
}

function propagateTmpAssign_RemapArgs(args: MIRArgument[], propMap: Map<number, MIRArgument>): MIRArgument[] {
    return args.map((v) => propagateTmpAssign_Remap(v, propMap));
}

function propagateTmpAssign_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function propagateTmpAssignForOp(op: MIROp, propMap: Map<number, MIRArgument>) {
    switch (op.tag) {
        case MIROpTag.LoadConst: {
            const lc = op as MIRLoadConst;
            propagateTmpAssign_Bind(lc.trgt, lc.src, propMap);
            break;
        }
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            //TODO: maybe these can be propagated later too when we add the corresponding MIRArgument bits
            break;
        }
        case MIROpTag.AccessCapturedVariable: {
            const lcv = op as MIRAccessCapturedVariable;
            propagateTmpAssign_Bind(lcv.trgt, lcv.name, propMap);
            break;
        }
        case MIROpTag.AccessArgVariable: {
            const lav = op as MIRAccessArgVariable;
            propagateTmpAssign_Bind(lav.trgt, lav.name, propMap);
            break;
        }
        case MIROpTag.AccessLocalVariable: {
            const llv = op as MIRAccessLocalVariable;
            propagateTmpAssign_Bind(llv.trgt, llv.name, propMap);
            break;
        }
        case MIROpTag.ConstructorPrimary: {
            const cp = op as MIRConstructorPrimary;
            cp.args = propagateTmpAssign_RemapArgs(cp.args, propMap);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            const cc = op as MIRConstructorPrimaryCollectionSingletons;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            const cc = op as MIRConstructorPrimaryCollectionCopies;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            const cc = op as MIRConstructorPrimaryCollectionMixed;
            cc.args = propagateTmpAssign_RemapStructuredArgs(cc.args, (v) => [v[0], propagateTmpAssign_Remap(v[1], propMap)] as [boolean, MIRArgument]);
            break;
        }
        case MIROpTag.ConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            tc.args = propagateTmpAssign_RemapArgs(tc.args, propMap);
            break;
        }
        case MIROpTag.ConstructorRecord: {
            const tc = op as MIRConstructorRecord;
            tc.args = propagateTmpAssign_RemapStructuredArgs(tc.args, (v) => [v[0], propagateTmpAssign_Remap(v[1], propMap)] as [string, MIRArgument]);
            break;
        }
        case MIROpTag.ConstructorLambda: {
            break;
        }
        case MIROpTag.CallNamespaceFunction: {
            const fc = op as MIRCallNamespaceFunction;
            fc.args = propagateTmpAssign_RemapArgs(fc.args, propMap);
            break;
        }
        case MIROpTag.CallStaticFunction: {
            const fc = op as MIRCallStaticFunction;
            fc.args = propagateTmpAssign_RemapArgs(fc.args, propMap);
            break;
        }
        case MIROpTag.MIRAccessFromIndex: {
            const ai = op as MIRAccessFromIndex;
            ai.arg = propagateTmpAssign_Remap(ai.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            const pi = op as MIRProjectFromIndecies;
            pi.arg = propagateTmpAssign_Remap(pi.arg, propMap);
            break;
        }
        case MIROpTag.MIRAccessFromProperty: {
            const ap = op as MIRAccessFromProperty;
            ap.arg = propagateTmpAssign_Remap(ap.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromProperties: {
            const pi = op as MIRProjectFromProperties;
            pi.arg = propagateTmpAssign_Remap(pi.arg, propMap);
            break;
        }
        case MIROpTag.MIRAccessFromField: {
            const af = op as MIRAccessFromField;
            af.arg = propagateTmpAssign_Remap(af.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromFields: {
            const pf = op as MIRProjectFromFields;
            pf.arg = propagateTmpAssign_Remap(pf.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            const pt = op as MIRProjectFromTypeTuple;
            pt.arg = propagateTmpAssign_Remap(pt.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            const pr = op as MIRProjectFromTypeRecord;
            pr.arg = propagateTmpAssign_Remap(pr.arg, propMap);
            break;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            const pc = op as MIRProjectFromTypeConcept;
            pc.arg = propagateTmpAssign_Remap(pc.arg, propMap);
            break;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            const mi = op as MIRModifyWithIndecies;
            mi.arg = propagateTmpAssign_Remap(mi.arg, propMap);
            mi.updates = propagateTmpAssign_RemapStructuredArgs<[number, MIRArgument]>(mi.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case MIROpTag.MIRModifyWithProperties: {
            const mp = op as MIRModifyWithProperties;
            mp.arg = propagateTmpAssign_Remap(mp.arg, propMap);
            mp.updates = propagateTmpAssign_RemapStructuredArgs<[string, MIRArgument]>(mp.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case MIROpTag.MIRModifyWithFields: {
            const mf = op as MIRModifyWithFields;
            mf.arg = propagateTmpAssign_Remap(mf.arg, propMap);
            mf.updates = propagateTmpAssign_RemapStructuredArgs<[string, MIRArgument]>(mf.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            const st = op as MIRStructuredExtendTuple;
            st.arg = propagateTmpAssign_Remap(st.arg, propMap);
            st.update = propagateTmpAssign_Remap(st.update, propMap);
            break;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            const sr = op as MIRStructuredExtendRecord;
            sr.arg = propagateTmpAssign_Remap(sr.arg, propMap);
            sr.update = propagateTmpAssign_Remap(sr.update, propMap);
            break;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            const so = op as MIRStructuredExtendObject;
            so.arg = propagateTmpAssign_Remap(so.arg, propMap);
            so.update = propagateTmpAssign_Remap(so.update, propMap);
            break;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            const invk = op as MIRInvokeKnownTarget;
            invk.args = propagateTmpAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            const invk = op as MIRInvokeVirtualTarget;
            invk.args = propagateTmpAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case MIROpTag.MIRCallLambda: {
            const cl = op as MIRCallLambda;
            cl.lambda = propagateTmpAssign_Remap(cl.lambda, propMap);
            cl.args = propagateTmpAssign_RemapArgs(cl.args, propMap);
            break;
        }
        case MIROpTag.MIRPrefixOp: {
            const pfx = op as MIRPrefixOp;
            pfx.arg = propagateTmpAssign_Remap(pfx.arg, propMap);
            break;
        }
        case MIROpTag.MIRBinOp: {
            const bop = op as MIRBinOp;
            bop.lhs = propagateTmpAssign_Remap(bop.lhs, propMap);
            bop.rhs = propagateTmpAssign_Remap(bop.rhs, propMap);
            break;
        }
        case MIROpTag.MIRBinEq: {
            const beq = op as MIRBinEq;
            beq.lhs = propagateTmpAssign_Remap(beq.lhs, propMap);
            beq.rhs = propagateTmpAssign_Remap(beq.rhs, propMap);
            break;
        }
        case MIROpTag.MIRBinCmp: {
            const bcp = op as MIRBinCmp;
            bcp.lhs = propagateTmpAssign_Remap(bcp.lhs, propMap);
            bcp.rhs = propagateTmpAssign_Remap(bcp.rhs, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOfNone: {
            const ton = op as MIRIsTypeOfNone;
            ton.arg = propagateTmpAssign_Remap(ton.arg, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            const tos = op as MIRIsTypeOfSome;
            tos.arg = propagateTmpAssign_Remap(tos.arg, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOf: {
            const tog = op as MIRIsTypeOf;
            tog.arg = propagateTmpAssign_Remap(tog.arg, propMap);
            break;
        }
        case MIROpTag.MIRRegAssign: {
            const regop = op as MIRRegAssign;
            regop.src = propagateTmpAssign_Remap(regop.src, propMap);
            propagateTmpAssign_Bind(regop.trgt, regop.src, propMap);
            break;
        }
        case MIROpTag.MIRTruthyConvert: {
            const tcop = op as MIRTruthyConvert;
            tcop.src = propagateTmpAssign_Remap(tcop.src, propMap);
            break;
        }
        case MIROpTag.MIRLogicStore: {
            const llop = op as MIRLogicStore;
            llop.lhs = propagateTmpAssign_Remap(llop.lhs, propMap);
            llop.rhs = propagateTmpAssign_Remap(llop.rhs, propMap);
            break;
        }
        case MIROpTag.MIRVarStore: {
            const vs = op as MIRVarStore;
            vs.src = propagateTmpAssign_Remap(vs.src, propMap);
            break;
        }
        case MIROpTag.MIRReturnAssign: {
            const ra = op as MIRReturnAssign;
            ra.src = propagateTmpAssign_Remap(ra.src, propMap);
            break;
        }
        case MIROpTag.MIRAbort: {
            break;
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = propagateTmpAssign_Remap(dbg.value, propMap);
            }
            break;
        }
        case MIROpTag.MIRJump: {
            break;
        }
        case MIROpTag.MIRJumpCond: {
            const cjop = op as MIRJumpCond;
            cjop.arg = propagateTmpAssign_Remap(cjop.arg, propMap);
            break;
        }
        case MIROpTag.MIRJumpNone: {
            const njop = op as MIRJumpNone;
            njop.arg = propagateTmpAssign_Remap(njop.arg, propMap);
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

function propagateTmpAssignForBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        let propMap = new Map<number, MIRArgument>();
        for (let i = 0; i < blk.ops.length; ++i) {
            propagateTmpAssignForOp(blk.ops[i], propMap);
        }
    });
}

function computeTmpUseForBody(body: MIRBody): Set<number> {
    if (typeof (body) === "string") {
        return new Set<number>();
    }

    let usedTemps = new Set<number>();
    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        for (let i = 0; i < blk.ops.length; ++i) {
            const optmps = blk.ops[i].getUsedVars().filter((arg) => arg instanceof MIRTempRegister);
            for (let j = 0; j < optmps.length; ++j) {
                usedTemps.add((optmps[j] as MIRTempRegister).regID);
            }
        }
    });

    return usedTemps;
}

function isDeadTempAssign(op: MIROp, liveTemps: Set<number>): boolean {
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.AccessCapturedVariable:
        case MIROpTag.AccessArgVariable:
        case MIROpTag.AccessLocalVariable:
        case MIROpTag.MIRRegAssign: {
            return op.getModVars().every((mv) => mv instanceof MIRTempRegister && !liveTemps.has(mv.regID));
        }
        default:
            return false;
    }
}

function removeDeadTempAssignsFromBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    let oldLiveSize = Number.MAX_SAFE_INTEGER;
    let liveTemps = computeTmpUseForBody(body);
    while (liveTemps.size < oldLiveSize) {
        let nbody = new Map<string, MIRBasicBlock>();
        (body.body as Map<string, MIRBasicBlock>).forEach((blk, id) => {
            const ops = blk.ops.filter((op) => !isDeadTempAssign(op, liveTemps));
            nbody.set(id, new MIRBasicBlock(id, ops));
        });
        body.body = nbody;

        oldLiveSize = liveTemps.size;
        liveTemps = computeTmpUseForBody(body);
    }
}

export { propagateTmpAssignForBody, removeDeadTempAssignsFromBody };
