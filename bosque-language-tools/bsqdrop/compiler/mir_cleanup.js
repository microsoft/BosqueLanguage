"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const assert = require("assert");
const mir_ops_1 = require("./mir_ops");
//
//Implement cleanup passes for the MIR after translation from the AST representation:
//  (1) Remove redundant temp register use
//  (2) Convert to SSA form
//
function propagateTmpAssign_Bind(treg, arg, propMap) {
    assert(!propMap.has(treg.regID));
    propMap.set(treg.regID, arg);
}
function propagateTmpAssign_Kill(arg, propMap) {
    let killset = new Set();
    propMap.forEach((v, k) => {
        if (v instanceof mir_ops_1.MIRRegisterArgument && v.nameID === arg.nameID) {
            killset.add(k);
        }
    });
    killset.forEach((k) => propMap.delete(k));
    if (arg instanceof mir_ops_1.MIRTempRegister) {
        propMap.delete(arg.regID);
    }
}
function propagateTmpAssign_Remap(arg, propMap) {
    return (arg instanceof mir_ops_1.MIRTempRegister && propMap.has(arg.regID)) ? propMap.get(arg.regID) : arg;
}
function propagateTmpAssign_RemapArgs(args, propMap) {
    return args.map((v) => propagateTmpAssign_Remap(v, propMap));
}
function propagateTmpAssign_RemapStructuredArgs(args, remap) {
    return args.map((v) => remap(v));
}
function propagateTmpAssignForOp(op, propMap) {
    const ks = op.getModVars();
    ks.forEach((kv) => propagateTmpAssign_Kill(kv, propMap));
    switch (op.tag) {
        case mir_ops_1.MIROpTag.MIRLoadConst: {
            const lc = op;
            propagateTmpAssign_Kill(lc.trgt, propMap);
            propagateTmpAssign_Bind(lc.trgt, lc.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadConstRegex:
        case mir_ops_1.MIROpTag.MIRLoadConstSafeString:
        case mir_ops_1.MIROpTag.MIRLoadConstTypedString:
        case mir_ops_1.MIROpTag.MIRAccessConstantValue:
        case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
            //TODO: maybe these can be propagated later too when we add the corresponding MIRArgument bits
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessArgVariable: {
            const lav = op;
            propagateTmpAssign_Bind(lav.trgt, lav.name, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
            const llv = op;
            propagateTmpAssign_Bind(llv.trgt, llv.name, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckDirect: {
            const cp = op;
            cp.rcvr = propagateTmpAssign_Remap(cp.rcvr, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
            const cp = op;
            cp.rcvr = propagateTmpAssign_Remap(cp.rcvr, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
            const cp = op;
            cp.args = propagateTmpAssign_RemapArgs(cp.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cc = op;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cc = op;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cc = op;
            cc.args = propagateTmpAssign_RemapStructuredArgs(cc.args, (v) => [v[0], propagateTmpAssign_Remap(v[1], propMap)]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorTuple: {
            const tc = op;
            tc.args = propagateTmpAssign_RemapArgs(tc.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorRecord: {
            const tc = op;
            tc.args = propagateTmpAssign_RemapStructuredArgs(tc.args, (v) => [v[0], propagateTmpAssign_Remap(v[1], propMap)]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorEphemeralValueList: {
            const tc = op;
            tc.args = propagateTmpAssign_RemapArgs(tc.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
            const ai = op;
            ai.arg = propagateTmpAssign_Remap(ai.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
            const pi = op;
            pi.arg = propagateTmpAssign_Remap(pi.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
            const ap = op;
            ap.arg = propagateTmpAssign_Remap(ap.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
            const pi = op;
            pi.arg = propagateTmpAssign_Remap(pi.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromField: {
            const af = op;
            af.arg = propagateTmpAssign_Remap(af.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromFields: {
            const pf = op;
            pf.arg = propagateTmpAssign_Remap(pf.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: {
            const pt = op;
            pt.arg = propagateTmpAssign_Remap(pt.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: {
            const pr = op;
            pr.arg = propagateTmpAssign_Remap(pr.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeNominal: {
            const pc = op;
            pc.arg = propagateTmpAssign_Remap(pc.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithIndecies: {
            const mi = op;
            mi.arg = propagateTmpAssign_Remap(mi.arg, propMap);
            mi.updates = propagateTmpAssign_RemapStructuredArgs(mi.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithProperties: {
            const mp = op;
            mp.arg = propagateTmpAssign_Remap(mp.arg, propMap);
            mp.updates = propagateTmpAssign_RemapStructuredArgs(mp.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithFields: {
            const mf = op;
            mf.arg = propagateTmpAssign_Remap(mf.arg, propMap);
            mf.updates = propagateTmpAssign_RemapStructuredArgs(mf.updates, (u) => [u[0], propagateTmpAssign_Remap(u[1], propMap)]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: {
            const st = op;
            st.arg = propagateTmpAssign_Remap(st.arg, propMap);
            st.update = propagateTmpAssign_Remap(st.update, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: {
            const sr = op;
            sr.arg = propagateTmpAssign_Remap(sr.arg, propMap);
            sr.update = propagateTmpAssign_Remap(sr.update, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendObject: {
            const so = op;
            so.arg = propagateTmpAssign_Remap(so.arg, propMap);
            so.update = propagateTmpAssign_Remap(so.update, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadFromEpehmeralList: {
            const el = op;
            el.arg = propagateTmpAssign_Remap(el.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
            const invk = op;
            invk.args = propagateTmpAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
            const invk = op;
            invk.args = propagateTmpAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPrefixOp: {
            const pfx = op;
            pfx.arg = propagateTmpAssign_Remap(pfx.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinOp: {
            const bop = op;
            bop.lhs = propagateTmpAssign_Remap(bop.lhs, propMap);
            bop.rhs = propagateTmpAssign_Remap(bop.rhs, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinEq: {
            const beq = op;
            beq.lhs = propagateTmpAssign_Remap(beq.lhs, propMap);
            beq.rhs = propagateTmpAssign_Remap(beq.rhs, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinLess: {
            const bl = op;
            bl.lhs = propagateTmpAssign_Remap(bl.lhs, propMap);
            bl.rhs = propagateTmpAssign_Remap(bl.rhs, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinCmp: {
            const bcp = op;
            bcp.lhs = propagateTmpAssign_Remap(bcp.lhs, propMap);
            bcp.rhs = propagateTmpAssign_Remap(bcp.rhs, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
            const ton = op;
            ton.arg = propagateTmpAssign_Remap(ton.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
            const tos = op;
            tos.arg = propagateTmpAssign_Remap(tos.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOf: {
            const tog = op;
            tog.arg = propagateTmpAssign_Remap(tog.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRRegAssign: {
            const regop = op;
            regop.src = propagateTmpAssign_Remap(regop.src, propMap);
            propagateTmpAssign_Bind(regop.trgt, regop.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRTruthyConvert: {
            const tcop = op;
            tcop.src = propagateTmpAssign_Remap(tcop.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRVarStore: {
            const vs = op;
            vs.src = propagateTmpAssign_Remap(vs.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackSlice: {
            const pso = op;
            pso.src = propagateTmpAssign_Remap(pso.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackExtend: {
            const pse = op;
            pse.basepack = propagateTmpAssign_Remap(pse.basepack, propMap);
            pse.ext = propagateTmpAssign_RemapArgs(pse.ext, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRReturnAssign: {
            const ra = op;
            ra.src = propagateTmpAssign_Remap(ra.src, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAbort: {
            break;
        }
        case mir_ops_1.MIROpTag.MIRDebug: {
            const dbg = op;
            if (dbg.value !== undefined) {
                dbg.value = propagateTmpAssign_Remap(dbg.value, propMap);
            }
            break;
        }
        case mir_ops_1.MIROpTag.MIRJump: {
            break;
        }
        case mir_ops_1.MIROpTag.MIRJumpCond: {
            const cjop = op;
            cjop.arg = propagateTmpAssign_Remap(cjop.arg, propMap);
            break;
        }
        case mir_ops_1.MIROpTag.MIRJumpNone: {
            const njop = op;
            njop.arg = propagateTmpAssign_Remap(njop.arg, propMap);
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
function propagateTmpAssignForBody(body) {
    if (typeof (body) === "string") {
        return;
    }
    body.body.forEach((blk) => {
        let propMap = new Map();
        for (let i = 0; i < blk.ops.length; ++i) {
            propagateTmpAssignForOp(blk.ops[i], propMap);
        }
    });
}
exports.propagateTmpAssignForBody = propagateTmpAssignForBody;
function computeTmpUseForBody(body) {
    if (typeof (body) === "string") {
        return new Set();
    }
    let usedTemps = new Set();
    body.body.forEach((blk) => {
        for (let i = 0; i < blk.ops.length; ++i) {
            const optmps = blk.ops[i].getUsedVars().filter((arg) => arg instanceof mir_ops_1.MIRTempRegister);
            for (let j = 0; j < optmps.length; ++j) {
                usedTemps.add(optmps[j].regID);
            }
        }
    });
    return usedTemps;
}
function isDeadTempAssign(op, liveTemps) {
    switch (op.tag) {
        case mir_ops_1.MIROpTag.MIRLoadConst:
        case mir_ops_1.MIROpTag.MIRAccessArgVariable:
        case mir_ops_1.MIROpTag.MIRAccessLocalVariable:
        case mir_ops_1.MIROpTag.MIRRegAssign: {
            return op.getModVars().every((mv) => mv instanceof mir_ops_1.MIRTempRegister && !liveTemps.has(mv.regID));
        }
        default:
            return false;
    }
}
function removeDeadTempAssignsFromBody(body) {
    if (typeof (body) === "string") {
        return;
    }
    let oldLiveSize = Number.MAX_SAFE_INTEGER;
    let liveTemps = computeTmpUseForBody(body);
    while (liveTemps.size < oldLiveSize) {
        let nbody = new Map();
        body.body.forEach((blk, id) => {
            const ops = blk.ops.filter((op) => !isDeadTempAssign(op, liveTemps));
            nbody.set(id, new mir_ops_1.MIRBasicBlock(id, ops));
        });
        body.body = nbody;
        oldLiveSize = liveTemps.size;
        liveTemps = computeTmpUseForBody(body);
    }
}
exports.removeDeadTempAssignsFromBody = removeDeadTempAssignsFromBody;
//# sourceMappingURL=mir_cleanup.js.map