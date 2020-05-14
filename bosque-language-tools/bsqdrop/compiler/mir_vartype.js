"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_ops_1 = require("./mir_ops");
const assert = require("assert");
const mir_info_1 = require("./mir_info");
function getArgType(arg, vtypes, assembly) {
    if (arg instanceof mir_ops_1.MIRRegisterArgument) {
        return vtypes.get(arg.nameID);
    }
    else {
        if (arg instanceof mir_ops_1.MIRConstantNone) {
            return assembly.typeMap.get("NSCore::None");
        }
        else if (arg instanceof mir_ops_1.MIRConstantTrue || arg instanceof mir_ops_1.MIRConstantFalse) {
            return assembly.typeMap.get("NSCore::Bool");
        }
        else if (arg instanceof mir_ops_1.MIRConstantInt) {
            return assembly.typeMap.get("NSCore::Int");
        }
        else if (arg instanceof mir_ops_1.MIRConstantBigInt) {
            return assembly.typeMap.get("NSCore::BigInt");
        }
        else if (arg instanceof mir_ops_1.MIRConstantFloat64) {
            return assembly.typeMap.get("NSCore::Float64");
        }
        else {
            return assembly.typeMap.get("NSCore::String");
        }
    }
}
function extendVariableTypeMapForOp(op, vtypes, assembly, cinvokeResult) {
    switch (op.tag) {
        case mir_ops_1.MIROpTag.MIRLoadConst: {
            const lcv = op;
            vtypes.set(lcv.trgt.nameID, getArgType(lcv.src, vtypes, assembly));
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadConstRegex: {
            const lcr = op;
            vtypes.set(lcr.trgt.nameID, assembly.typeMap.get("NSCore::Regex"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadConstSafeString: {
            const lvs = op;
            vtypes.set(lvs.trgt.nameID, assembly.typeMap.get(lvs.tskey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
            const lts = op;
            vtypes.set(lts.trgt.nameID, assembly.typeMap.get(lts.tskey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
            const acv = op;
            vtypes.set(acv.trgt.nameID, assembly.typeMap.get(assembly.constantDecls.get(acv.ckey).declaredType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
            const ldv = op;
            vtypes.set(ldv.trgt.nameID, assembly.typeMap.get(assembly.fieldDecls.get(ldv.fkey).declaredType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessArgVariable: {
            const lav = op;
            vtypes.set(lav.trgt.nameID, getArgType(lav.name, vtypes, assembly));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
            const llv = op;
            vtypes.set(llv.trgt.nameID, getArgType(llv.name, vtypes, assembly));
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckDirect: {
            const cp = op;
            vtypes.set(cp.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
            const cp = op;
            vtypes.set(cp.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
            const cp = op;
            vtypes.set(cp.trgt.nameID, assembly.typeMap.get(cp.tkey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            const cpce = op;
            vtypes.set(cpce.trgt.nameID, assembly.typeMap.get(cpce.tkey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cpcs = op;
            vtypes.set(cpcs.trgt.nameID, assembly.typeMap.get(cpcs.tkey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cpcc = op;
            vtypes.set(cpcc.trgt.nameID, assembly.typeMap.get(cpcc.tkey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cpcm = op;
            vtypes.set(cpcm.trgt.nameID, assembly.typeMap.get(cpcm.tkey));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorTuple: {
            const tc = op;
            vtypes.set(tc.trgt.nameID, assembly.typeMap.get(tc.resultTupleType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorRecord: {
            const tr = op;
            vtypes.set(tr.trgt.nameID, assembly.typeMap.get(tr.resultRecordType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRConstructorEphemeralValueList: {
            const el = op;
            vtypes.set(el.trgt.nameID, assembly.typeMap.get(el.resultEphemeralListType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
            const ai = op;
            vtypes.set(ai.trgt.nameID, assembly.typeMap.get(ai.resultAccessType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
            const pi = op;
            vtypes.set(pi.trgt.nameID, assembly.typeMap.get(pi.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
            const ap = op;
            vtypes.set(ap.trgt.nameID, assembly.typeMap.get(ap.resultAccessType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
            const pp = op;
            vtypes.set(pp.trgt.nameID, assembly.typeMap.get(pp.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRAccessFromField: {
            const af = op;
            vtypes.set(af.trgt.nameID, assembly.typeMap.get(af.resultAccessType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromFields: {
            const pf = op;
            vtypes.set(pf.trgt.nameID, assembly.typeMap.get(pf.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: {
            const ptt = op;
            vtypes.set(ptt.trgt.nameID, assembly.typeMap.get(ptt.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: {
            const prt = op;
            vtypes.set(prt.trgt.nameID, assembly.typeMap.get(prt.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRProjectFromTypeNominal: {
            const pct = op;
            vtypes.set(pct.trgt.nameID, assembly.typeMap.get(pct.resultProjectType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithIndecies: {
            const mi = op;
            vtypes.set(mi.trgt.nameID, assembly.typeMap.get(mi.resultTupleType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithProperties: {
            const mp = op;
            vtypes.set(mp.trgt.nameID, assembly.typeMap.get(mp.resultRecordType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRModifyWithFields: {
            const mf = op;
            vtypes.set(mf.trgt.nameID, assembly.typeMap.get(mf.resultNominalType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: {
            const et = op;
            vtypes.set(et.trgt.nameID, assembly.typeMap.get(et.resultTupleType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: {
            const er = op;
            vtypes.set(er.trgt.nameID, assembly.typeMap.get(er.resultRecordType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRStructuredExtendObject: {
            const eo = op;
            vtypes.set(eo.trgt.nameID, assembly.typeMap.get(eo.resultNominalType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRLoadFromEpehmeralList: {
            const elv = op;
            vtypes.set(elv.trgt.nameID, assembly.typeMap.get(elv.argInferType).options[0].entries[elv.idx]);
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
            const invk = op;
            vtypes.set(invk.trgt.nameID, assembly.typeMap.get(invk.resultType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
            const eo = op;
            vtypes.set(eo.trgt.nameID, assembly.typeMap.get(eo.resultType));
            break;
        }
        case mir_ops_1.MIROpTag.MIRPrefixOp: {
            const pfx = op;
            if (pfx.op === "!") {
                vtypes.set(pfx.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            }
            else {
                vtypes.set(pfx.trgt.nameID, assembly.typeMap.get("NSCore::Int"));
            }
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinOp: {
            const bop = op;
            vtypes.set(bop.trgt.nameID, assembly.typeMap.get("NSCore::Int"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinEq: {
            const beq = op;
            vtypes.set(beq.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinLess: {
            const beq = op;
            vtypes.set(beq.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRBinCmp: {
            const bcmp = op;
            vtypes.set(bcmp.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
            const ton = op;
            vtypes.set(ton.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
            const tos = op;
            vtypes.set(tos.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRIsTypeOf: {
            const tof = op;
            vtypes.set(tof.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRRegAssign: {
            const regop = op;
            vtypes.set(regop.trgt.nameID, getArgType(regop.src, vtypes, assembly));
            break;
        }
        case mir_ops_1.MIROpTag.MIRTruthyConvert: {
            const tcop = op;
            vtypes.set(tcop.trgt.nameID, assembly.typeMap.get("NSCore::Bool"));
            break;
        }
        case mir_ops_1.MIROpTag.MIRVarStore: {
            const vsop = op;
            vtypes.set(vsop.name.nameID, getArgType(vsop.src, vtypes, assembly)); //ok since we are in SSA!
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackSlice: {
            const pso = op;
            vtypes.set(pso.trgt.nameID, assembly.typeMap.get(pso.sltype));
            break;
        }
        case mir_ops_1.MIROpTag.MIRPackExtend: {
            const pse = op;
            vtypes.set(pse.trgt.nameID, assembly.typeMap.get(pse.sltype));
            break;
        }
        case mir_ops_1.MIROpTag.MIRReturnAssign: {
            const raop = op;
            vtypes.set(raop.name.nameID, cinvokeResult);
            break;
        }
        case mir_ops_1.MIROpTag.MIRAbort:
        case mir_ops_1.MIROpTag.MIRDebug:
        case mir_ops_1.MIROpTag.MIRJump:
        case mir_ops_1.MIROpTag.MIRJumpCond:
        case mir_ops_1.MIROpTag.MIRJumpNone: {
            //Nothing to do
            break;
        }
        case mir_ops_1.MIROpTag.MIRPhi: {
            const pop = op;
            const vopts = [...pop.src].map((avar) => getArgType(avar[1], vtypes, assembly));
            const mtype = assembly.registerUnionTypeIfNeeded(vopts);
            vtypes.set(pop.trgt.nameID, mtype);
            break;
        }
        case mir_ops_1.MIROpTag.MIRVarLifetimeStart:
        case mir_ops_1.MIROpTag.MIRVarLifetimeEnd: {
            //Nothing to do
            break;
        }
        default:
            assert(false);
            break;
    }
}
function extendVarTypeMapForBody(body, invresult, vtypes, assembly) {
    const btopo = mir_info_1.topologicalOrder(body.body);
    for (let j = 0; j < btopo.length; ++j) {
        for (let i = 0; i < btopo[j].ops.length; ++i) {
            extendVariableTypeMapForOp(btopo[j].ops[i], vtypes, assembly, invresult);
        }
    }
}
function computeVarTypesForInvoke(body, params, resulttype, assembly) {
    let vmirtypes = new Map();
    vmirtypes.set("$$return", resulttype);
    params.forEach((vtype, vname) => vmirtypes.set(vname, vtype));
    extendVarTypeMapForBody(body, resulttype, vmirtypes, assembly);
    let vtypes = new Map();
    vmirtypes.forEach((mtype, vname) => vtypes.set(vname, mtype.trkey));
    body.vtypes = vtypes;
}
exports.computeVarTypesForInvoke = computeVarTypesForInvoke;
//# sourceMappingURL=mir_vartype.js.map