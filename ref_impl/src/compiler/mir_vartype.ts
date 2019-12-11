//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRLoadConstTypedString, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorPrimary, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRProjectFromIndecies, MIRAccessFromProperty, MIRProjectFromProperties, MIRAccessFromField, MIRProjectFromFields, MIRProjectFromTypeTuple, MIRProjectFromTypeRecord, MIRProjectFromTypeConcept, MIRModifyWithIndecies, MIRModifyWithProperties, MIRModifyWithFields, MIRStructuredExtendTuple, MIRStructuredExtendRecord, MIRStructuredExtendObject, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRIsTypeOf, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRPhi, MIRBody, MIRResolvedTypeKey, MIRGetKey } from "./mir_ops";
import { MIRType, MIRAssembly, MIRConstantDecl, MIRFieldDecl } from "./mir_assembly";
import assert = require("assert");
import { topologicalOrder } from "./mir_info";

function getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>, assembly: MIRAssembly): MIRType {
    if (arg instanceof MIRRegisterArgument) {
        return vtypes.get(arg.nameID) as MIRType;
    }
    else {
        if (arg instanceof MIRConstantNone) {
            return assembly.typeMap.get("NSCore::None") as MIRType;
        }
        else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
            return assembly.typeMap.get("NSCore::Bool") as MIRType;
        }
        else if (arg instanceof MIRConstantInt) {
            return assembly.typeMap.get("NSCore::Int") as MIRType;
        }
        else {
            return assembly.typeMap.get("NSCore::String") as MIRType;
        }
    }
}

function extendVariableTypeMapForOp(op: MIROp, vtypes: Map<string, MIRType>, assembly: MIRAssembly, cinvokeResult: MIRType) {
    switch (op.tag) {
        case MIROpTag.MIRLoadConst: {
            const lcv = op as MIRLoadConst;
            vtypes.set(lcv.trgt.nameID, getArgType(lcv.src, vtypes, assembly));
            break;
        }
        case MIROpTag.MIRLoadConstTypedString:  {
            const lts = op as MIRLoadConstTypedString;
            vtypes.set(lts.trgt.nameID, assembly.typeMap.get(lts.tskey) as MIRType);
            break;
        }
        case MIROpTag.MIRAccessConstantValue: {
            const acv = op as MIRAccessConstantValue;
            vtypes.set(acv.trgt.nameID, assembly.typeMap.get((assembly.constantDecls.get(acv.ckey) as MIRConstantDecl).declaredType) as MIRType);
            break;
        }
        case MIROpTag.MIRLoadFieldDefaultValue: {
            const ldv = op as MIRLoadFieldDefaultValue;
            vtypes.set(ldv.trgt.nameID, assembly.typeMap.get((assembly.fieldDecls.get(ldv.fkey) as MIRFieldDecl).declaredType) as MIRType);
            break;
        }
        case MIROpTag.MIRAccessArgVariable: {
            const lav = op as MIRAccessArgVariable;
            vtypes.set(lav.trgt.nameID, getArgType(lav.name, vtypes, assembly));
            break;
        }
        case MIROpTag.MIRAccessLocalVariable: {
            const llv = op as MIRAccessLocalVariable;
            vtypes.set(llv.trgt.nameID, getArgType(llv.name, vtypes, assembly));
            break;
        }
        case MIROpTag.MIRConstructorPrimary: {
            const cp = op as MIRConstructorPrimary;
            vtypes.set(cp.trgt.nameID, assembly.typeMap.get(cp.tkey) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            const cpce = op as MIRConstructorPrimaryCollectionEmpty;
            vtypes.set(cpce.trgt.nameID, assembly.typeMap.get(cpce.tkey) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
            vtypes.set(cpcs.trgt.nameID, assembly.typeMap.get(cpcs.tkey) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cpcc = op as MIRConstructorPrimaryCollectionCopies;
            vtypes.set(cpcc.trgt.nameID, assembly.typeMap.get(cpcc.tkey) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cpcm = op as MIRConstructorPrimaryCollectionMixed;
            vtypes.set(cpcm.trgt.nameID, assembly.typeMap.get(cpcm.tkey) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            vtypes.set(tc.trgt.nameID, assembly.typeMap.get(tc.resultTupleType) as MIRType);
            break;
        }
        case MIROpTag.MIRConstructorRecord: {
            const tr = op as MIRConstructorRecord;
            vtypes.set(tr.trgt.nameID, assembly.typeMap.get(tr.resultRecordType) as MIRType);
            break;
        }
        case MIROpTag.MIRAccessFromIndex: {
            const ai = op as MIRAccessFromIndex;
            vtypes.set(ai.trgt.nameID, assembly.typeMap.get(ai.resultAccessType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            const pi = op as MIRProjectFromIndecies;
            vtypes.set(pi.trgt.nameID, assembly.typeMap.get(pi.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRAccessFromProperty: {
            const ap = op as MIRAccessFromProperty;
            vtypes.set(ap.trgt.nameID, assembly.typeMap.get(ap.resultAccessType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromProperties: {
            const pp = op as MIRProjectFromProperties;
            vtypes.set(pp.trgt.nameID, assembly.typeMap.get(pp.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRAccessFromField: {
            const af = op as MIRAccessFromField;
            vtypes.set(af.trgt.nameID, assembly.typeMap.get(af.resultAccessType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromFields: {
            const pf = op as MIRProjectFromFields;
            vtypes.set(pf.trgt.nameID, assembly.typeMap.get(pf.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            const ptt = op as MIRProjectFromTypeTuple;
            vtypes.set(ptt.trgt.nameID, assembly.typeMap.get(ptt.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            const prt = op as MIRProjectFromTypeRecord;
            vtypes.set(prt.trgt.nameID, assembly.typeMap.get(prt.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            const pct = op as MIRProjectFromTypeConcept;
            vtypes.set(pct.trgt.nameID, assembly.typeMap.get(pct.resultProjectType) as MIRType);
            break;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            const mi = op as MIRModifyWithIndecies;
            vtypes.set(mi.trgt.nameID, assembly.typeMap.get(mi.resultTupleType) as MIRType);
            break;
        }
        case MIROpTag.MIRModifyWithProperties: {
            const mp = op as MIRModifyWithProperties;
            vtypes.set(mp.trgt.nameID, assembly.typeMap.get(mp.resultRecordType) as MIRType);
            break;
        }
        case MIROpTag.MIRModifyWithFields: {
            const mf = op as MIRModifyWithFields;
            vtypes.set(mf.trgt.nameID, assembly.typeMap.get(mf.resultNominalType) as MIRType);
            break;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            const et = op as MIRStructuredExtendTuple;
            vtypes.set(et.trgt.nameID, assembly.typeMap.get(et.resultTupleType) as MIRType);
            break;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            const er = op as MIRStructuredExtendRecord;
            vtypes.set(er.trgt.nameID, assembly.typeMap.get(er.resultRecordType) as MIRType);
            break;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            const eo = op as MIRStructuredExtendObject;
            vtypes.set(eo.trgt.nameID, assembly.typeMap.get(eo.resultNominalType) as MIRType);
            break;
        }
        case MIROpTag.MIRInvokeFixedFunction: {
            const invk = op as MIRInvokeFixedFunction;
            vtypes.set(invk.trgt.nameID, assembly.typeMap.get(invk.resultType) as MIRType);
            break;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            const eo = op as MIRInvokeVirtualFunction;
            vtypes.set(eo.trgt.nameID, assembly.typeMap.get(eo.resultType) as MIRType);
            break;
        }
        case MIROpTag.MIRPrefixOp: {
            const pfx = op as MIRPrefixOp;
            if (pfx.op === "!") {
                vtypes.set(pfx.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            }
            else {
                vtypes.set(pfx.trgt.nameID, assembly.typeMap.get("NSCore::Int") as MIRType);
            }
            break;
        }
        case MIROpTag.MIRBinOp: {
            const bop = op as MIRBinOp;
            vtypes.set(bop.trgt.nameID, assembly.typeMap.get("NSCore::Int") as MIRType);
            break;
        }
        case MIROpTag.MIRGetKey: {
            const mgk = op as MIRGetKey;
            vtypes.set(mgk.trgt.nameID, assembly.typeMap.get(mgk.resultKeyType) as MIRType);
            break;
        }
        case MIROpTag.MIRBinEq: {
            const beq = op as MIRBinEq;
            vtypes.set(beq.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRBinCmp: {
            const bcmp = op as MIRBinCmp;
            vtypes.set(bcmp.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRIsTypeOfNone: {
            const ton = op as MIRIsTypeOfNone;
            vtypes.set(ton.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            const tos = op as MIRIsTypeOfSome;
            vtypes.set(tos.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRIsTypeOf: {
            const tof = op as MIRIsTypeOf;
            vtypes.set(tof.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRRegAssign: {
            const regop = op as MIRRegAssign;
            vtypes.set(regop.trgt.nameID, getArgType(regop.src, vtypes, assembly));
            break;
        }
        case MIROpTag.MIRTruthyConvert: {
            const tcop = op as MIRTruthyConvert;
            vtypes.set(tcop.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRLogicStore: {
            const llop = op as MIRLogicStore;
            vtypes.set(llop.trgt.nameID, assembly.typeMap.get("NSCore::Bool") as MIRType);
            break;
        }
        case MIROpTag.MIRVarStore: {
            const vsop = op as MIRVarStore;
            vtypes.set(vsop.name.nameID, getArgType(vsop.src, vtypes, assembly));
            break;
        }
        case MIROpTag.MIRReturnAssign: {
            const raop = op as MIRReturnAssign;
            vtypes.set(raop.name.nameID, cinvokeResult);
            break;
        }
        case MIROpTag.MIRAbort:
        case MIROpTag.MIRDebug:
        case MIROpTag.MIRJump:
        case MIROpTag.MIRJumpCond:
        case MIROpTag.MIRJumpNone: {
            //Nothing to do
            break;
        }
        case MIROpTag.MIRPhi: {
            const pop = op as MIRPhi;
            const vopts = [...pop.src].map((avar) => getArgType(avar[1], vtypes, assembly));

            const mtype = assembly.registerUnionTypeIfNeeded(vopts);
            vtypes.set(pop.trgt.nameID, mtype);
        }
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            //Nothing to do
            break;
        }
        default:
            assert(false);
            break;
    }
}

function extendVarTypeMapForBody(body: MIRBody, invresult: MIRType, vtypes: Map<string, MIRType>, assembly: MIRAssembly) {
    const btopo = topologicalOrder(body.body);
    for (let j = 0; j < btopo.length; ++j) {
        for (let i = 0; i < btopo[j].ops.length; ++i) {
            extendVariableTypeMapForOp(btopo[j].ops[i], vtypes, assembly, invresult);
        }
    }
}

function computeVarTypesForInvoke(body: MIRBody, params: Map<string, MIRType>, resulttype: MIRType, assembly: MIRAssembly) {
    let vmirtypes = new Map<string, MIRType>();
    params.forEach((vtype, vname) => vmirtypes.set(vname, vtype));

    extendVarTypeMapForBody(body, resulttype as MIRType, vmirtypes, assembly);

    let vtypes = new Map<string, MIRResolvedTypeKey>();
    vmirtypes.forEach((mtype, vname) => vtypes.set(vname, mtype.trkey));
    body.vtypes = vtypes;
}

export {
    computeVarTypesForInvoke
};
