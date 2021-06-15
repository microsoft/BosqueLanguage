//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRFieldKey, MIRInvokeKey, MIRResolvedTypeKey, MIRVirtualMethodKey } from "../../../compiler/mir_ops";
import { ICPP_WORD_SIZE, SourceInfo, UNIVERSAL_SIZE } from "./icpp_assembly";

enum ArgumentTag
{
    InvalidOp = 0x0,
    Const,
    LocalScalar,
    LocalMixed,
    Argument
}

const EMPTY_CONST_POSITION = 0;
const NONE_VALUE_POSITION = + UNIVERSAL_SIZE;
const TRUE_VALUE_POSITION = NONE_VALUE_POSITION + ICPP_WORD_SIZE;
const FALSE_VALUE_POSITION = TRUE_VALUE_POSITION + ICPP_WORD_SIZE;

enum OpCodeTag
{
    Invalid = 0x0,
    DeadFlowOp,
    AbortOp,
    AssertOp,
    DebugOp,
    LoadUnintVariableValueOp,
    NoneInitUnionOp,
    StoreConstantMaskValueOp,

    DirectAssignOp,
    BoxOp,
    ExtractOp,

    LoadConstOp,
    TupleHasIndexOp,
    RecordHasPropertyOp,
    LoadTupleIndexDirectOp,
    LoadTupleIndexVirtualOp,
    LoadTupleIndexSetGuardDirectOp,
    LoadTupleIndexSetGuardVirtualOp,
    LoadRecordPropertyDirectOp,
    LoadRecordPropertyVirtualOp,
    LoadRecordPropertySetGuardDirectOp,
    LoadRecordPropertySetGuardVirtualOp,
    LoadEntityFieldDirectOp,
    LoadEntityFieldVirtualOp,

    ProjectTupleOp,
    ProjectRecordOp,
    ProjectEntityOp,
    UpdateTupleOp,
    UpdateRecordOp,
    UpdateEntityOp,
    LoadFromEpehmeralListOp,
    MultiLoadFromEpehmeralListOp,
    SliceEphemeralListOp,

    InvokeFixedFunctionOp,
    InvokeVirtualFunctionOp,
    InvokeVirtualOperatorOp,

    ConstructorTupleOp,
    ConstructorTupleFromEphemeralListOp,
    ConstructorRecordOp,
    EphemeralListExtendOp,
    ConstructorRecordFromEphemeralListOp,
    ConstructorEphemeralListOp,
    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp,
    PrefixNotOp,
    AllTrueOp,
    SomeTrueOp,

    BinKeyEqFastOp,
    BinKeyEqStaticOp,
    BinKeyEqVirtualOp,
    BinKeyLessFastOp,
    BinKeyLessStaticOp,
    BinKeyLessVirtualOp,

    TypeIsNoneOp,
    TypeIsSomeOp,
    TypeTagIsOp,
    TypeTagSubtypeOfOp,
    
    JumpOp,
    JumpCondOp,
    JumpNoneOp,

    RegisterAssignOp,
    ReturnAssignOp,
    ReturnAssignOfConsOp,
    VarLifetimeStartOp,
    VarLifetimeEndOp,

    NegateIntOp,
    NegateBigIntOp,
    NegateRationalOp,
    NegateFloatOp,
    NegateDecimalOp,
    AddNatOp,
    AddIntOp,
    AddBigNatOp,
    AddBigIntOp,
    AddRationalOp,
    AddFloatOp,
    AddDecimalOp,
    SubNatOp,
    SubIntOp,
    SubBigNatOp,
    SubBigIntOp,
    SubRationalOp,
    SubFloatOp,
    SubDecimalOp,
    MultNatOp,
    MultIntOp,
    MultBigNatOp,
    MultBigIntOp,
    MultRationalOp,
    MultFloatOp,
    MultDecimalOp,
    DivNatOp,
    DivIntOp,
    DivBigNatOp,
    DivBigIntOp,
    DivRationalOp,
    DivFloatOp,
    DivDecimalOp,

    EqNatOp,
    EqIntOp,
    EqBigNatOp,
    EqBigIntOp,
    EqRationalOp,
    NeqNatOp,
    NeqIntOp,
    NeqBigNatOp,
    NeqBigIntOp,
    NeqRationalOp,

    LtNatOp,
    LtIntOp,
    LtBigNatOp,
    LtBigIntOp,
    LtRationalOp,
    LtFloatOp,
    LtDecimalOp,
    GtNatOp,
    GtIntOp,
    GtBigNatOp,
    GtBigIntOp,
    GtRationalOp,
    GtFloatOp,
    GtDecimalOp,

    LeNatOp,
    LeIntOp,
    LeBigNatOp,
    LeBigIntOp,
    LeRationalOp,
    LeFloatOp,
    LeDecimalOp,
    GeNatOp,
    GeIntOp,
    GeBigNatOp,
    GeBigIntOp,
    GeRationalOp,
    GeFloatOp,
    GeDecimalOp,

    EqStrPosOp,
    NeqStrPosOp,
    LtStrPosOp,
    GtStrPosOp,
    LeStrPosOp,
    GeStrPosOp,
}

type Argument = {
    kind: ArgumentTag;
    location: number;
};

type TargetVar = {
    kind: ArgumentTag;
    offset: number;
};

type ICPPGuard = {
    gmaskoffset: number; 
    gindex: number; //-1 if this is var guard

    gvaroffset: number; //if gindex is -1
};

type ICPPStatementGuard = {
    guard: ICPPGuard;
    usedefaulton: boolean;
    defaultvar: Argument;
    enabled: boolean;
};

type ICPPOp = object;

class ICPPOpEmitter
{
    static genConstArgument(offset: number): Argument {
        return { kind: ArgumentTag.Const, location: offset };
    }

    static genLocalScalarArgument(offset: number): Argument {
        return { kind: ArgumentTag.LocalScalar, location: offset };
    }

    static genLocalMixedArgument(offset: number): Argument {
        return { kind: ArgumentTag.LocalMixed, location: offset };
    }

    static genParameterArgument(offset: number): Argument {
        return { kind: ArgumentTag.Argument, location: offset };
    }

    static genMaskGuard(gindex: number, goffset: number): ICPPGuard {
        return { gmaskoffset: goffset, gindex: gindex, gvaroffset: -1 };
    }

    static genVarGuard(gvaroffset: number): ICPPGuard {
        return { gmaskoffset: -1, gindex: -1, gvaroffset: gvaroffset };
    }

    static genNoStatmentGuard(): ICPPStatementGuard {
        return { guard: { gmaskoffset: -1, gindex: -1, gvaroffset: -1 }, usedefaulton: true, defaultvar: { kind: ArgumentTag.InvalidOp, location: 0 }, enabled: false };
    }

    static genStatmentGuard(guard: ICPPGuard, usedefaultwhen: boolean, defaultvar: Argument): ICPPStatementGuard {
        return { guard: guard, usedefaulton: usedefaultwhen, defaultvar: defaultvar, enabled: true };
    }

    static genDeadFlowOp(sinfo: SourceInfo): ICPPOp {
        return {tag: OpCodeTag.DeadFlowOp, sinfo: sinfo};
    }

    static genAbortOp(sinfo: SourceInfo, msg: string): ICPPOp {
        return {tag: OpCodeTag.AbortOp, sinfo: sinfo, msg: msg};
    }

    static genAssertOp(sinfo: SourceInfo, arg: Argument, msg: String): ICPPOp {
        return {tag: OpCodeTag.AssertOp, sinfo: sinfo, arg: arg, msg: msg};
    }
    
    static genDebugOp(sinfo: SourceInfo, arg: Argument): ICPPOp {
        return {tag: OpCodeTag.DebugOp, sinfo: sinfo, arg: arg};
    }

    static genLoadUnintVariableValueOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.LoadUnintVariableValueOp, sinfo: sinfo, trgt: trgt, oftype: oftype};
    }

    static genNoneInitUnionOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.NoneInitUnionOp, sinfo: sinfo, trgt: trgt, oftype: oftype};
    }

    static genStoreConstantMaskValueOp(sinfo: SourceInfo, gmaskoffset: number, gindex: number, flag: boolean): ICPPOp {
        return {tag: OpCodeTag.StoreConstantMaskValueOp, sinfo: sinfo, gmaskoffset: gmaskoffset, gindex: gindex, flag: flag};
    }

    static genDirectAssignOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.DirectAssignOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, sguard: sguard};
    }

    static genBoxOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.BoxOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genExtractOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.ExtractOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genLoadConstOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.LoadConstOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype};
    }

    static genTupleHasIndexOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, layouttype: MIRResolvedTypeKey, idx: number): ICPPOp {
        return {tag: OpCodeTag.TupleHasIndexOp, sinfo: sinfo, trgt: trgt, arg: arg, layouttype: layouttype, idx: idx};
    }

    static genRecordHasPropertyOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, layouttype: MIRResolvedTypeKey, propId: string): ICPPOp {
        return {tag: OpCodeTag.RecordHasPropertyOp, sinfo: sinfo, trgt: trgt, arg: arg, layouttype: layouttype, propId: propId};
    }

    static genLoadTupleIndexDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, idx: number): ICPPOp {
        return {tag: OpCodeTag.LoadTupleIndexDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, idx: idx};
    }

    static genLoadTupleIndexVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, idx: number): ICPPOp {
        return {tag: OpCodeTag.LoadTupleIndexSetGuardVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, idx: idx};
    }

    static genLoadTupleIndexSetGuardDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, idx: number, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadTupleIndexSetGuardDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, idx: idx, guard: guard};
    }

    static genLoadTupleIndexSetGuardVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, idx: number, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadTupleIndexSetGuardVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, idx: idx, guard: guard};
    }

    static genLoadRecordPropertyDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, propId: string): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertyDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, propId: propId};
    }

    static genLoadRecordPropertyVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, propId: string): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertyVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, propId: propId};
    }

    static genLoadRecordPropertySetGuardDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, propId: string, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertySetGuardDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, propId: propId, guard: guard};
    }

    static genLoadRecordPropertySetGuardVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, propId: string, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertySetGuardVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, propId: propId, guard: guard};
    }

    static genLoadEntityFieldDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, fieldId: MIRFieldKey): ICPPOp {
        return {tag: OpCodeTag.LoadEntityFieldDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, fieldId: fieldId};
    }

    static genLoadEntityFieldVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, fieldId: MIRFieldKey): ICPPOp {
        return {tag: OpCodeTag.LoadEntityFieldVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, fieldId: fieldId};
    }

    static genProjectTupleOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, idxs: [number, number, MIRResolvedTypeKey][]): ICPPOp {
        return {tag: OpCodeTag.ProjectTupleOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, idxs: idxs};
    }

    static genProjectRecordOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, props: [string, number, MIRResolvedTypeKey][]): ICPPOp {
        return {tag: OpCodeTag.ProjectRecordOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, props: props};
    }

    static genProjectEntityOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, fields: [MIRFieldKey, number, MIRResolvedTypeKey][]): ICPPOp {
        return {tag: OpCodeTag.ProjectEntityOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, fields: fields};
    }

    static genUpdateTupleOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, updates: [number, number, MIRResolvedTypeKey, Argument][]): ICPPOp {
        return {tag: OpCodeTag.UpdateTupleOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, updates: updates};
    }

    static genUpdateRecordOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, updates: [string, number, MIRResolvedTypeKey, Argument][]): ICPPOp {
        return {tag: OpCodeTag.UpdateRecordOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, updates: updates};
    }

    static genUpdateEntityOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, flowtype: MIRResolvedTypeKey, updates: [MIRFieldKey, number, MIRResolvedTypeKey, Argument][]): ICPPOp {
        return {tag: OpCodeTag.UpdateEntityOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, flowtype: flowtype, updates: updates};
    }

    static genLoadFromEpehmeralListOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, index: number): ICPPOp {
        return {tag: OpCodeTag.LoadFromEpehmeralListOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, index: index};
    }

    static genMultiLoadFromEpehmeralListOp(sinfo: SourceInfo, trgts: TargetVar[], trgttypes: MIRResolvedTypeKey[], arg: Argument, layouttype: MIRResolvedTypeKey, slotoffsets: number[], indexs: number[]): ICPPOp {
        return {tag: OpCodeTag.MultiLoadFromEpehmeralListOp, sinfo: sinfo, trgts: trgts, trgttypes: trgttypes, arg: arg, layouttype: layouttype, slotoffsets: slotoffsets, indexs: indexs};
    }

    static genSliceEphemeralListOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffsetend: number, indexend: number): ICPPOp {
        return {tag: OpCodeTag.SliceEphemeralListOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffsetend: slotoffsetend, indexend: indexend};
    }

    static genInvokeFixedFunctionOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: MIRInvokeKey, args: Argument[], optmaskoffset: number, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.InvokeFixedFunctionOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args, optmaskoffset: optmaskoffset, sguard: sguard};
    }

    static genInvokeVirtualFunctionOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: MIRVirtualMethodKey, rcvrlayouttype: MIRResolvedTypeKey, args: Argument[], optmaskoffset: number): ICPPOp {
        return {tag: OpCodeTag.InvokeVirtualFunctionOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, rcvrlayouttype: rcvrlayouttype, args: args, optmaskoffset: optmaskoffset};
    }

    static genInvokeVirtualOperatorOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: MIRVirtualMethodKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.InvokeVirtualOperatorOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args};
    }

    static genConstructorTupleOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorTupleOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorTupleFromEphemeralListOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, arg: Argument, argtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ConstructorTupleFromEphemeralListOp, sinfo: sinfo, trgt: trgt, oftype: oftype, arg: arg, argtype: argtype};
    }

    static genConstructorRecordOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorRecordOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorRecordFromEphemeralListOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, arg: Argument, argtype: MIRResolvedTypeKey, proppositions: number[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorRecordFromEphemeralListOp, sinfo: sinfo, trgt: trgt, oftype: oftype, arg: arg, argtype: argtype, proppositions: proppositions};
    }

    static genEphemeralListExtendOp(sinfo: SourceInfo, trgt: TargetVar, resultType: MIRResolvedTypeKey, arg: Argument, argtype: MIRResolvedTypeKey, ext: Argument[]): ICPPOp {
        return {tag: OpCodeTag.EphemeralListExtendOp, sinfo: sinfo, trgt: trgt, resultType: resultType, arg: arg, argtype: argtype, ext: ext};
    }

    static genConstructorEphemeralListOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorEphemeralListOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorPrimaryCollectionEmptyOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ConstructorPrimaryCollectionEmptyOp, sinfo: sinfo, trgt: trgt, oftype: oftype};
    }

    static genConstructorPrimaryCollectionSingletonsOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorPrimaryCollectionSingletonsOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorPrimaryCollectionCopiesOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorPrimaryCollectionCopiesOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorPrimaryCollectionMixedOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorPrimaryCollectionMixedOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genPrefixNotOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument): ICPPOp {
        return {tag: OpCodeTag.PrefixNotOp, sinfo: sinfo, trgt: trgt, arg: arg};
    }

    static genAllTrueOp(sinfo: SourceInfo, trgt: TargetVar, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.AllTrueOp, sinfo: sinfo, trgt: trgt, args: args};
    }

    static genSomeTrueOp(sinfo: SourceInfo, trgt: TargetVar, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.SomeTrueOp, sinfo: sinfo, trgt: trgt, args: args};
    }

    static genBinKeyEqFastOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, argl: Argument, argr: Argument): ICPPOp {
        return {tag: OpCodeTag.BinKeyEqFastOp, sinfo: sinfo, trgt: trgt, oftype: oftype, argl: argl, argr: argr };
    }

    static genBinKeyEqStaticOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, argl: Argument, argllayout: MIRResolvedTypeKey, argr: Argument, argrlayout: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BinKeyEqStaticOp, sinfo: sinfo, trgt: trgt, oftype: oftype, argl: argl, argllayout: argllayout, argr: argr, argrlayout: argrlayout };
    }

    static genBinKeyEqVirtualOp(sinfo: SourceInfo, trgt: TargetVar, argl: Argument, argllayout: MIRResolvedTypeKey, argr: Argument, argrlayout: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BinKeyEqVirtualOp, sinfo: sinfo, trgt: trgt, argl: argl, argllayout: argllayout, argr: argr, argrlayout: argrlayout };
    }
     
    static genBinKeyLessFastOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, argl: Argument, argr: Argument): ICPPOp {
        return {tag: OpCodeTag.BinKeyLessFastOp, sinfo: sinfo, trgt: trgt, oftype: oftype, argl: argl, argr: argr };
    }

    static genBinKeyLessStaticOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, argl: Argument, argllayout: MIRResolvedTypeKey, argr: Argument, argrlayout: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BinKeyLessStaticOp, sinfo: sinfo, trgt: trgt, oftype: oftype, argl: argl, argllayout: argllayout, argr: argr, argrlayout: argrlayout };
    }

    static genBinKeyLessVirtualOp(sinfo: SourceInfo, trgt: TargetVar, argl: Argument, argllayout: MIRResolvedTypeKey, argr: Argument, argrlayout: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BinKeyLessVirtualOp, sinfo: sinfo, trgt: trgt, argl: argl, argllayout: argllayout, argr: argr, argrlayout: argrlayout };
    }

    static genTypeIsNoneOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, arglayout: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.TypeIsNoneOp, sinfo: sinfo, trgt: trgt, arg: arg, arglayout: arglayout, sguard: sguard};
    }

    static genTypeIsSomeOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, arglayout: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.TypeIsSomeOp, sinfo: sinfo, trgt: trgt, arg: arg, arglayout: arglayout, sguard: sguard};
    }

    static genTypeTagIsOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, arg: Argument, arglayout: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.TypeTagIsOp, sinfo: sinfo, trgt: trgt, oftype: oftype, arg: arg, arglayout: arglayout, sguard: sguard};
    }

    static genTypeTagSubtypeOfOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, arg: Argument, arglayout: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.TypeTagSubtypeOfOp, sinfo: sinfo, trgt: trgt, oftype: oftype, arg: arg, arglayout: arglayout, sguard: sguard};
    }
    
    static genJumpOp(sinfo: SourceInfo, offset: number, label: string): ICPPOp {
        return { tag: OpCodeTag.JumpOp, sinfo: sinfo, offset: offset, label: label };
    }

    static genJumpCondOp(sinfo: SourceInfo, arg: Argument, toffset: number, foffset: number, tlabel: string, flabel: string): ICPPOp {
        return { tag: OpCodeTag.JumpCondOp, sinfo: sinfo, arg: arg, toffset: toffset, foffset: foffset, tlabel: tlabel, flabel: flabel };
    }
    
    static genJumpNoneOp(sinfo: SourceInfo, arg: Argument, arglayout: MIRResolvedTypeKey, noffset: number, soffset: number, nlabel: string, slabel: string): ICPPOp {
        return { tag: OpCodeTag.JumpNoneOp, sinfo: sinfo, arg: arg, arglayout: arglayout, noffset: noffset, soffset: soffset, nlabel: nlabel, slabel: slabel};
    }
    
    static genRegisterAssignOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return { tag: OpCodeTag.RegisterAssignOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype, sguard: sguard};
    }
    
    static genReturnAssignOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey): ICPPOp {
        return { tag: OpCodeTag.ReturnAssignOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype };
    }
    
    static genReturnAssignOfConsOp(sinfo: SourceInfo, trgt: TargetVar, args: Argument[], oftype: MIRResolvedTypeKey): ICPPOp {
        return { tag: OpCodeTag.ReturnAssignOfConsOp, sinfo: sinfo, trgt: trgt, args: args, oftype: oftype };
    }
    
    static genVarLifetimeStartOp(sinfo: SourceInfo, homelocation: Argument, oftype: MIRResolvedTypeKey, name: string): ICPPOp {
        return { tag: OpCodeTag.VarLifetimeStartOp, sinfo: sinfo, homelocation: homelocation, oftype: oftype, name: name };
    }
    
    static genVarLifetimeEndOp(sinfo: SourceInfo, name: string): ICPPOp {
        return { tag: OpCodeTag.VarLifetimeEndOp, sinfo: sinfo, name: name };
    }
    
    static genNegateOp(sinfo: SourceInfo, tag: OpCodeTag, trgt: TargetVar, oftype: MIRResolvedTypeKey, arg: Argument): ICPPOp {
        return {tag: tag, sinfo: sinfo, trgt: trgt, oftype: oftype, arg: arg};
    }

    static genBinaryOp(sinfo: SourceInfo, tag: OpCodeTag, trgt: TargetVar, oftype: MIRResolvedTypeKey, larg: Argument, rarg: Argument): ICPPOp {
        return {tag: tag, sinfo: sinfo, trgt: trgt, oftype: oftype, larg: larg, rarg: rarg};
    }

    static genCmpOp(sinfo: SourceInfo, tag: OpCodeTag, trgt: TargetVar, oftype: MIRResolvedTypeKey, larg: Argument, rarg: Argument): ICPPOp {
        return {tag: tag, sinfo: sinfo, trgt: trgt, oftype: oftype, larg: larg, rarg: rarg};
    }
}

export {
    ArgumentTag, OpCodeTag, 
    EMPTY_CONST_POSITION, NONE_VALUE_POSITION, TRUE_VALUE_POSITION, FALSE_VALUE_POSITION, 
    Argument, TargetVar,
    ICPPGuard, ICPPStatementGuard,
    ICPPOp,
    ICPPOpEmitter
};
