//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

enum ArgumentTag
{
    InvalidOp = 0x0,
    ConstNone,
    ConstTrue,
    ConstFalse,
    ConstNat,
    ConstInt,
    ConstBigNat,
    ConstBigInt,
    ConstRational,
    ConstFloat,
    ConstDecimal,
    ConstString,
    ConstStringOf,
    ConstDataString,
    ConstRegex,
    Local,
    Argument,
    GlobalConst,
    UninterpFill
}

enum OpCodeTag
{
    Invalid = 0x0,
    DeadFlowOp,
    AbortOp,
    AssertOp,
    DebugOp,
    LoadUnintVariableValueOp,

    BoxUniqueRegisterToInlineOp,
    BoxUniqueStructOrStringToInlineOp,
    BoxUniqueRefToInlineOp,
    BoxUniqueRegisterToHeapOp,
    BoxUniqueStructOrStringToHeapOp,
    BoxUniqueRefToHeapOp,
    BoxInlineBoxToHeapOp,
    ExtractUniqueRegisterFromInlineOp,
    ExtractUniqueStructOrStringFromInlineOp,
    ExtractUniqueRefFromInlineOp,
    ExtractUniqueRegisterFromHeapOp,
    ExtractUniqueStructOrStringFromHeapOp,
    ExtractUniqueRefFromHeapOp,
    ExtractInlineBoxFromHeapOp,
    WidenInlineOp,
    NarrowInlineOp,
    GuardedBoxUniqueRegisterToInlineOp,
    GuardedBoxUniqueStructOrStringToInlineOp,
    GuardedBoxUniqueRefToInlineOp,
    GuardedBoxUniqueRegisterToHeapOp,
    GuardedBoxUniqueStructOrStringToHeapOp,
    GuardedBoxUniqueRefToHeapOp,
    GuardedBoxInlineBoxToHeapOp,
    GuardedExtractUniqueRegisterFromInlineOp,
    GuardedExtractUniqueStructOrStringFromInlineOp,
    GuardedExtractUniqueRefFromInlineOp,
    GuardedExtractUniqueRegisterFromHeapOp,
    GuardedExtractUniqueStructOrStringFromHeapOp,
    GuardedExtractUniqueRefFromHeapOp,
    GuardedExtractInlineBoxFromHeapOp,
    GuardedWidenInlineOp,
    GuardedNarrowInlineOp,

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
    LoadFromEpehmeralListOp,
    InvokeFixedFunctionOp,
    GuardedInvokeFixedFunctionOp,
    InvokeVirtualFunctionOp,
    InvokeVirtualOperatorOp,
    ConstructorTupleOp,
    ConstructorRecordOp,
    ConstructorEphemeralListOp,
    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp,
    PrefixNotOp,
    AllTrueOp,
    SomeTrueOp,

    BinKeyEqVirtualOp,
    BinKeyLessVirtualOp,

    TypeIsNoneOp,
    TypeIsSomeOp,
    TypeTagIsOp,
    TypeTagSubtypeOfOp,
    GuardedTypeIsNoneOp,
    GuardedTypeIsSomeOp,
    GuardedTypeTagIsOp,
    GuardedTypeTagSubtypeOfOp,
    
    JumpOp,
    JumpCondOp,
    JumpNoneOp,
    RegisterAssignOp,
    GuardedRegisterAssignOp,
    ReturnAssignOp,
    ReturnAssignOfConsOp,
    VarLifetimeStartOp,
    VarLifetimeEndOp,

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
    LtStringOp,
    GtNatOp,
    GtIntOp,
    GtBigNatOp,
    GtBigIntOp,
    GtRationalOp,
    GtFloatOp,
    GtDecimalOp,
    GtStringOp,

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

    EqStringOp,
    NeqStringOp,
    LessStringOp
}

type Argument = {
    kind: ArgumentTag;
    location: number;
};

type TargetVar = {
    offset: number;
};

type SourceInfo = {
    line: number;
    column: number;
};

type BSQGuard = {
    gmaskoffset: number; 
    gindex: number; //-1 if this is var guard

    gvaroffset: number; //if gindex is -1
};

type BSQStatementGuard = {
    guard: BSQGuard;
    usedefaulton: boolean;
    defaultvar: Argument; //may be uninterp fill kind
};

type InterpOp = object;

class InterpOpGenerator
{
    genDeadFlowOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.DeadFlowOp, sinfo: sinfo};
    }

    genAbortOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.AbortOp, sinfo: sinfo};
    }

    genAssertOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.AssertOp, sinfo: sinfo};
    }
    
    genDebugOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.DebugOp, sinfo: sinfo};
    }

    genLoadUnintVariableValueOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.LoadUnintVariableValueOp, sinfo: sinfo};
    }

    genBoxUniqueRegisterToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxUniqueRegisterToInlineOp, sinfo: sinfo};
    }

    genBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToInlineOp, sinfo: sinfo};
    }
    
    genBoxUniqueRefToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxUniqueRefToInlineOp, sinfo: sinfo};
    }

    genBoxUniqueRegisterToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo};
    }

    genBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToHeapOp, sinfo: sinfo};
    }

    genBoxUniqueRefToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxUniqueRefToHeapOp, sinfo: sinfo};
    }

    genBoxInlineBoxToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.BoxInlineBoxToHeapOp, sinfo: sinfo};
    }

    genExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromInlineOp, sinfo: sinfo};
    }

    genExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo};
    }

    genExtractUniqueRefFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromInlineOp, sinfo: sinfo};
    }

    genExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromHeapOp, sinfo: sinfo};
    }
    
    genExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo};
    }

    genExtractUniqueRefFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromHeapOp, sinfo: sinfo};
    }

    genExtractInlineBoxFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.ExtractInlineBoxFromHeapOp, sinfo: sinfo};
    }

    genWidenInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.WidenInlineOp, sinfo: sinfo};
    }

    genNarrowInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.NarrowInlineOp, sinfo: sinfo};
    }
    
    genGuardedBoxUniqueRegisterToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToInlineOp, sinfo: sinfo};
    }

    genGuardedBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToInlineOp, sinfo: sinfo};
    }

    genGuardedBoxUniqueRefToInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToInlineOp, sinfo: sinfo};
    }

    genGuardedBoxUniqueRegisterToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo};
    }

    genGuardedBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToHeapOp, sinfo: sinfo};
    }

    genGuardedBoxUniqueRefToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToHeapOp, sinfo: sinfo};
    }

    genGuardedBoxInlineBoxToHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedBoxInlineBoxToHeapOp, sinfo: sinfo};
    }
    
    genGuardedExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromInlineOp, sinfo: sinfo};
    }
    
    genGuardedExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo};
    }

    genGuardedExtractUniqueRefFromInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromInlineOp, sinfo: sinfo};
    }

    genGuardedExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromHeapOp, sinfo: sinfo};
    }

    genGuardedExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo};
    }
    
    genGuardedExtractUniqueRefFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromHeapOp, sinfo: sinfo};
    }

    genGuardedExtractInlineBoxFromHeapOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedExtractInlineBoxFromHeapOp, sinfo: sinfo};
    }
    
    genGuardedWidenInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedWidenInlineOp, sinfo: sinfo};
    }

    genGuardedNarrowInlineOp(sinfo: SourceInfo): InterpOp {
        return {tag: OpCodeTag.GuardedNarrowInlineOp, sinfo: sinfo};
    }

    /*
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
    LoadFromEpehmeralListOp,
    InvokeFixedFunctionOp,
    GuardedInvokeFixedFunctionOp,
    InvokeVirtualFunctionOp,
    InvokeVirtualOperatorOp,
    ConstructorTupleOp,
    ConstructorRecordOp,
    ConstructorEphemeralListOp,
    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp,
    PrefixNotOp,
    AllTrueOp,
    SomeTrueOp,

    BinKeyEqVirtualOp,
    BinKeyLessVirtualOp,

    TypeIsNoneOp,
    TypeIsSomeOp,
    TypeTagIsOp,
    TypeTagSubtypeOfOp,
    GuardedTypeIsNoneOp,
    GuardedTypeIsSomeOp,
    GuardedTypeTagIsOp,
    GuardedTypeTagSubtypeOfOp,
    
    JumpOp,
    JumpCondOp,
    JumpNoneOp,
    RegisterAssignOp,
    GuardedRegisterAssignOp,
    ReturnAssignOp,
    ReturnAssignOfConsOp,
    VarLifetimeStartOp,
    VarLifetimeEndOp,

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
    LtStringOp,
    GtNatOp,
    GtIntOp,
    GtBigNatOp,
    GtBigIntOp,
    GtRationalOp,
    GtFloatOp,
    GtDecimalOp,
    GtStringOp,

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

    EqStringOp,
    NeqStringOp,
    LessStringOp
    */
}

export {
    ArgumentTag, OpCodeTag, 
    Argument, TargetVar, SourceInfo,
    BSQGuard, BSQStatementGuard,
    InterpOp,
    InterpOpGenerator
};
