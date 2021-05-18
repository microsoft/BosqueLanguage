//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRResolvedTypeKey } from "../../../compiler/mir_ops";

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
    DirectAssignRegisterOp,
    DirectAssignValueOp,
    DirectAssignRefOp,
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
    GuardedDirectAssignRegisterOp,
    GuardedDirectAssignValueOp,
    GuardedDirectAssignRefOp,
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

type ICCPGuard = {
    gmaskoffset: number; 
    gindex: number; //-1 if this is var guard

    gvaroffset: number; //if gindex is -1
};

type ICCPStatementGuard = {
    guard: ICCPGuard;
    usedefaulton: boolean;
    defaultvar: Argument; //may be uninterp fill kind
};

type ICCPOp = object;

class ICCPOpEmitter
{
    static genDeadFlowOp(sinfo: SourceInfo): ICCPOp {
        return {tag: OpCodeTag.DeadFlowOp, sinfo: sinfo};
    }

    static genAbortOp(sinfo: SourceInfo, msg: string): ICCPOp {
        return {tag: OpCodeTag.AbortOp, sinfo: sinfo, msg: msg};
    }

    static genAssertOp(sinfo: SourceInfo, arg: Argument, msg: String): ICCPOp {
        return {tag: OpCodeTag.AssertOp, sinfo: sinfo, arg: arg, msg: msg};
    }
    
    static genDebugOp(sinfo: SourceInfo, arg: Argument): ICCPOp {
        return {tag: OpCodeTag.DebugOp, sinfo: sinfo, arg: arg};
    }

    static genLoadUnintVariableValueOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.LoadUnintVariableValueOp, sinfo: sinfo, trgt: trgt, oftype: oftype};
    }

    static genBoxUniqueRegisterToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxUniqueRegisterToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genBoxUniqueRefToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxUniqueRefToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueRegisterToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueRefToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxUniqueRefToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxInlineBoxToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.BoxInlineBoxToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRefFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRefFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractInlineBoxFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.ExtractInlineBoxFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genDirectAssignRegisterOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICCPOp {
        return {tag: OpCodeTag.DirectAssignRegisterOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genDirectAssignValueOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICCPOp {
        return {tag: OpCodeTag.DirectAssignValueOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genDirectAssignRefOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICCPOp {
        return {tag: OpCodeTag.DirectAssignRefOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genWidenInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.WidenInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genNarrowInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICCPOp {
        return {tag: OpCodeTag.NarrowInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genGuardedBoxUniqueRegisterToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRefToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRegisterToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRefToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxInlineBoxToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedBoxInlineBoxToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueRefFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueRefFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractInlineBoxFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedExtractInlineBoxFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedDirectAssignRegisterOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedDirectAssignRegisterOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedDirectAssignValueOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedDirectAssignValueOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedDirectAssignRefOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedDirectAssignRefOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedWidenInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedWidenInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedNarrowInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICCPStatementGuard): ICCPOp {
        return {tag: OpCodeTag.GuardedNarrowInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
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
    ICCPGuard, ICCPStatementGuard,
    ICCPOp,
    ICCPOpEmitter
};
