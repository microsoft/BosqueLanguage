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

type ICPPGuard = {
    gmaskoffset: number; 
    gindex: number; //-1 if this is var guard

    gvaroffset: number; //if gindex is -1
};

type ICPPStatementGuard = {
    guard: ICPPGuard;
    usedefaulton: boolean;
    defaultvar: Argument;
};

type ICPPOp = object;

class ICPPOpEmitter
{
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

    static genBoxUniqueRegisterToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxUniqueRegisterToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genBoxUniqueRefToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxUniqueRefToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueRegisterToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxUniqueStructOrStringToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxUniqueRefToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxUniqueRefToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genBoxInlineBoxToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.BoxInlineBoxToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRefFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueRegisterFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractUniqueRefFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractUniqueRefFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genExtractInlineBoxFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.ExtractInlineBoxFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genDirectAssignRegisterOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICPPOp {
        return {tag: OpCodeTag.DirectAssignRegisterOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genDirectAssignValueOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICPPOp {
        return {tag: OpCodeTag.DirectAssignValueOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genDirectAssignRefOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number): ICPPOp {
        return {tag: OpCodeTag.DirectAssignRefOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size};
    }

    static genWidenInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.WidenInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }

    static genNarrowInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.NarrowInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype};
    }
    
    static genGuardedBoxUniqueRegisterToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueStructOrStringToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRefToInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRegisterToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRegisterToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueStructOrStringToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueStructOrStringToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxUniqueRefToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxUniqueRefToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedBoxInlineBoxToHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedBoxInlineBoxToHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueRegisterFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueStructOrStringFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueRefFromInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueRegisterFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRegisterFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractUniqueStructOrStringFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueStructOrStringFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }
    
    static genGuardedExtractUniqueRefFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractUniqueRefFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedExtractInlineBoxFromHeapOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedExtractInlineBoxFromHeapOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedDirectAssignRegisterOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedDirectAssignRegisterOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedDirectAssignValueOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedDirectAssignValueOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedDirectAssignRefOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, size: number, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedDirectAssignRefOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, size: size, sguard: sguard};
    }

    static genGuardedWidenInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedWidenInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genGuardedNarrowInlineOp(sinfo: SourceInfo, trgt: TargetVar, intotype: MIRResolvedTypeKey, arg: Argument, fromtype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedNarrowInlineOp, sinfo: sinfo, trgt: trgt, intotype: intotype, arg: arg, fromtype: fromtype, sguard: sguard};
    }

    static genLoadConstOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey): ICPPOp {
        return {tag: OpCodeTag.LoadConstOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype};
    }

    static genTupleHasIndexOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, layouttype: MIRResolvedTypeKey, idx: number): ICPPOp {
        return {tag: OpCodeTag.TupleHasIndexOp, sinfo: sinfo, trgt: trgt, arg: arg, layouttype: layouttype, idx: idx};
    }

    static genRecordHasPropertyOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, layouttype: MIRResolvedTypeKey, propId: number): ICPPOp {
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

    static genLoadRecordPropertyDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, propId: number): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertyDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, propId: propId};
    }

    static genLoadRecordPropertyVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, propId: number): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertyVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, propId: propId};
    }

    static genLoadRecordPropertySetGuardDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, propId: number, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertySetGuardDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, propId: propId, guard: guard};
    }

    static genLoadRecordPropertySetGuardVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, propId: number, guard: ICPPGuard): ICPPOp {
        return {tag: OpCodeTag.LoadRecordPropertySetGuardVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, propId: propId, guard: guard};
    }

    static genLoadEntityFieldDirectOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, fieldId: number): ICPPOp {
        return {tag: OpCodeTag.LoadEntityFieldDirectOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, fieldId: fieldId};
    }

    static genLoadEntityFieldVirtualOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, fieldId: number): ICPPOp {
        return {tag: OpCodeTag.LoadEntityFieldVirtualOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, fieldId: fieldId};
    }

    static genLoadFromEpehmeralListOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, arg: Argument, layouttype: MIRResolvedTypeKey, slotoffset: number, index: number): ICPPOp {
        return {tag: OpCodeTag.LoadFromEpehmeralListOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, arg: arg, layouttype: layouttype, slotoffset: slotoffset, index: index};
    }

    static genInvokeFixedFunctionOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: number, args: Argument[], optmaskoffset: number): ICPPOp {
        return {tag: OpCodeTag.InvokeFixedFunctionOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args, optmaskoffset: optmaskoffset};
    }

    static genGuardedInvokeFixedFunctionOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: number, args: Argument[], optmaskoffset: number, sguard: ICPPStatementGuard): ICPPOp {
        return {tag: OpCodeTag.GuardedInvokeFixedFunctionOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args, optmaskoffset: optmaskoffset, sguard: sguard};
    }

    static genInvokeVirtualFunctionOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: number, args: Argument[], optmaskoffset: number): ICPPOp {
        return {tag: OpCodeTag.InvokeVirtualFunctionOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args, optmaskoffset: optmaskoffset};
    }

    static genInvokeVirtualOperatorOp(sinfo: SourceInfo, trgt: TargetVar, trgttype: MIRResolvedTypeKey, invokeId: number, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.InvokeVirtualOperatorOp, sinfo: sinfo, trgt: trgt, trgttype: trgttype, invokeId: invokeId, args: args};
    }

    static genConstructorTupleOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorTupleOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
    }

    static genConstructorRecordOp(sinfo: SourceInfo, trgt: TargetVar, oftype: MIRResolvedTypeKey, args: Argument[]): ICPPOp {
        return {tag: OpCodeTag.ConstructorRecordOp, sinfo: sinfo, trgt: trgt, oftype: oftype, args: args};
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

    /*
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
    */
    
    static genJumpOp(sinfo: SourceInfo, offset: number, label: string): ICPPOp {
        return { tag: OpCodeTag.JumpOp, sinfo: sinfo, offset: offset, label: label };
    }

    static genJumpCondOp(sinfo: SourceInfo, arg: Argument, toffset: number, foffset: number, tlabel: string, flabel: string): ICPPOp {
        return { tag: OpCodeTag.JumpCondOp, sinfo: sinfo, arg: arg, toffset: toffset, foffset: foffset, tlabel: tlabel, flabel: flabel };
    }
    
    static genJumpNoneOp(sinfo: SourceInfo, arg: Argument, arglayout: MIRResolvedTypeKey, noffset: number, soffset: number, nlabel: string, slabel: string): ICPPOp {
        return { tag: OpCodeTag.JumpNoneOp, sinfo: sinfo, arg: arg, arglayout: arglayout, noffset: noffset, soffset: soffset, nlabel: nlabel, slabel: slabel};
    }
    
    static genRegisterAssignOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey): ICPPOp {
        return { tag: OpCodeTag.RegisterAssignOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype };
    }
    
    static genGuardedRegisterAssignOp(sinfo: SourceInfo, trgt: TargetVar, arg: Argument, oftype: MIRResolvedTypeKey, sguard: ICPPStatementGuard): ICPPOp {
        return { tag: OpCodeTag.GuardedRegisterAssignOp, sinfo: sinfo, trgt: trgt, arg: arg, oftype: oftype, sguard: sguard };
    }
    
    static genReturnAssignOp(sinfo: SourceInfo, arg: Argument, oftype: MIRResolvedTypeKey): ICPPOp {
        return { tag: OpCodeTag.ReturnAssignOp, sinfo: sinfo, arg: arg, oftype: oftype };
    }
    
    static genReturnAssignOfConsOp(sinfo: SourceInfo, args: Argument[], oftype: MIRResolvedTypeKey): ICPPOp {
        return { tag: OpCodeTag.ReturnAssignOfConsOp, sinfo: sinfo, args: args, oftype: oftype };
    }
    
    static genVarLifetimeStartOp(sinfo: SourceInfo, homelocation: Argument, oftype: MIRResolvedTypeKey, name: string): ICPPOp {
        return { tag: OpCodeTag.VarLifetimeStartOp, sinfo: sinfo, homelocation: homelocation, oftype: oftype, name: name };
    }
    
    static genVarLifetimeEndOp(sinfo: SourceInfo, name: string): ICPPOp {
        return { tag: OpCodeTag.VarLifetimeEndOp, sinfo: sinfo, name: name };
    }
    
/*
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
    ICPPGuard, ICPPStatementGuard,
    ICPPOp,
    ICPPOpEmitter
};
