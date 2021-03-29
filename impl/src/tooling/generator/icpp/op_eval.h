//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "assembly/bsqtype.h"
#include "assembly/bsqop.h"

#include "runtime/environment.h"

class Evaluator
{
private:
    std::wstring* getCurrentFile();
    uint64_t getCurrentLine();
    uint64_t getCurrentColumn();

    StorageLocationPtr evalConstArgument(Argument arg);

    inline StorageLocationPtr evalArgument(Argument arg)
    {
        if(arg.kind == ArgumentTag::Register)
        {
            return xxx;
        }
        else if(arg.kind == ArgumentTag::Argument)
        {
            return xxx;
        }
        else 
        {
            return evalConstArgument(arg);
        }
    }

    inline StorageLocationPtr evalTargetVar(TargetVar trgt)
    {
        return xxx;
    }

    inline BSQBool* evalMaskLocation(uint32_t gmaskoffset)
    {
        return xxx;
    }

    void evalDeadFlowOp();
    void evalAbortOp(const AbortOp* op);
    void evalAssertCheckOp(const AssertOp* op);
    void evalDebugOp(const DebugOp* op);

    void evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op);

    void evalBoxUniqueStructToInlineOp(const BoxOp<OpCodeTag::BoxUniqueStructToInlineOp>* op);
    void evalBoxUniqueRefToInlineOp(const BoxOp<OpCodeTag::BoxUniqueRefToInlineOp>* op);
    void evalBoxUniqueStructToHeapOp(const BoxOp<OpCodeTag::BoxUniqueStructToHeapOp>* op);
    void evalBoxUniqueRefToHeapOp(const BoxOp<OpCodeTag::BoxUniqueRefToHeapOp>* op);
    void evalBoxInlineBoxToHeapOp(const BoxOp<OpCodeTag::BoxInlineBoxToHeapOp>* op);
    void evalExtractUniqueStructFromInlineOp(const ExtractOp<OpCodeTag::ExtractUniqueStructFromInlineOp>* op);
    void evalExtractUniqueRefFromInlineOp(const ExtractOp<OpCodeTag::ExtractUniqueRefFromInlineOp>* op);
    void evalExtractUniqueStructFromHeapOp(const ExtractOp<OpCodeTag::ExtractUniqueStructFromHeapOp>* op);
    void evalExtractUniqueRefFromHeapOp(const ExtractOp<OpCodeTag::ExtractUniqueRefFromHeapOp>* op);
    void evalExtractInlineBoxFromHeapOp(const ExtractOp<OpCodeTag::ExtractInlineBoxFromHeapOp>* op);
    void evalWidenInlineOp(const BoxOp<OpCodeTag::WidenInlineOp>* op);
    void evalNarrowInlineOp(const ExtractOp<OpCodeTag::NarrowInlineOp>* op);

    void evalLoadConstOp(const LoadConstOp* op);

    const BSQType* loadTupleTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadTupleDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    
    const BSQType* loadRecordTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadRecordDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    
    const BSQType* loadEntityTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadEntityDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);

    void processTupleDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype);
    void processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype);
    void processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype);

    void processGuardVarStore(const BSQGuard& gv, BSQBool f);

    void evalTupleHasIndexOp(const TupleHasIndexOp* op);
    void evalRecordHasPropertyOp(const RecordHasPropertyOp* op);
    
    void evalLoadTupleIndexDirectOp(const LoadTupleIndexDirectOp* op);
    void evalLoadTupleIndexVirtualOp(const LoadTupleIndexVirtualOp* op);
    void evalLoadTupleIndexSetGuardDirectOp(const LoadTupleIndexSetGuardDirectOp* op);
    void evalLoadTupleIndexSetGuardVirtualOp(const LoadTupleIndexSetGuardVirtualOp* op);

    void evalLoadRecordPropertyDirectOp(const LoadRecordPropertyDirectOp* op);
    void evalLoadRecordPropertyVirtualOp(const LoadRecordPropertyVirtualOp* op);
    void evalLoadRecordPropertySetGuardDirectOp(const LoadRecordPropertySetGuardDirectOp* op);
    void evalLoadRecordPropertySetGuardVirtualOp(const LoadRecordPropertySetGuardVirtualOp* op);

    void evalLoadDirectFieldOp(const LoadEntityFieldDirectOp* op);
    void evalLoadVirtualFieldOp(const LoadEntityFieldVirtualOp* op);

    void evalLoadFromEpehmeralListOp(const LoadFromEpehmeralListOp* op);

    void evalInvokeFixedFunctionOp(const InvokeFixedFunctionOp* op);
    void evalInvokeFixedFunctionWGuardOp(const InvokeFixedFunctionWGuardOp* op);
    void evalInvokeVirtualFunctionOp(const InvokeVirtualFunctionOp* op);
    void evalInvokeVirtualOperatorOp(const InvokeVirtualOperatorOp* op);

    void evalConstructorTupleOp(const ConstructorTupleOp* op);
    void evalConstructorRecordOp(const ConstructorRecordOp* op);
    void evalConstructorEphemeralListOp(const ConstructorEphemeralListOp* op);

    void evalConstructorPrimaryCollectionEmptyOp(const ConstructorPrimaryCollectionEmptyOp* op);
    void evalConstructorPrimaryCollectionSingletonsOp(const ConstructorPrimaryCollectionSingletonsOp* op);
    void evalConstructorPrimaryCollectionCopiesOp(const ConstructorPrimaryCollectionCopiesOp* op);
    void evalConstructorPrimaryCollectionMixedOp(const ConstructorPrimaryCollectionMixedOp* op);

    void evalPrefixNotOp(const PrefixNotOp* op);
    void evalAllTrueOp(const AllTrueOp* op);
    void evalSomeTrueOp(const SomeTrueOp* op);

    void evalIsNoneOp(const IsNoneOp* op);
    void evalIsSomeOp(const IsSomeOp* op);
    void evalTypeTagIsOp(const TypeTagIsOp* op);
    void evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp* op);

    void evalJumpOp(const JumpOp* op);
    void evalJumpCondOp(const JumpCondOp* op);
    void evalJumpNoneOp(const JumpNoneOp* op);

    void evalRegisterAssignOp(const RegisterAssignOp* op);
    void evalReturnAssignOp(const ReturnAssignOp* op);
    void evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op);

    void evalVarLifetimeStartOp(const VarLifetimeStartOp* op);
    void evalVarLifetimeEndOp(const VarLifetimeEndOp* op);

    template <bool isTTDMode>
    void evaluateOpCode(const InterpOp* op);
};
