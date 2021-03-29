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

    void evalDeadFlow();
    void evalAbort(const AbortOp* op);
    void evalAssertCheck(const AssertOp* op);
    void evalDebug(const DebugOp* op);

    void evalLoadUnintVariableValue(const LoadUnintVariableValueOp* op);

    void evalBoxUniqueStructToInlineOp(const BoxOp<OpCodeTag::BoxUniqueStructToInlineOp>* op);
    void evalBoxUniqueRefToInlineOp(const BoxOp<OpCodeTag::BoxUniqueRefToInlineOp>* op);
    void evalBoxUniqueStructToHeapOp(const BoxOp<OpCodeTag::BoxUniqueStructToHeapOp>* op);
    void evalBoxUniqueRefToHeapOp(const BoxOp<OpCodeTag::BoxUniqueRefToHeapOp>* op);
    void evalBoxInlineBoxToHeapOp(const BoxOp<OpCodeTag::BoxInlineBoxToHeapOp>* op);
    void evalExtractUniqueStructFromInlineOp(const BoxOp<OpCodeTag::ExtractUniqueStructFromInlineOp>* op);
    void evalExtractUniqueRefFromInlineOp(const BoxOp<OpCodeTag::ExtractUniqueRefFromInlineOp>* op);
    void evalExtractUniqueStructFromHeapOp(const BoxOp<OpCodeTag::ExtractUniqueStructFromHeapOp>* op);
    void evalExtractUniqueRefFromHeapOp(const BoxOp<OpCodeTag::ExtractUniqueRefFromHeapOp>* op);
    void evalExtractInlineBoxFromHeapOp(const BoxOp<OpCodeTag::ExtractInlineBoxFromHeapOp>* op);

    void evalLoadConst(const LoadConstOp* op);

    const BSQTupleType* loadTupleTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadTupleDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    
    const BSQRecordType* loadRecordTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadRecordDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    
    const BSQType* loadEntityTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);
    StorageLocationPtr loadEntityDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype);

    void processTupleDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQTupleType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype);
    void processRecordDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQRecordType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype);
    void processEntityDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype);
    void processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQStdEntityType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype);

    void processGuardVarStore(const BSQGuard& gv, BSQBool f);

    void evalTupleHasIndex(const TupleHasIndexOp* op);
    void evalRecordHasProperty(const RecordHasPropertyOp* op);
    
    void evalLoadTupleIndexDirect(const LoadTupleIndexDirectOp* op);
    void evalLoadTupleIndexVirtual(const LoadTupleIndexVirtualOp* op);
    void evalLoadTupleIndexSetGuardDirect(const LoadTupleIndexSetGuardDirectOp* op);
    void evalLoadTupleIndexSetGuardVirtual(const LoadTupleIndexSetGuardVirtualOp* op);

    void evalLoadRecordPropertyDirect(const LoadRecordPropertyDirectOp* op);
    void evalLoadRecordPropertyVirtual(const LoadRecordPropertyVirtualOp* op);
    void evalLoadRecordPropertySetGuardDirect(const LoadRecordPropertySetGuardDirectOp* op);
    void evalLoadRecordPropertySetGuardVirtual(const LoadRecordPropertySetGuardVirtualOp* op);

    void evalLoadDirectField(const LoadEntityFieldDirectOp* op);
    void evalLoadVirtualField(const LoadEntityFieldVirtualOp* op);

    void evalLoadFromEpehmeralList(const LoadFromEpehmeralListOp* op);

    void evalInvokeFixedFunction(const InvokeFixedFunctionOp* op);
    void evalInvokeVirtualFunction(const InvokeVirtualFunctionOp* op);
    void evalInvokeVirtualOperator(const InvokeVirtualOperatorOp* op);

    void evalConstructorTuple(const ConstructorTupleOp* op);
    void evalConstructorRecord(const ConstructorRecordOp* op);
    void evalConstructorEphemeralList(const ConstructorEphemeralListOp* op);

    void evalConstructorPrimaryCollectionEmpty(const ConstructorPrimaryCollectionEmptyOp* op);
    void evalConstructorPrimaryCollectionSingletons(const ConstructorPrimaryCollectionSingletonsOp* op);
    void evalConstructorPrimaryCollectionCopies(const ConstructorPrimaryCollectionCopiesOp* op);
    void evalConstructorPrimaryCollectionMixed(const ConstructorPrimaryCollectionMixedOp* op);

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
};
