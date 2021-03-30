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
    std::wstring* dbg_currentFile;
    int64_t dbg_currentLine;

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

    inline StorageLocationPtr evalGuardVar(uint32_t gvaroffset)
    {
        return xxx;
    }

    inline static bool isEnabledGuardStmt(const BSQStatementGuard& sguard)
    {
        return sguard.arg.kind != ArgumentTag::InvalidOp;
    }

    inline BSQBool evalGuardStmt(const BSQGuard& guard)
    {
        if(guard.gindex != -1)
        {
            auto maskptr = this->evalMaskLocation(guard.gmaskoffset);
            return maskptr[guard.gindex];
        }
        else {
            return SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalGuardVar(guard.gvaroffset));
        }
    }

    inline void evalStoreAltValueForGuardStmt(TargetVar trgt, Argument arg, const BSQType* oftype)
    {
        if(arg.kind != ArgumentTag::UninterpFill)
        {
            oftype->slcopy(this->evalTargetVar(trgt), this->evalArgument(arg));
        }
    }

    template <bool isEnabled>
    inline bool tryProcessGuardStmt(TargetVar trgt, const BSQType* trgttype, const BSQStatementGuard& sguard)
    {
        if(isEnabled & Evaluator::isEnabledGuardStmt(sguard))
        {
            if(!this->evalGuard(sguard.guard))
            {
                this->evalStoreAltValueForGuardStmt(op->trgt, op->sguard.arg, op->intotype);
                return false;
            }
        }

        return true;
    }

    void evalDeadFlowOp();
    void evalAbortOp(const AbortOp* op);
    void evalAssertCheckOp(const AssertOp* op);
    void evalDebugOp(const DebugOp* op);

    void evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueStructToInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRefToInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueStructToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRefToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxInlineBoxToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueStructFromInlineOp(const ExtractOp<tag, isGuarded>* op);
    
    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRefFromInlineOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueStructFromHeapOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRefFromHeapOp(const ExtractOp<tag,isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractInlineBoxFromHeapOp(const ExtractOp<tag, isGuarded>* op);

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
