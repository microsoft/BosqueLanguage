//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "assembly/bsqtype.h"
#include "assembly/bsqop.h"

#include "runtime/environment.h"

class EvaluatorFrame
{
public:
#ifdef BSQ_DEBUG_BUILD
    const std::wstring* dbg_file;
    const std::wstring* dbg_function;
    int64_t dbg_prevline;
    int64_t dbg_line;
#endif

    void* argsbase;
    void* localsbase;

    const std::vector<InterpOp*>* ops;
    std::vector<InterpOp*>::const_iterator cpos;

#ifdef BSQ_DEBUG_BUILD
    EvaluatorFrame(std::wstring* dbg_file, std::wstring* dbg_function, void* argsbase, void* localsbase, const std::vector<InterpOp*>* ops) : dbg_file(dbg_file), dbg_function(dbg_function), dbg_prevline(-1), dbg_line(-1), argsbase(argsbase), localsbase(localsbase), ops(ops), cpos(ops->cbegin()) 
    {
        this->dbg_line = this->cpos->sinfo.line;
    }
#else
    EvaluatorFrame(void* argsbase, void* localsbase, const std::vector<InterpOp*>* ops) : argsbase(argsbase), localsbase(localsbase), ops(ops), cpos(ops->cbegin()) {;}
#endif
};

class Evaluator
{
private:
    EvaluatorFrame* cframe;
    std::deque<EvaluatorFrame> callstack;

#ifdef BSQ_DEBUG_BUILD
    inline void pushFrame(std::wstring* dbg_file, std::wstring* dbg_function, void* argsbase, void* localsbase, const std::vector<InterpOp*>* ops)
    {
        tthis->callstack.emplace_back(dbg_file, dbg_function, argsbase, localsbase, ops);
    }
#else
    inline void pushFrame(void* argsbase, void* localsbase, const std::vector<InterpOp*>* ops) 
    {
        this->callstack.emplace_back(argsbase, localsbase, ops);
    }
#endif

    inline void popFrame()
    {
        this->callstack.pop_back();
    }

#ifdef BSQ_DEBUG_BUILD
    const std::wstring* getCurrentFile() { return cframe->dbg_file; }
    const std::wstring* getCurrentfunction() { return cframe->dbg_function; }
    int64_t getPrevLine() { return cframe->dbg_prevline; }
    int64_t getCurrentLine() { return cframe->dbg_line; }
#else
    const std::wstring* getCurrentFile() { return nullptr; }
    const std::wstring* getCurrentfunction() { return nullptr; }
    int64_t getPrevLine() { return -1; }
    int64_t getCurrentLine() { return 0; }
#endif

    inline InterpOp* getCurrentOp()
    {
        return *this->cframe->cpos;
    }

    inline InterpOp* advanceCurrentOp(uint32_t offset)
    {
        this->cframe->cpos += offset;

#ifdef BSQ_DEBUG_BUILD
        this->cframe->dbg_prevline = this->cframe->dbg_line;
        this->dbg_line = this->cframe->cpos->sinfo.line;  
#endif

        return *this->cframe->cpos;
    }

    inline InterpOp* advanceCurrentOp()
    {
        this->cframe->cpos++;

#ifdef BSQ_DEBUG_BUILD
        this->cframe->dbg_prevline = this->cframe->dbg_line;
        this->dbg_line = this->cframe->cpos->sinfo.line;  
#endif

        return *this->cframe->cpos;
    }

    StorageLocationPtr evalConstArgument(Argument arg);

    inline void clearValue(StorageLocationPtr trgt, const BSQType* oftype)
    {
#ifdef BSQ_DEBUG_BUILD
        if((oftype->tkind == BSQTypeKind::Ref) | (oftype->tkind == BSQTypeKind::HeapUnion)) 
        {
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
        }
        else 
        {
            if(oftype->tkind == BSQTypeKind::Register || oftype->tkind == BSQTypeKind::Struct)
            {
                GC_MEM_ZERO(trgt, oftype->allocsize);
            }
            else
            {
                GC_MEM_ZERO(trgt, static_cast<const BSQInlineUnionType*>(oftype)->getAllocSizePlusType());
            }
        }
#endif
    }

    inline void storeValue(StorageLocationPtr trgt, StorageLocationPtr src, const BSQType* oftype)
    {
        if((oftype->tkind == BSQTypeKind::Ref) | (oftype->tkind == BSQTypeKind::HeapUnion)) 
        {
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
        }
        else 
        {
            if(oftype->tkind == BSQTypeKind::Register || oftype->tkind == BSQTypeKind::Struct)
            {
                SLPTR_COPY_CONTENTS(trgt, src, oftype->allocsize);
            }
            else
            {
                SLPTR_COPY_CONTENTS(trgt, src, static_cast<const BSQInlineUnionType*>(oftype)->getAllocSizePlusType());
            }
        }
    }

    inline StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, uint32_t offset, const BSQType* oftype)
    {
        if((oftype->tkind == BSQTypeKind::Ref) | (oftype->tkind == BSQTypeKind::HeapUnion)) 
        {
            SLPTR_INDEX_HEAP(src, offset);
        }
        else 
        {
            if(oftype->tkind == BSQTypeKind::Register || oftype->tkind == BSQTypeKind::Struct)
            {
                SLPTR_INDEX_INLINE(src, offset);
            }
            else
            {
                SLPTR_INDEX_INLINE(src, offset + sizeof(BSQType*));
            }
        }
    }

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
        return sguard.defaultvar.kind != ArgumentTag::InvalidOp;
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
            this->storeValue(this->evalTargetVar(trgt), this->evalArgument(arg), oftype);
        }
        else
        {
            this->clearValue(this->evalTargetVar(trgt), oftype);
        }
    }

    template <bool isEnabled>
    inline bool tryProcessGuardStmt(TargetVar trgt, const BSQType* trgttype, const BSQStatementGuard& sguard)
    {
        if(!isEnabled)
        {
            return true;
        }
        else
        {
            if(!Evaluator::isEnabledGuardStmt(sguard))
            {
                return true;
            }
            else
            {
                auto gval = this->evalGuard(sguard.guard);
                auto dodefault = sguard.usedefaulton ? gval : !gval;

                if(dodefault)
                {
                    this->evalStoreAltValueForGuardStmt(op->trgt, op->sguard.arg, op->intotype);
                }

                return dodefault;
            }
        }
    }

    inline const BSQType* loadBSQTypeFromAbstractLocationGeneral(StorageLocationPtr sl, const BSQType* layouttype)
    {
        auto layout = layouttype->tkind;
        if(layout == BSQTypeKind::InlineUnion)
        {
            return SLPTR_LOAD_UNION_INLINE_TYPE(sl);
        }
        else
        {
            assert(layout == BSQTypeKind::HeapUnion);
            if(SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(sl) == BSQNoneHeapValue)
            {
                return Environment::g_typeNone;
            }
            else
            {
                return SLPTR_LOAD_UNION_HEAP_TYPE(sl);
            }
        }
    }

    template <typename T>
    inline const T* loadBSQTypeFromAbstractLocationOfType(StorageLocationPtr sl, const BSQType* layouttype)
    {
        return static_cast<const T*>(this->loadBSQTypeFromAbstractLocationGeneral(sl, layouttype));
    }

    inline StorageLocationPtr Evaluator::loadDataPtrFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
    {
        auto layout = layouttype->tkind;
        if(layout == BSQTypeKind::InlineUnion)
        {
            return SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);

        }
        else
        {
            assert(layout == BSQTypeKind::HeapUnion);
            return SLPTR_LOAD_UNION_HEAP_DATAPTR(sl);
        }
    }

    void evalDeadFlowOp();
    void evalAbortOp(const AbortOp* op);
    void evalAssertCheckOp(const AssertOp* op);
    void evalDebugOp(const DebugOp* op);

    void evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRegisterToInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueStructToInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRefToInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRegisterToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueStructToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxUniqueRefToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalBoxInlineBoxToHeapOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRegisterFromInlineOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueStructFromInlineOp(const ExtractOp<tag, isGuarded>* op);
    
    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRefFromInlineOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRegisterFromHeapOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueStructFromHeapOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractUniqueRefFromHeapOp(const ExtractOp<tag,isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalExtractInlineBoxFromHeapOp(const ExtractOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalWidenInlineOp(const BoxOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalNarrowInlineOp(const ExtractOp<tag, isGuarded>* op);

    void evalLoadConstOp(const LoadConstOp* op);

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

    template <OpCodeTag tag, bool isGuarded>
    void evalInvokeFixedFunctionOp(const InvokeFixedFunctionOp<tag, isGuarded>* op);

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

    void evalBinKeyEqVirtualOp(const BinKeyEqVirtualOp* op);
    void evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalIsNoneOp(const TypeIsNoneOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalIsSomeOp(const TypeIsSomeOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalTypeTagIsOp(const TypeTagIsOp<tag, isGuarded>* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp<tag, isGuarded>* op);

    void evalJumpOp(const JumpOp* op);
    void evalJumpCondOp(const JumpCondOp* op);
    void evalJumpNoneOp(const JumpNoneOp* op);

    template <OpCodeTag tag, bool isGuarded>
    void evalRegisterAssignOp(const RegisterAssignOp<tag, isGuarded>* op);

    void evalReturnAssignOp(const ReturnAssignOp* op);
    void evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op);

    void evalVarLifetimeStartOp(const VarLifetimeStartOp* op);
    void evalVarLifetimeEndOp(const VarLifetimeEndOp* op);

    template <bool isTTDMode>
    void evaluateOpCode(const InterpOp* op);
};
