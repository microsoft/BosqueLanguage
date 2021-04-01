//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

StorageLocationPtr Evaluator::evalConstArgument(Argument arg)
{
    switch (arg.kind)
    {
    case ArgumentTag::ConstNone:
        return Environment::g_constNone;
    case ArgumentTag::ConstTrue:
        return &Environment::g_constTrue;
    case ArgumentTag::ConstFalse:
        return &Environment::g_constFalse;
    case ArgumentTag::ConstNat:
        return Environment::g_constNats + arg.location;
    case ArgumentTag::ConstInt:
        return Environment::g_constInts + arg.location;
    case ArgumentTag::ConstBigNat:
        return Environment::g_constBigNats + arg.location;
    case ArgumentTag::ConstBigInt:
        return Environment::g_constBigInts + arg.location;
    case ArgumentTag::ConstRational:
        return Environment::g_constRationals + arg.location;
    case ArgumentTag::ConstFloat:
        return Environment::g_constFloats + arg.location;
    case ArgumentTag::ConstDecimal:
        return Environment::g_constDecimals + arg.location;
    case ArgumentTag::ConstString:
        return Environment::g_constStrings + arg.location;
    case ArgumentTag::ConstRegex:
        return Environment::g_constRegexs + arg.location;
    default: {
            const ConstValueLoad loadfp = Environment::g_constLoads[arg.location];
            return loadfp();
        }
    }
}

void Evaluator::evalDeadFlowOp()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void Evaluator::evalAbortOp(const AbortOp *op)
{
    BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
}

void Evaluator::evalAssertCheckOp(const AssertOp *op)
{
    auto val = this->evalArgument(op->arg);
    if (!SLPTR_LOAD_CONTENTS_AS(BSQBool, val))
    {
        BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
    }
}

void Evaluator::evalDebugOp(const DebugOp *op)
{
    if(op->arg.kind == ArgumentTag::InvalidOp)
    {
        //TODO: debugger break here
        assert(false);
    }
    else
    {
        auto val = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
        auto ttype = GET_TYPE_META_DATA(val);
        auto dval = ttype->fpDisplay(val);

        wprintf(L"%s\n", dval.c_str());
        fflush(stdout);
    }
}

void Evaluator::evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op)
{
    this->clearValue(this->evalTargetVar(op->trgt), op->oftype);
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalBoxUniqueStructToInlineOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, op->fromtype);
        SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), this->evalArgument(op->arg), op->fromtype->allocsize));
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalBoxUniqueRefToInlineOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, op->fromtype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg)));
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalBoxUniqueStructToHeapOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        auto balloc = Allocator::allocateDynamic(op->fromtype);
        SLPTR_COPY_CONTENTS(balloc, this->evalArgument(op->arg), op->fromtype->allocsize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, balloc);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalBoxUniqueRefToHeapOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg)));
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalBoxInlineBoxToHeapOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(srcl);

        auto isl = this->evalTargetVar(op->trgt);
        auto balloc = Allocator::allocateDynamic(rtype);
        SLPTR_COPY_CONTENTS(balloc, SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl), rtype->allocsize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, balloc);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractUniqueStructFromInlineOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto sldata = SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl);
        SLPTR_COPY_CONTENTS(this->evalTargetVar(op->trgt), sldata, op->intotype->allocsize);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractUniqueRefFromInlineOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto sldata = SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(sldata));
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractUniqueStructFromHeapOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto sldata = SLPTR_LOAD_UNION_HEAP_DATAPTR(srcl);
        SLPTR_COPY_CONTENTS(this->evalTargetVar(op->trgt), sldata, op->intotype->allocsize);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractUniqueRefFromHeapOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(srcl));
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractInlineBoxFromHeapOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto rtype = SLPTR_LOAD_UNION_HEAP_TYPE(srcl);

        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, rtype);
        SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), SLPTR_LOAD_UNION_HEAP_DATAPTR(srcl), rtype->allocsize);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalWidenInlineOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(srcl);

        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, rtype);
        SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl), rtype->allocsize);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalNarrowInlineOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(srcl);

        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, rtype);
        SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl), rtype->allocsize);
    }
}

void Evaluator::evalLoadConstOp(const LoadConstOp* op)
{
    this->storeValue(this->evalTargetVar(op->trgt), Evaluator::evalConstArgument(op->arg), op->oftype);
}

void Evaluator::processTupleDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    this->storeValue(this->evalTargetVar(dst), this->indexStorageLocationOffset(src, slotoffset, srctype), dsttype);
}

void Evaluator::processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype)
{
    auto ttype = this->loadBSQTypeFromAbstractLocation<BSQTupleType>(src, srctype);
    auto voffset = ttype->idxoffsets[idx];
    this->processTupleDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    this->storeValue(this->evalTargetVar(dst), this->indexStorageLocationOffset(src, slotoffset, srctype), dsttype);
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    auto rtype = this->loadBSQTypeFromAbstractLocation<BSQRecordType>(src, srctype);
    auto proppos = std::find(rtype->properties.cbegin(), rtype->properties.cend(), propId);
    assert(proppos != rtype->properties.cend());

    auto propidx = std::distance(rtype->properties.cbegin(), proppos);
    auto voffset = rtype->propertyoffsets[propidx];

    this->processRecordDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}
    
void Evaluator::processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    this->storeValue(this->evalTargetVar(dst), this->indexStorageLocationOffset(src, slotoffset, srctype), dsttype);
}

void Evaluator::processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype)
{
    auto etype = this->loadBSQTypeFromAbstractLocation<BSQEntityType>(src, srctype);
    auto fldpos = std::find(etype->fields.cbegin(), etype->fields.cend(), fldId);
    assert(fldpos != etype->fields.cend());

    auto fldidx = std::distance(etype->fields.cbegin(), fldpos);
    auto voffset = etype->fieldoffsets[fldidx];

    this->processEntityDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}

void Evaluator::processGuardVarStore(const BSQGuard& gv, BSQBool f)
{
    if(gv.gindex == -1)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalGuardVar(gv.gvaroffset), f);
    }
    else
    {
        auto mask = this->evalMaskLocation(gv.gmaskoffset);
        mask[gv.gindex] = f;
    }
}

void Evaluator::evalTupleHasIndexOp(const TupleHasIndexOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto ttype = this->loadBSQTypeFromAbstractLocation<BSQTupleType>(sl, op->layouttype);
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)(op->idx < ttype->maxIndex));
}

void Evaluator::evalRecordHasPropertyOp(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto rtype = this->loadBSQTypeFromAbstractLocation<BSQRecordType>(sl, op->layouttype);
    BSQBool hasprop = std::find(rtype->properties.cbegin(), rtype->properties.cend(), op->propId) != rtype->properties.cend();

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), hasprop);
}

void Evaluator::evalLoadTupleIndexDirectOp(const LoadTupleIndexDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->layouttype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexVirtualOp(const LoadTupleIndexVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    this->processTupleVirtualLoadAndStore(sl, op->layouttype, op->idx, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexSetGuardDirectOp(const LoadTupleIndexSetGuardDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->layouttype, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadTupleIndexSetGuardVirtualOp(const LoadTupleIndexSetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadBSQTypeFromAbstractLocation<BSQTupleType>(sl, op->layouttype);
    
    BSQBool loadsafe = op->idx < argtype->maxIndex;
    if(loadsafe)
    {
        this->processTupleVirtualLoadAndStore(sl, op->layouttype, op->idx, op->trgt, op->trgttype);

    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadRecordPropertyDirectOp(const LoadRecordPropertyDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->layouttype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertyVirtualOp(const LoadRecordPropertyVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    this->processRecordVirtualLoadAndStore(sl, op->layouttype, op->propId, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertySetGuardDirectOp(const LoadRecordPropertySetGuardDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->layouttype, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadRecordPropertySetGuardVirtualOp(const LoadRecordPropertySetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadBSQTypeFromAbstractLocation<BSQRecordType>(sl, op->layouttype);

    BSQBool loadsafe = std::find(argtype->properties.cbegin(), argtype->properties.cend(), op->propId) != argtype->properties.cend();
    if(loadsafe)
    {
        this->processRecordVirtualLoadAndStore(sl, op->layouttype, op->propId, op->trgt, op->trgttype);
    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadDirectFieldOp(const LoadEntityFieldDirectOp* op)
{
    this->processEntityDirectLoadAndStore(this->evalArgument(op->arg), op->layouttype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadVirtualFieldOp(const LoadEntityFieldVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    this->processEntityVirtualLoadAndStore(sl, op->layouttype, op->fieldId, op->trgt, op->trgttype);
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalInvokeFixedFunctionOp(const InvokeFixedFunctionOp<tag, isGuarded>* op)
{
    xxxx;
}

void Evaluator::evalInvokeVirtualFunctionOp(const InvokeVirtualFunctionOp* op)
{
    //NOT IMPLEMENTED
    assert(false);
}

void Evaluator::evalInvokeVirtualOperatorOp(const InvokeVirtualOperatorOp* op)
{
    //NOT IMPLEMENTED
    assert(false);
}

void Evaluator::evalConstructorTupleOp(const ConstructorTupleOp* op)
{
    StorageLocationPtr sl = this->evalTargetVar(op->trgt);
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->tkind == BSQTypeKind::Struct)
    {
        tcontents = sl;
    }
    else
    {
        tcontents = Allocator::GlobalAllocator.allocateDynamic(op->oftype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tcontents);
    }

    for(size_t i = 0; i < op->oftype->idxoffsets.size(); ++i)
    {
        this->storeValue(this->indexStorageLocationOffset(tcontents, op->oftype->idxoffsets[i], op->oftype), this->evalArgument(op->args[i]), op->oftype->ttypes[i]);
    }
}

void Evaluator::evalConstructorRecordOp(const ConstructorRecordOp* op)
{
    StorageLocationPtr sl = this->evalTargetVar(op->trgt);
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->tkind == BSQTypeKind::Struct)
    {
        tcontents = sl;
    }
    else
    {
        tcontents = Allocator::GlobalAllocator.allocateDynamic(op->oftype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tcontents);
    }

    for(size_t i = 0; i < op->oftype->propertyoffsets.size(); ++i)
    {
        this->storeValue(this->indexStorageLocationOffset(tcontents, op->oftype->propertyoffsets[i], op->oftype), this->evalArgument(op->args[i]), op->oftype->rtypes[i]);
    }
}

void Evaluator::evalConstructorEphemeralListOp(const ConstructorEphemeralListOp* op)
{
    StorageLocationPtr tcontents = this->evalTargetVar(op->trgt);

    for(size_t i = 0; i < op->oftype->idxoffsets.size(); ++i)
    {
        this->storeValue(this->indexStorageLocationOffset(tcontents, op->oftype->idxoffsets[i], op->oftype), this->evalArgument(op->args[i]), op->oftype->etypes[i]);
    }
}

void Evaluator::evalConstructorPrimaryCollectionEmptyOp(const ConstructorPrimaryCollectionEmptyOp* op)
{
    xxxx;
}

void Evaluator::evalConstructorPrimaryCollectionSingletonsOp(const ConstructorPrimaryCollectionSingletonsOp* op)
{
    xxxx;
}

void Evaluator::evalConstructorPrimaryCollectionCopiesOp(const ConstructorPrimaryCollectionCopiesOp* op)
{
    assert(false);
}

void Evaluator::evalConstructorPrimaryCollectionMixedOp(const ConstructorPrimaryCollectionMixedOp* op)
{
    assert(false);
}

void Evaluator::evalPrefixNotOp(const PrefixNotOp* op)
{
    BSQBool sval = !SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(op->arg));
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), sval);
}

void Evaluator::evalAllTrueOp(const AllTrueOp* op)
{
    auto fpos = std::find_if(op->args.cbegin(), op->args.cend(), [this](Argument arg) {
        return !SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(arg));
    });

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), fpos != op->args.cend());
}
    
void Evaluator::evalSomeTrueOp(const SomeTrueOp* op)
{
    auto tpos = std::find_if(op->args.cbegin(), op->args.cend(), [this](Argument arg) {
        return SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(arg));
    });

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), tpos != op->args.cend());
}

void Evaluator::evalBinKeyEqVirtualOp(const BinKeyEqVirtualOp* op)
{
    //Get types for the values -- either virtual or direct
    //Make sure they are equal -- otherwise call virtual eq op
    xxxx;
}

void Evaluator::evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op)
{
    //Get types for the values -- either virtual or direct
    //Make sure they are ordered -- otherwise call virtual < op
    xxxx;
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalIsNoneOp(const TypeIsNoneOp<tag, isGuarded>* op)
{
    this->loadBSQTypeFromAbstractLocation(this->evalArgument(op->arg), op->arglayout)->tkind = BSQTypeKind::None;
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalIsSomeOp(const TypeIsSomeOp<tag, isGuarded>* op)
{
    this->loadBSQTypeFromAbstractLocation(this->evalArgument(op->arg), op->arglayout)->tkind != BSQTypeKind::None;
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalTypeTagIsOp(const TypeTagIsOp<tag, isGuarded>* op)
{
    this->loadBSQTypeFromAbstractLocation(this->evalArgument(op->arg), op->arglayout)->tkind == op->oftype->tkind;
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp<tag, isGuarded>* op)
{
    xxxx;
}

void Evaluator::evalJumpOp(const JumpOp* op)
{
    xxxx;
}

void Evaluator::evalJumpCondOp(const JumpCondOp* op)
{
    xxxx;
}

void Evaluator::evalJumpNoneOp(const JumpNoneOp* op)
{
    xxxx;
}

void Evaluator::evalRegisterAssignOp(const RegisterAssignOp* op)
{
    xxxx;
}

void Evaluator::evalReturnAssignOp(const ReturnAssignOp* op)
{
    xxxx;
}

void Evaluator::evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op)
{
    xxxx;
}

void Evaluator::evalVarLifetimeStartOp(const VarLifetimeStartOp* op)
{
    assert(false);
}


void Evaluator::evalVarLifetimeEndOp(const VarLifetimeEndOp* op)
{
    assert(false);
}

template <bool isTTDMode>
void Evaluator::evaluateOpCode(const InterpOp* op)
{
#ifdef BSQ_DEBUG_BUILD 
    //TODO: update position info for debugging
#endif

    switch(op->tag)
    {
    case OpCodeTag::DeadFlowOp:
    {
        this->evalDeadFlowOp();
    }
    case OpCodeTag::AbortOp:
    {
        this->evalAbortOp(static_cast<const AbortOp*>(op));
    }
    case OpCodeTag::AssertOp:
    {
        this->evalAssertCheckOp(static_cast<const AssertOp*>(op));
    }
#ifdef BSQ_DEBUG_BUILD 
    case OpCodeTag::DebugOp:
    {
        this->evalDebugOp(static_cast<const DebugOp*>(op));
    }
    case OpCodeTag::LoadUnintVariableValueOp:
    {
        this->evalLoadUnintVariableValueOp(static_cast<const LoadUnintVariableValueOp*>(op));
    }
#endif
    case OpCodeTag::BoxUniqueStructToInlineOp:
    {
        this->evalBoxUniqueStructToInlineOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueStructToInlineOp>*>(op));
    }
    case OpCodeTag::BoxUniqueRefToInlineOp:
    {
        this->evalBoxUniqueRefToInlineOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRefToInlineOp>*>(op));
    }
    case OpCodeTag::BoxUniqueStructToHeapOp:
    {
        this->evalBoxUniqueStructToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueStructToHeapOp>*>(op));
    }
    case OpCodeTag::BoxUniqueRefToHeapOp:
    {
        this->evalBoxUniqueRefToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRefToHeapOp>*>(op));
    }
    case OpCodeTag::BoxInlineBoxToHeapOp:
    {
        this->evalBoxInlineBoxToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxInlineBoxToHeapOp>*>(op));
    }
    case OpCodeTag::ExtractUniqueStructFromInlineOp:
    {
        this->evalExtractUniqueStructFromInlineOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueStructFromInlineOp>*>(op));
    }
    case OpCodeTag::ExtractUniqueRefFromInlineOp:
    {
        this->evalExtractUniqueRefFromInlineOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRefFromInlineOp>*>(op));
    }
    case OpCodeTag::ExtractUniqueStructFromHeapOp:
    {
        this->evalExtractUniqueStructFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueStructFromHeapOp>*>(op));
    }
    case OpCodeTag::ExtractUniqueRefFromHeapOp:
    {
        this->evalExtractUniqueRefFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRefFromHeapOp>*>(op));
    }
    case OpCodeTag::ExtractInlineBoxFromHeapOp:
    {
        this->evalExtractInlineBoxFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractInlineBoxFromHeapOp>*>(op));
    }
    case OpCodeTag::WidenInlineOp:
    {
        this->evalWidenInlineOp(static_cast<const BoxOp<OpCodeTag::WidenInlineOp>*>(op));
    }
    case OpCodeTag::NarrowInlineOp:
    {
        this->evalNarrowInlineOp(static_cast<const ExtractOp<OpCodeTag::NarrowInlineOp>*>(op));
    }
    case OpCodeTag::LoadConstOp:
    {
        this->evalLoadConstOp(static_cast<const ExtractOp<OpCodeTag::LoadConstOp*>(op));
    }
    case OpCodeTag::TupleHasIndexOp:
    {
        this->evalTupleHasIndexOp(static_cast<const OpCodeTag::TupleHasIndexOp*>(op));
    }
    case OpCodeTag::RecordHasPropertyOp:
    {
        this->evalRecordHasPropertyOp(static_cast<const OpCodeTag::RecordHasPropertyOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexDirectOp:
    {
        this->evalLoadTupleIndexDirectOp(static_cast<const OpCodeTag::LoadTupleIndexDirectOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexVirtualOp:
    {
        this->evalLoadTupleIndexVirtualOp(static_cast<const OpCodeTag::LoadTupleIndexVirtualOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexSetGuardDirectOp:
    {
        this->evalLoadTupleIndexSetGuardDirectOp(static_cast<const OpCodeTag::LoadTupleIndexSetGuardDirectOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexSetGuardVirtualOp:
    {
        this->evalLoadTupleIndexSetGuardVirtualOp(static_cast<const OpCodeTag::LoadTupleIndexSetGuardVirtualOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertyDirectOp:
    {
        this->evalLoadRecordPropertyDirectOp(static_cast<const OpCodeTag::LoadRecordPropertyDirectOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertyVirtualOp:
    {
        this->evalLoadRecordPropertyVirtualOp(static_cast<const OpCodeTag::LoadRecordPropertyVirtualOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertySetGuardDirectOp:
    {
        this->evalLoadRecordPropertySetGuardDirectOp(static_cast<const OpCodeTag::LoadRecordPropertySetGuardDirectOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertySetGuardVirtualOp:
    {
        this->evalLoadRecordPropertySetGuardVirtualOp(static_cast<const OpCodeTag::LoadRecordPropertySetGuardVirtualOp*>(op));
    }
    case OpCodeTag::LoadEnityFieldDirectOp:
    {
        this->evalLoadDirectFieldOp(static_cast<const OpCodeTag::LoadEnityFieldDirectOp*>(op));
    }
    case OpCodeTag::LoadEnityFieldVirtualOp:
    {
        this->evalLoadVirtualFieldOp(static_cast<const OpCodeTag::LoadEnityFieldVirtualOp*>(op));
    }
    case OpCodeTag::LoadFromEpehmeralListOp:
    {
        this->evalLoadFromEpehmeralListOp(static_cast<const OpCodeTag::LoadFromEpehmeralListOp*>(op));
    }
    case OpCodeTag::InvokeFixedFunctionOp:
    {
        this->evalInvokeFixedFunctionOp(static_cast<const OpCodeTag::InvokeFixedFunctionOp*>(op));
    }
    case OpCodeTag::InvokeFixedFunctionWGuardOp:
    {
        this->evalInvokeFixedFunctionWGuardOp(static_cast<const OpCodeTag::InvokeFixedFunctionWGuardOp*>(op));
    }
    case OpCodeTag::InvokeVirtualFunctionOp,
    case OpCodeTag::InvokeVirtualOperatorOp,
    case OpCodeTag::ConstructorTupleOp,
    case OpCodeTag::ConstructorRecordOp,
    case OpCodeTag::ConstructorEphemeralListOp,
    case OpCodeTag::ConstructorPrimaryCollectionEmptyOp,
    case OpCodeTag::ConstructorPrimaryCollectionSingletonsOp,
    case OpCodeTag::ConstructorPrimaryCollectionCopiesOp,
    case OpCodeTag::ConstructorPrimaryCollectionMixedOp,
    case OpCodeTag::PrefixNotOp,
    case OpCodeTag::AllTrueOp,
    case OpCodeTag::SomeTrueOp,
    case OpCodeTag::IsNoneOp,
    case OpCodeTag::IsSomeOp,
    case OpCodeTag::TypeTagIsOp,
    case OpCodeTag::TypeTagSubtypeOfOp,
    case OpCodeTag::JumpOp,
    case OpCodeTag::JumpCondOp,
    case OpCodeTag::JumpNoneOp,
    case OpCodeTag::RegisterAssignOp,
    case OpCodeTag::ReturnAssignOp,
    case OpCodeTag::ReturnAssignOfConsOp,
    case OpCodeTag::VarLifetimeStartOp,
    case OpCodeTag::VarLifetimeEndOp,

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
    EqStringOp,
    NeqNatOp,
    NeqIntOp,
    NeqBigNatOp,
    NeqBigIntOp,
    NeqRationalOp,
    NeqStringOp,

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
    GeFloatOp,
    GeDecimalOp
    };
}


