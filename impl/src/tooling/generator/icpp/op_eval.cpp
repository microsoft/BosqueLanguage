//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

//Big Macro for generating code for primitive checked binary operations
#define PrimitiveBinaryOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATOR, ERROR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
REPRTYPE res; \
bool safe = OPERATOR(larg, rarg, res); \
BSQ_LANGUAGE_ASSERT(safe, THIS->dbg_currentFile, THIS->dbg_currentLine, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);

//Big Macro for generating code for primitive checked rhsarg is non-zero binary operations
#define PrimitiveBinaryOperatorMacroCheckedDiv(THIS, OP, TAG, REPRTYPE) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
BSQ_LANGUAGE_ASSERT(rarg != 0, THIS->dbg_currentFile, THIS->dbg_currentLine, "Division by 0"); \
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), larg / rarg);

//Big Macro for generating code for primitive un-checked infix binary operations
#define PrimitiveBinaryOperatorMacroSafe(THIS, OP, TAG, REPRTYPE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);

//Big Macro for generating code for primitive infix equality operations
#define PrimitiveBinaryComparatorMacroSafe(THIS, OP, TAG, REPRTYPE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);

//Big Macro for generating code for primitive infix equality operations
#define PrimitiveBinaryComparatorMacroFP(THIS, OP, TAG, REPRTYPE, ISNAN, ISINFINITE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
BSQ_LANGUAGE_ASSERT(!ISNAN(rarg) & !ISNAN(larg), THIS->dbg_currentFile, THIS->dbg_currentLine, "NaN cannot be ordered"); \
BSQ_LANGUAGE_ASSERT((!ISINFINITE(rarg) | !ISINFINITE(larg)) || ((rarg <= 0) & (0 <= larg)) || ((larg <= 0) & (0 <= rarg)), THIS->dbg_currentFile, THIS->dbg_currentLine, "Infinte values cannot be ordered"); \
BSQ_LANGUAGE_ASSERT(rarg != 0, THIS->dbg_currentFile, THIS->dbg_currentLine, "Division by 0"); \
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);

StorageLocationPtr Evaluator::evalConstArgument(Argument arg)
{
    switch (arg.kind)
    {
    case ArgumentTag::ConstNone:
        return &Environment::g_constNone;
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
void Evaluator::evalBoxUniqueRegisterToInlineOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        SLPTR_STORE_UNION_INLINE_TYPE(isl, op->fromtype);
        SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), this->evalArgument(op->arg), op->fromtype->allocsize));
    }
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
void Evaluator::evalBoxUniqueRegisterToHeapOp(const BoxOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto isl = this->evalTargetVar(op->trgt);
        if(op->fromtype->tid == BSQ_TYPE_ID_NONE)
        {
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, BSQNoneHeapValue);
        }
        else
        {
            auto balloc = Allocator::allocateDynamic(op->fromtype);
            SLPTR_COPY_CONTENTS(balloc, this->evalArgument(op->arg), op->fromtype->allocsize);
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, balloc);
        }
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
        if(rtype->tid == BSQ_TYPE_ID_NONE)
        {
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, BSQNoneHeapValue);
        }
        else
        {
            auto balloc = Allocator::allocateDynamic(rtype);
            SLPTR_COPY_CONTENTS(balloc, SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl), rtype->allocsize);
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(isl, balloc);
        }
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalExtractUniqueRegisterFromInlineOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto sldata = SLPTR_LOAD_UNION_INLINE_DATAPTR(srcl);
        SLPTR_COPY_CONTENTS(this->evalTargetVar(op->trgt), sldata, op->intotype->allocsize);
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
void Evaluator::evalExtractUniqueRegisterFromHeapOp(const ExtractOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->intotype, op->sguard))
    {
        auto srcl = this->evalArgument(op->arg);
        auto sldata = SLPTR_LOAD_UNION_HEAP_DATAPTR(srcl);

        if(sldata == BSQNoneHeapValue)
        {
            SLPTR_STORE_CONTENTS_AS(BSQNone, isl, BSQNoneValue);
        }
        else
        {
            SLPTR_COPY_CONTENTS(this->evalTargetVar(op->trgt), sldata, op->intotype->allocsize);
        }
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
        auto sldata = SLPTR_LOAD_UNION_HEAP_DATAPTR(srcl);

        auto isl = this->evalTargetVar(op->trgt);
        if(sldata == BSQNoneHeapValue)
        {
            SLPTR_STORE_UNION_INLINE_TYPE(isl, Environment::g_typeNone);
            SLPTR_STORE_CONTENTS_AS(BSQNone, SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), BSQNoneValue);
        }
        else
        {
            auto rtype = SLPTR_LOAD_UNION_HEAP_TYPE(srcl);
        
            SLPTR_STORE_UNION_INLINE_TYPE(isl, rtype);
            SLPTR_COPY_CONTENTS(SLPTR_LOAD_UNION_INLINE_DATAPTR(isl), sldata, rtype->allocsize);
        }
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
    auto ttype = this->loadBSQTypeFromAbstractLocationOfType<BSQTupleType>(src, srctype);
    auto voffset = ttype->idxoffsets[idx];
    this->processTupleDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    this->storeValue(this->evalTargetVar(dst), this->indexStorageLocationOffset(src, slotoffset, srctype), dsttype);
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    auto rtype = this->loadBSQTypeFromAbstractLocationOfType<BSQRecordType>(src, srctype);
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
    auto etype = this->loadBSQTypeFromAbstractLocationOfType<BSQEntityType>(src, srctype);
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
    auto ttype = this->loadBSQTypeFromAbstractLocationOfType<BSQTupleType>(sl, op->layouttype);
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)(op->idx < ttype->maxIndex));
}

void Evaluator::evalRecordHasPropertyOp(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto rtype = this->loadBSQTypeFromAbstractLocationOfType<BSQRecordType>(sl, op->layouttype);
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
    auto argtype = this->loadBSQTypeFromAbstractLocationOfType<BSQTupleType>(sl, op->layouttype);
    
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
    auto argtype = this->loadBSQTypeFromAbstractLocationOfType<BSQRecordType>(sl, op->layouttype);

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
    const BSQType* tl = nullptr;
    StorageLocationPtr cl = nullptr; 
    StorageLocationPtr sll = this->evalArgument(op->argl);
    if(op->argltype->tkind == BSQTypeKind::Register || op->argltype->tkind == BSQTypeKind::Struct || op->argltype->tkind == BSQTypeKind::Ref)
    {
        tl = op->argltype;
        cl = sll;
    }
    else
    {
        tl = this->loadBSQTypeFromAbstractLocationGeneral(sll, op->argllayout);
        cl = this->loadDataPtrFromAbstractLocation(sll, op->argllayout);
    }

    const BSQType* tr = nullptr;
    StorageLocationPtr cr = nullptr; 
    StorageLocationPtr slr = this->evalArgument(op->argr);
    if(op->argrtype->tkind == BSQTypeKind::Register || op->argrtype->tkind == BSQTypeKind::Struct || op->argrtype->tkind == BSQTypeKind::Ref)
    {
        tr = op->argrtype;
        cr = slr;
    }
    else
    {
        tr = this->loadBSQTypeFromAbstractLocationGeneral(slr, op->argrlayout);
        cr = this->loadDataPtrFromAbstractLocation(slr, op->argrlayout);
    }

    if(tl->tid != tr->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), BSQFALSE);
    }
    else
    {
        bool eqcontents = tl->fpKeyEqual(cl, cr);
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)eqcontents);
    }
}

void Evaluator::evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op)
{
    //Get types for the values -- either virtual or direct
    //Make sure they are ordered -- otherwise call virtual < op
    //Get types for the values -- either virtual or direct
    //Make sure they are equal -- otherwise call virtual eq op
    const BSQType* tl = nullptr;
    StorageLocationPtr cl = nullptr; 
    StorageLocationPtr sll = this->evalArgument(op->argl);
    if(op->argltype->tkind == BSQTypeKind::Register || op->argltype->tkind == BSQTypeKind::Struct || op->argltype->tkind == BSQTypeKind::Ref)
    {
        tl = op->argltype;
        cl = sll;
    }
    else
    {
        tl = this->loadBSQTypeFromAbstractLocationGeneral(sll, op->argllayout);
        cl = this->loadDataPtrFromAbstractLocation(sll, op->argllayout);
    }

    const BSQType* tr = nullptr;
    StorageLocationPtr cr = nullptr; 
    StorageLocationPtr slr = this->evalArgument(op->argr);
    if(op->argrtype->tkind == BSQTypeKind::Register || op->argrtype->tkind == BSQTypeKind::Struct || op->argrtype->tkind == BSQTypeKind::Ref)
    {
        tr = op->argrtype;
        cr = slr;
    }
    else
    {
        tr = this->loadBSQTypeFromAbstractLocationGeneral(slr, op->argrlayout);
        cr = this->loadDataPtrFromAbstractLocation(slr, op->argrlayout);
    }

    if(tl->tid != tr->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)tl->tid < tr->tid);
    }
    else
    {
        bool lesscontents = tl->fpKeyLess(cl, cr);
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)lesscontents);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalIsNoneOp(const TypeIsNoneOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, &Evaluator::g_boolType, op->sguard))
    {
        BSQBool isnone = this->loadBSQTypeFromAbstractLocationGeneral(this->evalArgument(op->arg), op->arglayout)->tid == BSQ_TYPE_ID_NONE;
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), isnone);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalIsSomeOp(const TypeIsSomeOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, &Evaluator::g_boolType, op->sguard))
    {
        BSQBool issome = this->loadBSQTypeFromAbstractLocationGeneral(this->evalArgument(op->arg), op->arglayout)->tid != BSQ_TYPE_ID_NONE;
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), issome);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalTypeTagIsOp(const TypeTagIsOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, &Evaluator::g_boolType, op->sguard))
    {
        auto istype = this->loadBSQTypeFromAbstractLocationGeneral(this->evalArgument(op->arg), op->arglayout)->tid == op->oftype->tid;
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), istype);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, &Evaluator::g_boolType, op->sguard))
    {
        auto tt = this->loadBSQTypeFromAbstractLocationGeneral(this->evalArgument(op->arg), op->arglayout);
        BSQBool subtype = tt->subtypes.find(op->oftype->tid) != tt->subtypes.cend();
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), subtype);
    }
}

InterpOp* Evaluator::evalJumpOp(const JumpOp* op)
{
    return this->advanceCurrentOp(op->offset);
}

InterpOp* Evaluator::evalJumpCondOp(const JumpCondOp* op)
{
    BSQBool jc = SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(op->arg));
    if(jc)
    {
        return this->advanceCurrentOp(op->toffset);
    }
    else
    {
        return this->advanceCurrentOp(op->foffset);
    }
}

InterpOp* Evaluator::evalJumpNoneOp(const JumpNoneOp* op)
{
    BSQBool isnone = this->loadBSQTypeFromAbstractLocationGeneral(this->evalArgument(op->arg), op->arglayout)->tid == BSQ_TYPE_ID_NONE;
    
    if(isnone)
    {
        return this->advanceCurrentOp(op->noffset);
    }
    else
    {
        return this->advanceCurrentOp(op->soffset);
    }
}

template <OpCodeTag tag, bool isGuarded>
void Evaluator::evalRegisterAssignOp(const RegisterAssignOp<tag, isGuarded>* op)
{
    if(this->tryProcessGuardStmt<isGuarded>(op->trgt, op->oftype, op->sguard))
    {
        this->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg), op->oftype);
    }
}

void Evaluator::evalReturnAssignOp(const ReturnAssignOp* op, StorageLocationPtr resultsl)
{
    this->storeValue(resultsl, this->evalArgument(op->arg), op->oftype);
}

void Evaluator::evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op, StorageLocationPtr resultsl)
{
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->tkind == BSQTypeKind::Register || op->oftype->tkind == BSQTypeKind::Struct)
    {
        tcontents = resultsl;
    }
    else
    {
        tcontents = Allocator::GlobalAllocator.allocateDynamic(op->oftype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, tcontents);
    }

    for(size_t i = 0; i < op->oftype->fieldoffsets.size(); ++i)
    {
        this->storeValue(this->indexStorageLocationOffset(tcontents, op->oftype->fieldoffsets[i], op->oftype), this->evalArgument(op->args[i]), op->oftype->ftypes[i]);
    }
}

void Evaluator::evalVarLifetimeStartOp(const VarLifetimeStartOp* op)
{
    assert(false);
}

void Evaluator::evalVarLifetimeEndOp(const VarLifetimeEndOp* op)
{
    assert(false);
}

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
    case OpCodeTag::BoxUniqueRegisterToInlineOp:
    {
        this->evalBoxUniqueRegisterToInlineOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRegisterToInlineOp, false>*>(op));
    }
    case OpCodeTag::BoxUniqueStructToInlineOp:
    {
        this->evalBoxUniqueStructToInlineOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueStructToInlineOp, false>*>(op));
    }
    case OpCodeTag::BoxUniqueRefToInlineOp:
    {
        this->evalBoxUniqueRefToInlineOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRefToInlineOp, false>*>(op));
    }
    case OpCodeTag::BoxUniqueRegisterToHeapOp:
    {
        this->evalBoxUniqueRegisterToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRegisterToHeapOp, false>*>(op));
    }
    case OpCodeTag::BoxUniqueStructToHeapOp:
    {
        this->evalBoxUniqueStructToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueStructToHeapOp, false>*>(op));
    }
    case OpCodeTag::BoxUniqueRefToHeapOp:
    {
        this->evalBoxUniqueRefToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxUniqueRefToHeapOp, false>*>(op));
    }
    case OpCodeTag::BoxInlineBoxToHeapOp:
    {
        this->evalBoxInlineBoxToHeapOp(static_cast<const BoxOp<OpCodeTag::BoxInlineBoxToHeapOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueRegisterFromInlineOp:
    {
        this->evalExtractUniqueRegisterFromInlineOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRegisterFromInlineOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueStructFromInlineOp:
    {
        this->evalExtractUniqueStructFromInlineOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueStructFromInlineOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueRefFromInlineOp:
    {
        this->evalExtractUniqueRefFromInlineOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRefFromInlineOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueRegisterFromHeapOp:
    {
        this->evalExtractUniqueRegisterFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRegisterFromHeapOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueStructFromHeapOp:
    {
        this->evalExtractUniqueStructFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueStructFromHeapOp, false>*>(op));
    }
    case OpCodeTag::ExtractUniqueRefFromHeapOp:
    {
        this->evalExtractUniqueRefFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractUniqueRefFromHeapOp, false>*>(op));
    }
    case OpCodeTag::ExtractInlineBoxFromHeapOp:
    {
        this->evalExtractInlineBoxFromHeapOp(static_cast<const ExtractOp<OpCodeTag::ExtractInlineBoxFromHeapOp, false>*>(op));
    }
    case OpCodeTag::WidenInlineOp:
    {
        this->evalWidenInlineOp(static_cast<const BoxOp<OpCodeTag::WidenInlineOp, false>*>(op));
    }
    case OpCodeTag::NarrowInlineOp:
    {
        this->evalNarrowInlineOp(static_cast<const ExtractOp<OpCodeTag::NarrowInlineOp, false>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueRegisterToInlineOp:
    {
        this->evalBoxUniqueRegisterToInlineOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueRegisterToInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueStructToInlineOp:
    {
        this->evalBoxUniqueStructToInlineOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueStructToInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueRefToInlineOp:
    {
        this->evalBoxUniqueRefToInlineOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueRefToInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueRegisterToHeapOp:
    {
        this->evalBoxUniqueRegisterToHeapOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueRegisterToHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueStructToHeapOp:
    {
        this->evalBoxUniqueStructToHeapOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueStructToHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxUniqueRefToHeapOp:
    {
        this->evalBoxUniqueRefToHeapOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxUniqueRefToHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedBoxInlineBoxToHeapOp:
    {
        this->evalBoxInlineBoxToHeapOp(static_cast<const BoxOp<OpCodeTag::GuardedBoxInlineBoxToHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueRegisterFromInlineOp:
    {
        this->evalExtractUniqueRegisterFromInlineOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueRegisterFromInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueStructFromInlineOp:
    {
        this->evalExtractUniqueStructFromInlineOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueStructFromInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueRefFromInlineOp:
    {
        this->evalExtractUniqueRefFromInlineOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueRefFromInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueRegisterFromHeapOp:
    {
        this->evalExtractUniqueRegisterFromHeapOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueRegisterFromHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueStructFromHeapOp:
    {
        this->evalExtractUniqueStructFromHeapOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueStructFromHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractUniqueRefFromHeapOp:
    {
        this->evalExtractUniqueRefFromHeapOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractUniqueRefFromHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedExtractInlineBoxFromHeapOp:
    {
        this->evalExtractInlineBoxFromHeapOp(static_cast<const ExtractOp<OpCodeTag::GuardedExtractInlineBoxFromHeapOp, true>*>(op));
    }
    case OpCodeTag::GuardedWidenInlineOp:
    {
        this->evalWidenInlineOp(static_cast<const BoxOp<OpCodeTag::GuardedWidenInlineOp, true>*>(op));
    }
    case OpCodeTag::GuardedNarrowInlineOp:
    {
        this->evalNarrowInlineOp(static_cast<const ExtractOp<OpCodeTag::GuardedNarrowInlineOp, true>*>(op));
    }
    case OpCodeTag::LoadConstOp:
    {
        this->evalLoadConstOp(static_cast<const LoadConstOp*>(op));
    }
    case OpCodeTag::TupleHasIndexOp:
    {
        this->evalTupleHasIndexOp(static_cast<const TupleHasIndexOp*>(op));
    }
    case OpCodeTag::RecordHasPropertyOp:
    {
        this->evalRecordHasPropertyOp(static_cast<const RecordHasPropertyOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexDirectOp:
    {
        this->evalLoadTupleIndexDirectOp(static_cast<const LoadTupleIndexDirectOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexVirtualOp:
    {
        this->evalLoadTupleIndexVirtualOp(static_cast<const LoadTupleIndexVirtualOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexSetGuardDirectOp:
    {
        this->evalLoadTupleIndexSetGuardDirectOp(static_cast<const LoadTupleIndexSetGuardDirectOp*>(op));
    }
    case OpCodeTag::LoadTupleIndexSetGuardVirtualOp:
    {
        this->evalLoadTupleIndexSetGuardVirtualOp(static_cast<const LoadTupleIndexSetGuardVirtualOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertyDirectOp:
    {
        this->evalLoadRecordPropertyDirectOp(static_cast<const LoadRecordPropertyDirectOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertyVirtualOp:
    {
        this->evalLoadRecordPropertyVirtualOp(static_cast<const LoadRecordPropertyVirtualOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertySetGuardDirectOp:
    {
        this->evalLoadRecordPropertySetGuardDirectOp(static_cast<const LoadRecordPropertySetGuardDirectOp*>(op));
    }
    case OpCodeTag::LoadRecordPropertySetGuardVirtualOp:
    {
        this->evalLoadRecordPropertySetGuardVirtualOp(static_cast<const LoadRecordPropertySetGuardVirtualOp*>(op));
    }
    case OpCodeTag::LoadEntityFieldDirectOp:
    {
        this->evalLoadDirectFieldOp(static_cast<const LoadEntityFieldDirectOp*>(op));
    }
    case OpCodeTag::LoadEntityFieldVirtualOp:
    {
        this->evalLoadVirtualFieldOp(static_cast<const LoadEntityFieldVirtualOp*>(op));
    }
    case OpCodeTag::LoadFromEpehmeralListOp:
    {
        this->evalLoadFromEpehmeralListOp(static_cast<const LoadFromEpehmeralListOp*>(op));
    }
    case OpCodeTag::InvokeFixedFunctionOp:
    {
        this->evalInvokeFixedFunctionOp(static_cast<const InvokeFixedFunctionOp<OpCodeTag::InvokeFixedFunctionOp, false>*>(op));
    }
    case OpCodeTag::GuardedInvokeFixedFunctionOp:
    {
        this->evalInvokeFixedFunctionOp(static_cast<const InvokeFixedFunctionOp<OpCodeTag::GuardedInvokeFixedFunctionOp, true>*>(op));
    }
    case OpCodeTag::InvokeVirtualFunctionOp:
    {
        this->evalInvokeVirtualFunctionOp(static_cast<const InvokeVirtualFunctionOp*>(op));
    }
    case OpCodeTag::InvokeVirtualOperatorOp:
    {
        this->evalInvokeVirtualOperatorOp(static_cast<const InvokeVirtualOperatorOp*>(op));
    }
    case OpCodeTag::ConstructorTupleOp:
    {
        this->evalConstructorTupleOp(static_cast<const ConstructorTupleOp*>(op));
    }
    case OpCodeTag::ConstructorRecordOp:
    {
        this->evalConstructorRecordOp(static_cast<const ConstructorRecordOp*>(op));
    }
    case OpCodeTag::ConstructorEphemeralListOp:
    {
        this->evalConstructorEphemeralListOp(static_cast<const ConstructorEphemeralListOp*>(op));
    }
    case OpCodeTag::ConstructorPrimaryCollectionEmptyOp:
    {
        this->evalConstructorPrimaryCollectionEmptyOp(static_cast<const ConstructorPrimaryCollectionEmptyOp*>(op));
    }
    case OpCodeTag::ConstructorPrimaryCollectionSingletonsOp:
    {
        this->evalConstructorPrimaryCollectionSingletonsOp(static_cast<const ConstructorPrimaryCollectionSingletonsOp*>(op));
    }
    case OpCodeTag::ConstructorPrimaryCollectionCopiesOp:
    {
        this->evalConstructorPrimaryCollectionCopiesOp(static_cast<const ConstructorPrimaryCollectionCopiesOp*>(op));
    }
    case OpCodeTag::ConstructorPrimaryCollectionMixedOp:
    {
        this->evalConstructorPrimaryCollectionMixedOp(static_cast<const ConstructorPrimaryCollectionMixedOp*>(op));
    }
    case OpCodeTag::PrefixNotOp:
    {
        this->evalPrefixNotOp(static_cast<const PrefixNotOp*>(op));
    }
    case OpCodeTag::AllTrueOp:
    {
        this->evalAllTrueOp(static_cast<const AllTrueOp*>(op));
    }
    case OpCodeTag::SomeTrueOp:
    {
        this->evalSomeTrueOp(static_cast<const SomeTrueOp*>(op));
    }
    case OpCodeTag::BinKeyEqVirtualOp:
    {
        this->evalBinKeyEqVirtualOp(static_cast<const BinKeyEqVirtualOp*>(op));
    }
    case OpCodeTag::BinKeyLessVirtualOp:
    {
        this->evalBinKeyLessVirtualOp(static_cast<const BinKeyLessVirtualOp*>(op));
    }
    case OpCodeTag::TypeIsNoneOp:
    {
        this->evalIsNoneOp(static_cast<const TypeIsNoneOp<OpCodeTag::TypeIsNoneOp, false>*>(op));
    }
    case OpCodeTag::TypeIsSomeOp:
    {
        this->evalIsSomeOp(static_cast<const TypeIsSomeOp<OpCodeTag::TypeIsSomeOp, false>*>(op));
    }
    case OpCodeTag::TypeTagIsOp:
    {
        this->evalTypeTagIsOp(static_cast<const TypeTagIsOp<OpCodeTag::TypeTagIsOp, false>*>(op));
    }
    case OpCodeTag::TypeTagSubtypeOfOp:
    {
        this->evalTypeTagSubtypeOfOp(static_cast<const TypeTagSubtypeOfOp<OpCodeTag::TypeTagSubtypeOfOp, false>*>(op));
    }
    case OpCodeTag::GuardedTypeIsNoneOp:
    {
        this->evalIsNoneOp(static_cast<const TypeIsNoneOp<OpCodeTag::GuardedTypeIsNoneOp, true>*>(op));
    }
    case OpCodeTag::GuardedTypeIsSomeOp:
    {
        this->evalIsSomeOp(static_cast<const TypeIsSomeOp<OpCodeTag::GuardedTypeIsSomeOp, true>*>(op));
    }
    case OpCodeTag::GuardedTypeTagIsOp:
    {
        this->evalTypeTagIsOp(static_cast<const TypeTagIsOp<OpCodeTag::GuardedTypeTagIsOp, true>*>(op));
    }
    case OpCodeTag::GuardedTypeTagSubtypeOfOp:
    {
        this->evalTypeTagSubtypeOfOp(static_cast<const TypeTagSubtypeOfOp<OpCodeTag::GuardedTypeTagSubtypeOfOp, true>*>(op));
    }
    //
    // ---- jump operations are handled in the outer loop ----
    //
    case OpCodeTag::RegisterAssignOp:
    {
        this->evalRegisterAssignOp(static_cast<const RegisterAssignOp<OpCodeTag::RegisterAssignOp, false>*>(op));
    }
    case OpCodeTag::GuardedRegisterAssignOp:
    {
        this->evalRegisterAssignOp(static_cast<const RegisterAssignOp<OpCodeTag::GuardedRegisterAssignOp, true>*>(op));
    }
    //
    // ---- return operations are handled in the outer loop ----
    //
#ifdef BSQ_DEBUG_BUILD 
    case OpCodeTag::VarLifetimeStartOp:
    {
        this->evalVarLifetimeStartOp(static_cast<const VarLifetimeStartOp*>(op));
    }
    case OpCodeTag::VarLifetimeEndOp:
    {
        this->evalVarLifetimeEndOp(static_cast<const VarLifetimeEndOp*>(op));
    }
#endif
    case OpCodeTag::AddNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddNatOp, BSQNat, __builtin_add_overflow, "Nat addition overflow")
    }
    case OpCodeTag::AddIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddIntOp, BSQInt, __builtin_add_overflow, "Int addition overflow/underflow")
    }
    case OpCodeTag::AddBigNatOp:
    {
        assert(false);
    }
    case OpCodeTag::AddBigIntOp:
    {
        assert(false);
    }
    case OpCodeTag::AddRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::AddFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddFloatOp, BSQFloat, +)
    }
    case OpCodeTag::AddDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddDecimalOp, BSQDecimal, +)
    }
    case OpCodeTag::SubNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubNatOp, BSQNat, __builtin_sub_overflow, "Nat subtraction overflow")
    }
    case OpCodeTag::SubIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubIntOp, BSQInt, __builtin_sub_overflow, "Int subtraction overflow/underflow")
    }
    case OpCodeTag::SubBigNatOp:
    {
        assert(false);
    }
    case OpCodeTag::SubBigIntOp:
    {
        assert(false);
    }
    case OpCodeTag::SubRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::SubFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubFloatOp, BSQFloat, -)
    }
    case OpCodeTag::SubDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubDecimalOp, BSQDecimal, -)
    }
    case OpCodeTag::MultNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultNatOp, BSQNat, __builtin_mul_overflow, "Nat multiplication overflow")
    }
    case OpCodeTag::MultIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultIntOp, BSQInt, __builtin_mul_overflow, "Int multiplication underflow/overflow")
    }
    case OpCodeTag::MultBigNatOp:
    {
        assert(false);
    }
    case OpCodeTag::MultBigIntOp:
    {
        assert(false);
    }
    case OpCodeTag::MultRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::MultFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultFloatOp, BSQFloat, *)
    }
    case OpCodeTag::MultDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultDecimalOp, BSQDecimal, *)
    }
    case OpCodeTag::DivNatOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivNatOp, BSQNat)
    }
    case OpCodeTag::DivIntOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivIntOp, BSQInt)
    }
    case OpCodeTag::DivBigNatOp:
    {
        assert(false);
    }
    case OpCodeTag::DivBigIntOp:
    {
        assert(false);
    }
    case OpCodeTag::DivRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::DivFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::DivFloatOp, BSQFloat, /)
    }
    case OpCodeTag::DivDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::DivDecimalOp, BSQDecimal, /)
    }
    case OpCodeTag::EqNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqNatOp, BSQNat, ==)
    }
    case OpCodeTag::EqIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqIntOp, BSQInt, ==)
    }
    case OpCodeTag::EqBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqBigNatOp, BSQBigNat, ==)
    }
    case OpCodeTag::EqBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqBigIntOp, BSQBigInt, ==)
    }
    case OpCodeTag::EqRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::NeqNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqNatOp, BSQNat, !=)
    }
    case OpCodeTag::NeqIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqIntOp, BSQInt, !=)
    }
    case OpCodeTag::NeqBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqBigNatOp, BSQBigNat, !=)
    }
    case OpCodeTag::NeqBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqBigIntOp, BSQBigInt, !=)
    }
    case OpCodeTag::NeqRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::LtNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtNatOp, BSQNat, <)
    }
    case OpCodeTag::LtIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtIntOp, BSQInt, <)
    }
    case OpCodeTag::LtBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtBigNatOp, BSQBigNat, <)
    }
    case OpCodeTag::LtBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtBigIntOp, BSQBigInt, <)
    }
    case OpCodeTag::LtRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::LtFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LtFloatOp, BSQFloat, boost::math::isnan, boost::math::isinf, <)
    }
    case OpCodeTag::LtDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LtDecimalOp, BSQDecimal, boost::math::isnan, boost::math::isinf, <)
    }
    case OpCodeTag::GtNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GtNatOp, BSQNat, >)
    }
    case OpCodeTag::GtIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GtIntOp, BSQInt, >)
    }
    case OpCodeTag::GtBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GtBigNatOp, BSQBigNat, >)
    }
    case OpCodeTag::GtBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GtBigIntOp, BSQBigInt, >)
    }
    case OpCodeTag::GtRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::GtFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::GtFloatOp, BSQFloat, boost::math::isnan, boost::math::isinf, >)
    }
    case OpCodeTag::GtDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::GtDecimalOp, BSQDecimal, boost::math::isnan, boost::math::isinf, >)
    }
    case OpCodeTag::LeNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeNatOp, BSQNat, <=)
    }
    case OpCodeTag::LeIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeIntOp, BSQInt, <=)
    }
    case OpCodeTag::LeBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeBigNatOp, BSQBigNat, <=)
    }
    case OpCodeTag::LeBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeBigIntOp, BSQBigInt, <=)
    }
    case OpCodeTag::LeRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::LeFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LeFloatOp, BSQFloat, boost::math::isnan, boost::math::isinf, <=)
    }
    case OpCodeTag::LeDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LeDecimalOp, BSQDecimal, boost::math::isnan, boost::math::isinf, <=)
    }
    case OpCodeTag::GeNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GeNatOp, BSQNat, >=)
    }
    case OpCodeTag::GeIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GeIntOp, BSQInt, >=)
    }
    case OpCodeTag::GeBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GeBigNatOp, BSQBigNat, >=)
    }
    case OpCodeTag::GeBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::GeBigIntOp, BSQBigInt, >=)
    }
    case OpCodeTag::GeRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::GeFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::GeFloatOp, BSQFloat, boost::math::isnan, boost::math::isinf, >=)
    }
    case OpCodeTag::GeDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::GeDecimalOp, BSQDecimal, boost::math::isnan, boost::math::isinf, >=)
    }
    case OpCodeTag::EqStringOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::EqStringOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::EqStringOp>*>(op);
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), BSQString::equalOperator(this->evalArgument(bop->larg), this->evalArgument(bop->rarg)));
    }
    case OpCodeTag::NeqStringOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::NeqStringOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::NeqStringOp>*>(op);
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), !BSQString::equalOperator(this->evalArgument(bop->larg), this->evalArgument(bop->rarg)));
    }
    case OpCodeTag::LessStringOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::LessStringOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::LessStringOp>*>(op);
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), BSQString::lessOperator(this->evalArgument(bop->larg), this->evalArgument(bop->rarg)));
    }
    default:
    {
        assert(false);
    }
    }
}

void Evaluator::evaluateOpCodeBlocks()
{
    InterpOp* op = this->getCurrentOp();
    while(true)
    {
        switch(op->tag)
        {
        case OpCodeTag::ReturnAssignOp:
        case OpCodeTag::ReturnAssignOfConsOp:
        {
            break;
        }
        case OpCodeTag::JumpOp:
        {
            op = this->evalJumpOp(static_cast<const JumpOp*>(op));
        }
        case OpCodeTag::JumpCondOp:
        {
            op = this->evalJumpCondOp(static_cast<const JumpCondOp*>(op));
        }
        case OpCodeTag::JumpNoneOp:
        {
            op = this->evalJumpNoneOp(static_cast<const JumpNoneOp*>(op));
        }
        default:
        {
            this->evaluateOpCode(op);
            op = this->advanceCurrentOp();
        }
        }
    }
}
    
void Evaluator::evaluateBody(StorageLocationPtr resultsl)
{
    this->evaluateOpCodeBlocks();
    
    InterpOp* op = this->getCurrentOp();
    if(op->tag == OpCodeTag::ReturnAssignOp)
    {  
        this->evalReturnAssignOp(static_cast<const ReturnAssignOp*>(op), resultsl);
    }
    else 
    {
        assert(op->tag == OpCodeTag::ReturnAssignOfConsOp);
        this->evalReturnAssignOfConsOp(static_cast<const ReturnAssignOfConsOp*>(op), resultsl);
    }
}


