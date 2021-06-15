//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

#include <boost/safe_numerics/checked_default.hpp>

///Big Macro for generating code for primitive checked negate operations
#define PrimitiveNegateOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATOR, ERROR) const PrimitiveNegateOperatorOp<TAG>* bop = static_cast<const PrimitiveNegateOperatorOp<TAG>*>(op); \
auto res = OPERATOR(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->arg))); \
BSQ_LANGUAGE_ASSERT(!res.exception(), THIS->cframe->dbg_file, THIS->cframe->dbg_line, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), static_cast<REPRTYPE>(res));

//Big Macro for generating code for primitive un-checked negate operations
#define PrimitiveNegateOperatorMacroSafe(THIS, OP, TAG, REPRTYPE) const PrimitiveNegateOperatorOp<TAG>* bop = static_cast<const PrimitiveNegateOperatorOp<TAG>*>(op); \
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), -SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->arg)));

//Big Macro for generating code for primitive checked binary operations
#define PrimitiveBinaryOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATOR, ERROR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
auto res = OPERATOR(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)), SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg))); \
BSQ_LANGUAGE_ASSERT(!res.exception(), THIS->cframe->dbg_file, THIS->cframe->dbg_line, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), static_cast<REPRTYPE>(res));

//Big Macro for generating code for primitive checked rhsarg is non-zero binary operations
#define PrimitiveBinaryOperatorMacroCheckedDiv(THIS, OP, TAG, REPRTYPE) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
BSQ_LANGUAGE_ASSERT(rarg != (REPRTYPE)0, THIS->cframe->dbg_file, THIS->cframe->dbg_line, "Division by 0"); \
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), larg / rarg);

//Big Macro for generating code for primitive un-checked infix binary operations
#define PrimitiveBinaryOperatorMacroSafe(THIS, OP, TAG, REPRTYPE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)) OPERATOR SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)));

//Big Macro for generating code for primitive infix equality operations
#define PrimitiveBinaryComparatorMacroSafe(THIS, OP, TAG, REPRTYPE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)) OPERATOR SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)));

//Big Macro for generating code for primitive infix equality operations
#define PrimitiveBinaryComparatorMacroFP(THIS, OP, TAG, REPRTYPE, ISNAN, ISINFINITE, OPERATOR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
BSQ_LANGUAGE_ASSERT(!ISNAN(rarg) & !ISNAN(larg), THIS->cframe->dbg_file, THIS->cframe->dbg_line, "NaN cannot be ordered"); \
BSQ_LANGUAGE_ASSERT((!ISINFINITE(rarg) | !ISINFINITE(larg)) || ((rarg <= 0) & (0 <= larg)) || ((larg <= 0) & (0 <= rarg)), THIS->cframe->dbg_file, THIS->cframe->dbg_line, "Infinte values cannot be ordered"); \
BSQ_LANGUAGE_ASSERT(rarg != 0, THIS->cframe->dbg_file, THIS->cframe->dbg_line, "Division by 0"); \
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);

EvaluatorFrame Evaluator::g_callstack[BSQ_MAX_STACK];

void Evaluator::evalDeadFlowOp()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void Evaluator::evalAbortOp(const AbortOp *op)
{
    BSQ_LANGUAGE_ABORT(op->msg.c_str(), this->cframe->dbg_file, this->cframe->dbg_line);
}

void Evaluator::evalAssertCheckOp(const AssertOp *op)
{
    if (!SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(op->arg)))
    {
        BSQ_LANGUAGE_ABORT(op->msg.c_str(), this->cframe->dbg_file, this->cframe->dbg_line);
    }
}

void Evaluator::evalDebugOp(const DebugOp* op)
{
    if(op->arg.kind == ArgumentTag::InvalidOp)
    {
        //TODO: debugger break here
        assert(false);
    }
    else
    {
        auto dval = op->argtype->fpDisplay(op->argtype, this->evalArgument(op->arg));

        printf("%s\n", dval.c_str());
        fflush(stdout);
    }
}

void Evaluator::evalLoadUnintVariableValueOp(const LoadUnintVariableValueOp* op)
{
    op->oftype->clearValue(this->evalTargetVar(op->trgt));
}

void Evaluator::evalNoneInitUnionOp(const NoneInitUnionOp* op)
{
    auto tl = this->evalTargetVar(op->trgt);
    if(op->oftype->isInline())
    {
        SLPTR_STORE_UNION_INLINE_TYPE(BSQType::g_typeNone, tl);
        SLPTR_STORE_CONTENTS_AS(BSQNone, SLPTR_LOAD_UNION_INLINE_DATAPTR(tl), BSQNoneValue);
    }
    else
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(tl, BSQNoneHeapValue);
    }
}

void Evaluator::evalStoreConstantMaskValueOp(const StoreConstantMaskValueOp* op)
{
    auto mask = this->evalMaskLocation(op->gmaskoffset);
    mask[op->gindex] = op->flag ? BSQTRUE : BSQFALSE;
}

template <>
void Evaluator::evalDirectAssignOp<true>(const DirectAssignOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->intotype, op->sguard))
    {
        op->intotype->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalDirectAssignOp<false>(const DirectAssignOp* op)
{
    op->intotype->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

template <>
void Evaluator::evalBoxOp<true>(const BoxOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->intotype, op->sguard))
    {
        op->intotype->injectIntoUnion(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalBoxOp<false>(const BoxOp* op)
{
    op->intotype->injectIntoUnion(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

template <>
void Evaluator::evalExtractOp<true>(const ExtractOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->intotype, op->sguard))
    {
        op->intotype->extractFromUnion(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalExtractOp<false>(const ExtractOp* op)
{
    op->intotype->extractFromUnion(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

void Evaluator::evalLoadConstOp(const LoadConstOp* op)
{
    op->oftype->storeValue(this->evalTargetVar(op->trgt), Evaluator::evalConstArgument(op->arg));
}

void Evaluator::processTupleDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->storeValue(this->evalTargetVar(dst), srctype->indexStorageLocationOffset(src, slotoffset));
}

void Evaluator::processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype)
{
    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching
    //

    const BSQType* ttype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(srctype, src);
    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    auto voffset = tinfo->idxoffsets[idx];
    this->processTupleDirectLoadAndStore(SLPTR_LOAD_UNION_INLINE_DATAPTR(src), ttype, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->storeValue(this->evalTargetVar(dst), srctype->indexStorageLocationOffset(src, slotoffset));
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching
    //

    const BSQType* rtype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(srctype, src);
    auto rinfo = dynamic_cast<const BSQRecordInfo*>(rtype);
    auto proppos = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), propId);
    assert(proppos != rinfo->properties.cend());

    auto propidx = (size_t)std::distance(rinfo->properties.cbegin(), proppos);
    auto voffset = rinfo->propertyoffsets[propidx];

    this->processRecordDirectLoadAndStore(SLPTR_LOAD_UNION_INLINE_DATAPTR(src), rtype, voffset, dst, dsttype);
}
    
void Evaluator::processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->storeValue(this->evalTargetVar(dst), srctype->indexStorageLocationOffset(src, slotoffset));
}

void Evaluator::processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype)
{
    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

    const BSQType* etype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(srctype, src);
    auto einfo = dynamic_cast<const BSQEntityInfo*>(etype);

    auto fldpos = std::find(einfo->fields.cbegin(), einfo->fields.cend(), fldId);
    assert(fldpos != einfo->fields.cend());

    auto fldidx = (size_t)std::distance(einfo->fields.cbegin(), fldpos);
    auto voffset = einfo->fieldoffsets[fldidx];

    this->processEntityDirectLoadAndStore(src, etype, voffset, dst, dsttype);
}

void Evaluator::processGuardVarStore(const BSQGuard& gv, BSQBool f)
{
    if(gv.gvaroffset == -1)
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
    const BSQType* ttype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(op->layouttype, sl);
    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    
    BSQBool hasidx = op->idx < tinfo->maxIndex;
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), hasidx);
}

void Evaluator::evalRecordHasPropertyOp(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);
    const BSQType* rtype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(op->layouttype, sl);
    auto rinfo = dynamic_cast<const BSQRecordInfo*>(rtype);

    BSQBool hasprop = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), op->propId) != rinfo->properties.cend();
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
    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

    auto sl = this->evalArgument(op->arg);
    const BSQType* ttype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(op->layouttype, sl);
    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    
    BSQBool loadsafe = op->idx < tinfo->maxIndex;
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
    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

    auto sl = this->evalArgument(op->arg);
    const BSQType* rtype = SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(op->layouttype, sl);
    auto rinfo = dynamic_cast<const BSQRecordInfo*>(rtype);

    BSQBool loadsafe = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), op->propId) != rinfo->properties.cend();
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

void Evaluator::evalProjectTupleOp(const ProjectTupleOp* op)
{
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);

        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    auto trgtl = this->evalTargetVar(op->trgt);
    for(size_t i = 0; i < op->idxs.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, op->trgttype->idxoffsets[i]);
        auto src = SLPTR_INDEX_DATAPTR(sl, std::get<1>(op->idxs[i]));

        std::get<2>(op->idxs[i])->storeValue(dst, src);
    }
}

void Evaluator::evalProjectRecordOp(const ProjectRecordOp* op)
{
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);
        
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    auto trgtl = this->evalTargetVar(op->trgt);
    for(size_t i = 0; i < op->props.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, op->trgttype->idxoffsets[i]);
        auto src = SLPTR_INDEX_DATAPTR(sl, std::get<1>(op->props[i]));

        std::get<2>(op->props[i])->storeValue(dst, src);
    }
}

void Evaluator::evalProjectEntityOp(const ProjectEntityOp* op)
{
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);
        
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    auto trgtl = this->evalTargetVar(op->trgt);
    for(size_t i = 0; i < op->fields.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, op->trgttype->idxoffsets[i]);
        auto src = SLPTR_INDEX_DATAPTR(sl, std::get<1>(op->fields[i]));

        std::get<2>(op->fields[i])->storeValue(dst, src);
    }
}

void Evaluator::evalUpdateTupleOp(const UpdateTupleOp* op)
{
    Allocator::GlobalAllocator.ensureSpace(op->trgttype->allocinfo.heapsize);
    
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);
        
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeKind::Struct)
    {
        trgtl = this->evalTargetVar(op->trgt);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
    }
    else
    {
        trgtl = Allocator::GlobalAllocator.allocateSafe(op->trgttype);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), trgtl);
    }

    for(size_t i = 0; i < op->updates.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, std::get<1>(op->updates[i]));
        std::get<2>(op->updates[i])->storeValue(dst, this->evalArgument(std::get<3>(op->updates[i])));
    }
}

void Evaluator::evalUpdateRecordOp(const UpdateRecordOp* op)
{
    Allocator::GlobalAllocator.ensureSpace(op->trgttype->allocinfo.heapsize);
    
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);
        
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeKind::Struct)
    {
        trgtl = this->evalTargetVar(op->trgt);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
    }
    else
    {
        trgtl = Allocator::GlobalAllocator.allocateSafe(op->trgttype);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), trgtl);
    }

    for(size_t i = 0; i < op->updates.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, std::get<1>(op->updates[i]));
        std::get<2>(op->updates[i])->storeValue(dst, this->evalArgument(std::get<3>(op->updates[i])));
    }
}

void Evaluator::evalUpdateEntityOp(const UpdateEntityOp* op)
{
    Allocator::GlobalAllocator.ensureSpace(op->trgttype->allocinfo.heapsize);
    
    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeKind::Struct)
    {
        sl = this->evalArgument(op->arg);
    }
    else if(op->layouttype->tkind == BSQTypeKind::UnionInline)
    {
        sl = SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->arg));
    }
    else
    {
        assert(op->layouttype->tkind == BSQTypeKind::Ref || op->layouttype->tkind == BSQTypeKind::UnionRef);
        
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalArgument(op->arg));
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeKind::Struct)
    {
        trgtl = this->evalTargetVar(op->trgt);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
    }
    else
    {
        trgtl = Allocator::GlobalAllocator.allocateSafe(op->trgttype);
        GC_MEM_COPY(trgtl, sl, op->trgttype->allocinfo.heapsize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), trgtl);
    }

    for(size_t i = 0; i < op->updates.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, std::get<1>(op->updates[i]));
        std::get<2>(op->updates[i])->storeValue(dst, this->evalArgument(std::get<3>(op->updates[i])));
    }
}

void Evaluator::evalLoadFromEpehmeralListOp(const LoadFromEpehmeralListOp* op)
{
    auto sl = this->evalArgument(op->arg);
    op->trgttype->storeValue(this->evalTargetVar(op->trgt), SLPTR_INDEX_DATAPTR(sl, op->slotoffset));
}

void Evaluator::evalMultiLoadFromEpehmeralListOp(const MultiLoadFromEpehmeralListOp* op)
{
    auto sl = this->evalArgument(op->arg);
    for(size_t i = 0; i < op->trgts.size(); ++i)
    {
        op->trgttypes[i]->storeValue(this->evalTargetVar(op->trgts[i]), SLPTR_INDEX_DATAPTR(sl, op->slotoffsets[i]));
    }
}

void Evaluator::evalSliceEphemeralListOp(const SliceEphemeralListOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto tl = this->evalTargetVar(op->trgt);

    BSQ_MEM_COPY(tl, sl, op->slotoffsetend);
}

template <>
void Evaluator::evalInvokeFixedFunctionOp<true>(const InvokeFixedFunctionOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->trgttype, op->sguard))
    {
        StorageLocationPtr resl = this->evalTargetVar(op->trgt);
        this->invoke(Environment::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
    }
}

template <>
void Evaluator::evalInvokeFixedFunctionOp<false>(const InvokeFixedFunctionOp* op)
{
    StorageLocationPtr resl = this->evalTargetVar(op->trgt);
    this->invoke(Environment::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
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

    auto tupinfo = dynamic_cast<const BSQTupleInfo*>(op->oftype);
    for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
    {
        BSQType::g_typetable[tupinfo->ttypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, tupinfo->idxoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorTupleFromEphemeralListOp(const ConstructorTupleFromEphemeralListOp* op)
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

    StorageLocationPtr tsrc = this->evalArgument(op->arg);
    BSQ_MEM_COPY(tcontents, tsrc, op->oftype->allocinfo.assigndatasize);
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

    auto recinfo = dynamic_cast<const BSQRecordInfo*>(op->oftype);
    for(size_t i = 0; i < recinfo->propertyoffsets.size(); ++i)
    {
        BSQType::g_typetable[recinfo->rtypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, recinfo->propertyoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorRecordFromEphemeralListOp(const ConstructorRecordFromEphemeralListOp* op)
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

    StorageLocationPtr tsrc = this->evalArgument(op->arg);
    if(op->proppositions.empty())
    {
        BSQ_MEM_COPY(tcontents, tsrc, op->oftype->allocinfo.assigndatasize);
    }
    else
    {
        auto recinfo = dynamic_cast<const BSQRecordInfo*>(op->oftype);
        for(size_t i = 0; i < op->proppositions.size(); ++i)
        {
            auto proppos = op->proppositions[i];
            BSQType::g_typetable[recinfo->rtypes[proppos]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, recinfo->propertyoffsets[proppos]), SLPTR_INDEX_DATAPTR(tsrc, op->argtype->idxoffsets[i]));
        }
    }
}

void Evaluator::evalEphemeralListExtendOp(const EphemeralListExtendOp* op)
{
    StorageLocationPtr tcontents = this->evalTargetVar(op->trgt);
    StorageLocationPtr acontents = this->evalArgument(op->arg);
    BSQ_MEM_COPY(tcontents, acontents, op->argtype->allocinfo.inlinedatasize);

    auto idxbase = op->argtype->idxoffsets.size();
    for(size_t i = 0; i < op->ext.size(); ++i)
    {
        BSQType::g_typetable[op->resultType->etypes[idxbase + i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, op->argtype->idxoffsets[idxbase + i]), this->evalArgument(op->ext[i]));
    }
}

void Evaluator::evalConstructorEphemeralListOp(const ConstructorEphemeralListOp* op)
{
    StorageLocationPtr tcontents = this->evalTargetVar(op->trgt);

    for(size_t i = 0; i < op->oftype->idxoffsets.size(); ++i)
    {
        BSQType::g_typetable[op->oftype->etypes[i]]->storeValue(op->oftype->indexStorageLocationOffset(tcontents, op->oftype->idxoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorPrimaryCollectionEmptyOp(const ConstructorPrimaryCollectionEmptyOp* op)
{
    ((BSQListType*)op->oftype)->storeValue(this->evalTargetVar(op->trgt), (StorageLocationPtr)&bsqemptylist);
}

void Evaluator::evalConstructorPrimaryCollectionSingletonsOp(const ConstructorPrimaryCollectionSingletonsOp* op)
{
    auto ltype = (BSQListType*)op->oftype;
    size_t ct = op->args.size();
    const ListTypeConstructorInfo& glistalloc = BSQListType::g_listTypeMap[ltype->tid];

    if(ct <= 40)
    {
        auto fltype = std::find_if(glistalloc.kcons, glistalloc.kcons + sizeof(glistalloc.kcons), [ct](const std::pair<size_t, BSQListFlatKTypeAbstract*>& pp) {
            return ct <= pp.first;
        });

        const BSQListFlatKTypeAbstract* klist = fltype->second;
        auto etype = BSQType::g_typetable[ltype->etype];
        void* res = Allocator::GlobalAllocator.allocateDynamic(klist);
        klist->initializeCountInfo(res, ct, ltype->esize);

        BSQList ll = {res, ct};
        ltype->storeValue(this->evalTargetVar(op->trgt), (StorageLocationPtr)&ll);

        uint8_t* iter = klist->initializeWriteIter(res);
        for(size_t i = 0; i < op->args.size(); ++i)
        {
            klist->storeDataToPostion(iter, etype, this->evalArgument(op->args[i]));
            klist->advanceWriteIter(&iter, etype);
        }
    }
    else
    {
        assert(false);
    }
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

void Evaluator::evalBinKeyEqFastOp(const BinKeyEqFastOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, this->evalArgument(op->argl), this->evalArgument(op->argr)) == 0);
}

void Evaluator::evalBinKeyEqStaticOp(const BinKeyEqStaticOp* op)
{
    auto lldata = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argl)) : this->evalArgument(op->argl); 
    auto rrdata = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argr)) : this->evalArgument(op->argr); 
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, lldata, rrdata) == 0);
}

void Evaluator::evalBinKeyEqVirtualOp(const BinKeyEqVirtualOp* op)
{
    auto lltype = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_TYPE(this->evalArgument(op->argl)) : SLPTR_LOAD_HEAP_TYPE_ANY(this->evalArgument(op->argl)); 
    auto rrtype = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_TYPE(this->evalArgument(op->argr)) : SLPTR_LOAD_HEAP_TYPE_ANY(this->evalArgument(op->argr));

    if(lltype->tid != rrtype->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), BSQFALSE);
    }
    else
    {
        auto lldata = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argl)) : this->evalArgument(op->argl); 
        auto rrdata = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argr)) : this->evalArgument(op->argr); 
    
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->fpkeycmp(lltype, lldata, rrdata) == 0);
    }
}

void Evaluator::evalBinKeyLessFastOp(const BinKeyLessFastOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, this->evalArgument(op->argl), this->evalArgument(op->argr)) < 0);
}

void Evaluator::evalBinKeyLessStaticOp(const BinKeyLessStaticOp* op)
{
    auto lldata = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argl)) : this->evalArgument(op->argl); 
    auto rrdata = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argr)) : this->evalArgument(op->argr); 
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, lldata, rrdata) < 0);
}

void Evaluator::evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op)
{
    auto lltype = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_TYPE(this->evalArgument(op->argl)) : SLPTR_LOAD_HEAP_TYPE_ANY(this->evalArgument(op->argl)); 
    auto rrtype = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_TYPE(this->evalArgument(op->argr)) : SLPTR_LOAD_HEAP_TYPE_ANY(this->evalArgument(op->argr));

    if(lltype->tid != rrtype->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->tid < rrtype->tid);
    }
    else
    {
        auto lldata = op->argllayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argl)) : this->evalArgument(op->argl); 
        auto rrdata = op->argrlayout->tkind == BSQTypeKind::UnionInline ? SLPTR_LOAD_UNION_INLINE_DATAPTR(this->evalArgument(op->argr)) : this->evalArgument(op->argr); 
    
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->fpkeycmp(lltype, lldata, rrdata) < 0);
    }
}

inline BSQBool isNoneTest(const BSQType* tt, StorageLocationPtr chkl)
{
    //otherwise this should be statically checkable
    assert(tt->tkind == BSQTypeKind::UnionInline || tt->tkind == BSQTypeKind::UnionRef);

    if(tt->tkind == BSQTypeKind::UnionRef) {
        return SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(chkl) == BSQNoneHeapValue;
    }
    else {
        return (SLPTR_LOAD_UNION_INLINE_TYPE(chkl)->tid == BSQ_TYPE_ID_NONE);
    }
}

inline BSQBool checkIsNone(const BSQType* tt, StorageLocationPtr chkl)
{
    //otherwise this should be statically checkable
    assert(tt->tkind == BSQTypeKind::UnionInline || tt->tkind == BSQTypeKind::UnionRef);

    if(tt->tkind == BSQTypeKind::UnionRef) {
        return SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(chkl) == BSQNoneHeapValue;
    }
    else {
        return (SLPTR_LOAD_UNION_INLINE_TYPE(chkl)->tid == BSQ_TYPE_ID_NONE);
    }
}

inline BSQTypeID getTypeIDForTypeOf(const BSQType* tt, StorageLocationPtr chkl)
{
    //otherwise this should be statically checkable
    assert(tt->tkind == BSQTypeKind::UnionInline || tt->tkind == BSQTypeKind::UnionRef);

    if(tt->tkind == BSQTypeKind::UnionRef) {
        return SLPTR_LOAD_HEAP_TYPE_ANY(chkl)->tid;
    }
    else {
        return SLPTR_LOAD_UNION_INLINE_TYPE(chkl)->tid;
    }
}

template <>
void Evaluator::evalIsNoneOp<true>(const TypeIsNoneOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQType::g_typeBool, op->sguard))
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), isNoneTest(op->arglayout, this->evalArgument(op->arg)));
    }
}

template <>
void Evaluator::evalIsNoneOp<false>(const TypeIsNoneOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), isNoneTest(op->arglayout, this->evalArgument(op->arg)));
}


template <>
void Evaluator::evalIsSomeOp<true>(const TypeIsSomeOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQType::g_typeBool, op->sguard))
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), !isNoneTest(op->arglayout, this->evalArgument(op->arg)));
    }
}

template <>
void Evaluator::evalIsSomeOp<false>(const TypeIsSomeOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), !isNoneTest(op->arglayout, this->evalArgument(op->arg)));
}

template <>
void Evaluator::evalTypeTagIsOp<true>(const TypeTagIsOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQType::g_typeBool, op->sguard))
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), getTypeIDForTypeOf(op->arglayout, this->evalArgument(op->arg)) == op->oftype->tid);
    }
}

template <>
void Evaluator::evalTypeTagIsOp<false>(const TypeTagIsOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), getTypeIDForTypeOf(op->arglayout, this->evalArgument(op->arg)) == op->oftype->tid);
}

template <>
void Evaluator::evalTypeTagSubtypeOfOp<true>(const TypeTagSubtypeOfOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQType::g_typeBool, op->sguard))
    {
        auto rtid = getTypeIDForTypeOf(op->arglayout, this->evalArgument(op->arg));
        auto subtype = std::find(op->oftype->subtypes.cbegin(), op->oftype->subtypes.cend(), rtid) != op->oftype->subtypes.cend();

        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), subtype);
    }
}

template <>
void Evaluator::evalTypeTagSubtypeOfOp<false>(const TypeTagSubtypeOfOp* op)
{
    auto rtid = getTypeIDForTypeOf(op->arglayout, this->evalArgument(op->arg));
    auto subtype = std::find(op->oftype->subtypes.cbegin(), op->oftype->subtypes.cend(), rtid) != op->oftype->subtypes.cend();

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), subtype);
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
    BSQBool isnone = isNoneTest(op->arglayout, this->evalArgument(op->arg));
    
    if(isnone)
    {
        return this->advanceCurrentOp(op->noffset);
    }
    else
    {
        return this->advanceCurrentOp(op->soffset);
    }
}

template <>
void Evaluator::evalRegisterAssignOp<true>(const RegisterAssignOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->oftype, op->sguard))
    {
        op->oftype->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalRegisterAssignOp<false>(const RegisterAssignOp* op)
{
    op->oftype->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

void Evaluator::evalReturnAssignOp(const ReturnAssignOp* op)
{
    op->oftype->storeValue(this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

void Evaluator::evalReturnAssignOfConsOp(const ReturnAssignOfConsOp* op)
{
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->tkind == BSQTypeKind::Struct)
    {
        tcontents = this->evalTargetVar(op->trgt);
    }
    else
    {
        tcontents = Allocator::GlobalAllocator.allocateDynamic(op->oftype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), tcontents);
    }

    const BSQEntityInfo* entityinfo = dynamic_cast<const BSQEntityInfo*>(op->oftype);
    for(size_t i = 0; i < entityinfo->fieldoffsets.size(); ++i)
    {
        BSQType::g_typetable[entityinfo->ftypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, entityinfo->fieldoffsets[i]), this->evalArgument(op->args[i]));
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
    case OpCodeTag::DebugOp:
    {
        this->evalDebugOp(static_cast<const DebugOp*>(op));
    }
    case OpCodeTag::LoadUnintVariableValueOp:
    {
        this->evalLoadUnintVariableValueOp(static_cast<const LoadUnintVariableValueOp*>(op));
    }
    case OpCodeTag::NoneInitUnionOp:
    {
        this->evalNoneInitUnionOp(static_cast<const NoneInitUnionOp*>(op));
    }
    case OpCodeTag::StoreConstantMaskValueOp:
    {
        this->evalStoreConstantMaskValueOp(static_cast<const StoreConstantMaskValueOp*>(op));
    }
    case OpCodeTag::DirectAssignOp:
    {
        auto daop = static_cast<const DirectAssignOp*>(op);
        if(daop->sguard.enabled)
        {
            this->evalDirectAssignOp<true>(daop);
        }
        else
        {
            this->evalDirectAssignOp<false>(daop);
        }
    }
    case OpCodeTag::BoxOp:
    {
        auto bop = static_cast<const BoxOp*>(op);
        if(bop->sguard.enabled)
        {
            this->evalBoxOp<true>(bop);
        }
        else
        {
            this->evalBoxOp<false>(bop);
        }
    }
    case OpCodeTag::ExtractOp:
    {
        auto exop = static_cast<const ExtractOp*>(op);
        if(exop->sguard.enabled)
        {
            this->evalExtractOp<true>(exop);
        }
        else
        {
            this->evalExtractOp<false>(exop);
        }
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
    case OpCodeTag::ProjectTupleOp:
    {
        this->evalProjectTupleOp(static_cast<const ProjectTupleOp*>(op));
    }
    case OpCodeTag::ProjectRecordOp:
    {
        this->evalProjectRecordOp(static_cast<const ProjectRecordOp*>(op));
    }
    case OpCodeTag::ProjectEntityOp:
    {
        this->evalProjectEntityOp(static_cast<const ProjectEntityOp*>(op));
    }
    case OpCodeTag::UpdateTupleOp:
    {
        this->evalUpdateTupleOp(static_cast<const UpdateTupleOp*>(op));
    }
    case OpCodeTag::UpdateRecordOp:
    {
        this->evalUpdateRecordOp(static_cast<const UpdateRecordOp*>(op));
    }
    case OpCodeTag::UpdateEntityOp:
    {
        this->evalUpdateEntityOp(static_cast<const UpdateEntityOp*>(op));
    }
    case OpCodeTag::LoadFromEpehmeralListOp:
    {
        this->evalLoadFromEpehmeralListOp(static_cast<const LoadFromEpehmeralListOp*>(op));
    }
    case OpCodeTag::MultiLoadFromEpehmeralListOp:
    {
        this->evalMultiLoadFromEpehmeralListOp(static_cast<const MultiLoadFromEpehmeralListOp*>(op));
    }
    case OpCodeTag::SliceEphemeralListOp:
    {
        this->evalSliceEphemeralListOp(static_cast<const SliceEphemeralListOp*>(op));
    }
    case OpCodeTag::InvokeFixedFunctionOp:
    {
        auto opc = static_cast<const InvokeFixedFunctionOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalInvokeFixedFunctionOp<true>(opc);
        }
        else
        {
            this->evalInvokeFixedFunctionOp<false>(opc);
        }
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
    case OpCodeTag::ConstructorTupleFromEphemeralListOp:
    {
        this->evalConstructorTupleFromEphemeralListOp(static_cast<const ConstructorTupleFromEphemeralListOp*>(op));
    }
    case OpCodeTag::ConstructorRecordOp:
    {
        this->evalConstructorRecordOp(static_cast<const ConstructorRecordOp*>(op));
    }
    case OpCodeTag::ConstructorRecordFromEphemeralListOp:
    {
        this->evalConstructorRecordFromEphemeralListOp(static_cast<const ConstructorRecordFromEphemeralListOp*>(op));
    }
    case OpCodeTag::EphemeralListExtendOp:
    {
        this->evalEphemeralListExtendOp(static_cast<const EphemeralListExtendOp*>(op));
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
    case OpCodeTag::BinKeyEqFastOp:
    {
        this->evalBinKeyEqFastOp(static_cast<const BinKeyEqFastOp*>(op));
    }
    case OpCodeTag::BinKeyEqStaticOp:
    {
        this->evalBinKeyEqStaticOp(static_cast<const BinKeyEqStaticOp*>(op));
    }
    case OpCodeTag::BinKeyEqVirtualOp:
    {
        this->evalBinKeyEqVirtualOp(static_cast<const BinKeyEqVirtualOp*>(op));
    }
    case OpCodeTag::BinKeyLessFastOp:
    {
        this->evalBinKeyLessFastOp(static_cast<const BinKeyLessFastOp*>(op));
    }
    case OpCodeTag::BinKeyLessStaticOp:
    {
        this->evalBinKeyLessStaticOp(static_cast<const BinKeyLessStaticOp*>(op));
    }
    case OpCodeTag::BinKeyLessVirtualOp:
    {
        this->evalBinKeyLessVirtualOp(static_cast<const BinKeyLessVirtualOp*>(op));
    }
    case OpCodeTag::TypeIsNoneOp:
    {
        auto opc = static_cast<const TypeIsNoneOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalIsNoneOp<true>(opc);
        }
        else
        {
            this->evalIsNoneOp<false>(opc);
        }
    }
    case OpCodeTag::TypeIsSomeOp:
    {
        auto opc = static_cast<const TypeIsSomeOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalIsSomeOp<true>(opc);
        }
        else
        {
            this->evalIsSomeOp<false>(opc);
        }
    }
    case OpCodeTag::TypeTagIsOp:
    {
        auto opc = static_cast<const TypeTagIsOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalTypeTagIsOp<true>(opc);
        }
        else
        {
            this->evalTypeTagIsOp<false>(opc);
        }
    }
    case OpCodeTag::TypeTagSubtypeOfOp:
    {
        auto opc = static_cast<const TypeTagSubtypeOfOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalTypeTagSubtypeOfOp<true>(opc);
        }
        else
        {
            this->evalTypeTagSubtypeOfOp<false>(opc);
        }
    }
    //
    // ---- jump operations are handled in the outer loop ----
    //
    case OpCodeTag::RegisterAssignOp:
    {
        auto opc = static_cast<const RegisterAssignOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalRegisterAssignOp<true>(opc);
        }
        else
        {
            this->evalRegisterAssignOp<false>(opc);
        }
    }
    case OpCodeTag::ReturnAssignOp:
    {
        this->evalReturnAssignOp(static_cast<const ReturnAssignOp*>(op));
    }
    case OpCodeTag::ReturnAssignOfConsOp:
    {
        this->evalReturnAssignOfConsOp(static_cast<const ReturnAssignOfConsOp*>(op));
    }
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
    case OpCodeTag::NegateIntOp:
    {
        PrimitiveNegateOperatorMacroChecked(this, op, OpCodeTag::NegateDecimalOp, BSQInt, boost::safe_numerics::checked::minus<BSQInt>, "Int negation overflow/underflow");
    }
    case OpCodeTag::NegateBigIntOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateBigIntOp, BSQBigInt);
    }
    case OpCodeTag::NegateRationalOp:
    {
        assert(false);
    }
    case OpCodeTag::NegateFloatOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateFloatOp, BSQFloat);
    }
    case OpCodeTag::NegateDecimalOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateDecimalOp, BSQDecimal);
    }
    case OpCodeTag::AddNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddNatOp, BSQNat, boost::safe_numerics::checked::add<BSQNat>, "Nat addition overflow")
    }
    case OpCodeTag::AddIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddIntOp, BSQInt, boost::safe_numerics::checked::add<BSQInt>, "Int addition overflow/underflow")
    }
    case OpCodeTag::AddBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddBigNatOp, BSQBigNat, +)
    }
    case OpCodeTag::AddBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddBigIntOp, BSQBigInt, +)
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
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubNatOp, BSQNat, boost::safe_numerics::checked::subtract<BSQNat>, "Nat subtraction overflow")
    }
    case OpCodeTag::SubIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubIntOp, BSQInt, boost::safe_numerics::checked::subtract<BSQInt>, "Int subtraction overflow/underflow")
    }
    case OpCodeTag::SubBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubBigNatOp, BSQBigNat, -)
    }
    case OpCodeTag::SubBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubBigIntOp, BSQBigInt, -)
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
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultNatOp, BSQNat, boost::safe_numerics::checked::multiply<BSQNat>, "Nat multiplication overflow")
    }
    case OpCodeTag::MultIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultIntOp, BSQInt, boost::safe_numerics::checked::multiply<BSQInt>, "Int multiplication underflow/overflow")
    }
    case OpCodeTag::MultBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultBigNatOp, BSQBigNat, *)
    }
    case OpCodeTag::MultBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultBigIntOp, BSQBigInt, *)
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
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivBigNatOp, BSQBigNat)
    }
    case OpCodeTag::DivBigIntOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivBigIntOp, BSQBigInt)
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
    case OpCodeTag::EqStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::EqStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::EqStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), iteratorEqual(&i1, &i2));
    }
    case OpCodeTag::NeqStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::NeqStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::NeqStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), !iteratorEqual(&i1, &i2));
    }
    case OpCodeTag::LtStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), iteratorLess(&i1, &i2));
    }
    case OpCodeTag::GtStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), iteratorLess(&i2, &i1));
    }
    case OpCodeTag::LeStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), !iteratorLess(&i2, &i1));
    }
    case OpCodeTag::GeStrPosOp:
    {
        const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>* bop = static_cast<const PrimitiveBinaryOperatorOp<OpCodeTag::LtStrPosOp>*>(op);
        auto i1 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->larg));
        auto i2 = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, this->evalArgument(bop->rarg));
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(bop->trgt), !iteratorLess(&i1, &i2));
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
    do
    {
        switch(op->tag)
        {
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
    } while (this->hasMoreOps());
}
    
void Evaluator::evaluateBody(StorageLocationPtr resultsl, const BSQType* restype, Argument resarg)
{
    this->evaluateOpCodeBlocks();
    restype->storeValue(resultsl, this->evalArgument(resarg));
}

void Evaluator::invoke(const BSQInvokeDecl* call, const std::vector<Argument>& args, StorageLocationPtr resultsl, BSQBool* optmask)
{
    if(call->isPrimitive())
    {
        this->invokePrimitivePrelude((const BSQInvokePrimitiveDecl*)call, args);
        this->evaluatePrimitiveBody((const BSQInvokePrimitiveDecl*)call, resultsl, call->resultType);
    }
    else
    {
        this->invokePrelude((const BSQInvokeBodyDecl*)call, args, optmask);
        this->evaluateBody(resultsl, call->resultType, static_cast<const BSQInvokeBodyDecl*>(call)->resultArg);
    }

    this->invokePostlude();
}

void Evaluator::invokePrelude(const BSQInvokeBodyDecl* invk, const std::vector<Argument>& args, BSQBool* optmask)
{
    void* argsbase = BSQ_STACK_SPACE_ALLOC(invk->params.size() * sizeof(void*));
    void** curr = (void**)argsbase;
    for(size_t i = 0; i < invk->params.size(); ++i)
    {
        *curr = this->evalArgument(args[i]);
        curr++;
    }

    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame(&invk->srcFile, &invk->name, (StorageLocationPtr*)argsbase, cstack, mixedslots, optmask, maskslots, &invk->body);
#else
    this->pushFrame((StorageLocationPtr*)argsbase, cstack, mixedslots, optmask, maskslots, &invk->body);
#endif
}
    
void Evaluator::invokePrimitivePrelude(const BSQInvokePrimitiveDecl* invk, const std::vector<Argument>& args)
{
    void* argsbase = BSQ_STACK_SPACE_ALLOC(invk->params.size() * sizeof(void*));
    void** curr = (void**)argsbase;
    for(size_t i = 0; i < invk->params.size(); ++i)
    {
        *curr = this->evalArgument(args[i]);
        curr++;
    }

    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;
    GC_MEM_ZERO(cstack, cssize);

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame(&invk->srcFile, &invk->name, (StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, nullptr, nullptr);
#else
    this->pushFrame((StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, nullptr, nullptr);
#endif
}
    
void Evaluator::invokePostlude()
{
    this->popFrame();
    GCStack::popFrame();
}

void Evaluator::evaluatePrimitiveBody(const BSQInvokePrimitiveDecl* invk, StorageLocationPtr resultsl, const BSQType* restype)
{
    assert(false);
    switch (invk->implkey)
    {
    case BSQPrimitiveImplTag::validator_accepts:
        assert(false);
        break;
    case BSQPrimitiveImplTag::string_empty:
        assert(false);
        break;
    case BSQPrimitiveImplTag::string_append:
        assert(false);
        break;
    default:
        assert(false);
        break;
    }
}

void Evaluator::invokeGlobalCons(const BSQInvokeBodyDecl* invk, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg)
{
    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame(&invk->srcFile, &invk->name, nullptr, cstack, mixedslots, nullptr, maskslots, &invk->body);
#else
    this->pushFrame(nullptr, cstack, mixedslots, nullptr, maskslots, &invk->body);
#endif

    this->evaluateBody(resultsl, restype, resarg);

    this->popFrame();
}

void Evaluator::invokeMain(const BSQInvokeBodyDecl* invk, const std::vector<void*>& argslocs, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg)
{
    void* argsbase = BSQ_STACK_SPACE_ALLOC(invk->params.size() * sizeof(void*));
    void** curr = (void**)argsbase;
    for(size_t i = 0; i < invk->params.size(); ++i)
    {
        *curr = argslocs[i];
        curr++;
    }

    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame(&invk->srcFile, &invk->name, (StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, maskslots, &invk->body);
#else
    this->pushFrame((StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, maskslots, &invk->body);
#endif

    this->evaluateBody(resultsl, restype, resarg);

    this->popFrame();
}