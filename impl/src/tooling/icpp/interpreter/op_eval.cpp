//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

//
//TODO: win32 add checked arith
//
//https://github.com/dcleblanc/SafeInt

#ifdef _WIN32
#define PrimitiveNegateOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, ERROR) const PrimitiveNegateOperatorOp<TAG>* bop = static_cast<const PrimitiveNegateOperatorOp<TAG>*>(op); \
REPRTYPE res = -(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->arg))); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);

//Big Macro for generating code for primitive checked binary operations
#define PrimitiveBinaryOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATORW, OPERATORP, ERROR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE res = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)) OPERATORW SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);
#else
///Big Macro for generating code for primitive checked negate operations
#define PrimitiveNegateOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, ERROR) const PrimitiveNegateOperatorOp<TAG>* bop = static_cast<const PrimitiveNegateOperatorOp<TAG>*>(op); \
REPRTYPE res; \
bool err = __builtin_mul_overflow(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->arg)), -1, &res); \
BSQ_LANGUAGE_ASSERT(!err, &(THIS->cframe->invoke->srcFile), THIS->cframe->dbg_currentline, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);

//Big Macro for generating code for primitive checked binary operations
#define PrimitiveBinaryOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATORW, OPERATORP, ERROR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE res; \
bool err = OPERATORP(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)), SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)), &res); \
BSQ_LANGUAGE_ASSERT(!err, &(THIS->cframe->invoke->srcFile), THIS->cframe->dbg_currentline, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);
#endif

//Big Macro for generating code for primitive un-checked negate operations
#define PrimitiveNegateOperatorMacroSafe(THIS, OP, TAG, REPRTYPE) const PrimitiveNegateOperatorOp<TAG>* bop = static_cast<const PrimitiveNegateOperatorOp<TAG>*>(op); \
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), -SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->arg)));

//Big Macro for generating code for primitive checked rhsarg is non-zero binary operations
#define PrimitiveBinaryOperatorMacroCheckedDiv(THIS, OP, TAG, REPRTYPE) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE larg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)); \
REPRTYPE rarg = SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)); \
\
BSQ_LANGUAGE_ASSERT(rarg != (REPRTYPE)0, &(THIS->cframe->invoke->srcFile), THIS->cframe->dbg_currentline, "Division by zero"); \
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
BSQ_LANGUAGE_ASSERT(!ISNAN(rarg) & !ISNAN(larg), &(THIS->cframe->invoke->srcFile), THIS->cframe->dbg_currentline, "NaN cannot be ordered"); \
BSQ_LANGUAGE_ASSERT((!ISINFINITE(rarg) | !ISINFINITE(larg)) || ((rarg <= 0) & (0 <= larg)) || ((larg <= 0) & (0 <= rarg)), &(THIS->cframe->invoke->srcFile), THIS->cframe->dbg_currentline, "Infinte values cannot be ordered"); \
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);

jmp_buf Evaluator::g_entrybuff;
EvaluatorFrame Evaluator::g_callstack[BSQ_MAX_STACK];
uint8_t* Evaluator::g_constantbuffer = nullptr;

std::map<BSQTypeID, const BSQRegex*> Evaluator::g_validators;
std::map<std::string, const BSQRegex*> Evaluator::g_regexs;

void Evaluator::evalDeadFlowOp()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void Evaluator::evalAbortOp(const AbortOp *op)
{
    if(this->debuggerattached)
    {
        throw DebuggerException::CreateErrorAbortRequest({this->cframe->invoke, this->cframe->dbg_currentline, this->call_count});
    }
    else
    {
        BSQ_LANGUAGE_ABORT(op->msg.c_str(), &this->cframe->invoke->srcFile, this->cframe->dbg_currentline);
    }
}

void Evaluator::evalAssertCheckOp(const AssertOp *op)
{
    if (!SLPTR_LOAD_CONTENTS_AS(BSQBool, this->evalArgument(op->arg)))
    {
        if(this->debuggerattached)
        {
            throw DebuggerException::CreateErrorAbortRequest({this->cframe->invoke, this->cframe->dbg_currentline, this->call_count});
        }
        else
        {
            BSQ_LANGUAGE_ABORT(op->msg.c_str(), &this->cframe->invoke->srcFile, this->cframe->dbg_currentline);
        }
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
        auto sl = this->evalArgument(op->arg);
        auto oftype = SLPTR_LOAD_UNION_INLINE_TYPE(sl);

        auto dval = oftype->fpDisplay(oftype, SLPTR_LOAD_UNION_INLINE_DATAPTR(sl), DisplayMode::Standard);

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
    SLPTR_STORE_UNION_INLINE_TYPE(BSQWellKnownType::g_typeNone, this->evalTargetVar(op->trgt));
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
        coerce(op->fromtype, op->intotype, this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalBoxOp<false>(const BoxOp* op)
{
    coerce(op->fromtype, op->intotype, this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
}

template <>
void Evaluator::evalExtractOp<true>(const ExtractOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, op->intotype, op->sguard))
    {
        coerce(op->fromtype, op->intotype, this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
    }
}

template <>
void Evaluator::evalExtractOp<false>(const ExtractOp* op)
{
    coerce(op->fromtype, op->intotype, this->evalTargetVar(op->trgt), this->evalArgument(op->arg));
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
    const BSQType* ttype = srctype->getVType(src);
    StorageLocationPtr pp = srctype->getVData_NoAlloc(src);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //
    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    auto voffset = tinfo->idxoffsets[idx];

    this->processTupleDirectLoadAndStore(pp, ttype, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->storeValue(this->evalTargetVar(dst), srctype->indexStorageLocationOffset(src, slotoffset));
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    const BSQType* rtype = srctype->getVType(src);
    StorageLocationPtr pp = srctype->getVData_NoAlloc(src);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //
    auto rinfo = dynamic_cast<const BSQRecordInfo*>(rtype);
    auto proppos = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), propId);
    assert(proppos != rinfo->properties.cend());

    auto propidx = (size_t)std::distance(rinfo->properties.cbegin(), proppos);
    auto voffset = rinfo->propertyoffsets[propidx];

    this->processRecordDirectLoadAndStore(pp, rtype, voffset, dst, dsttype);
}
    
void Evaluator::processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, size_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->storeValue(this->evalTargetVar(dst), srctype->indexStorageLocationOffset(src, slotoffset));
}

void Evaluator::processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQUnionType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype)
{
    const BSQType* etype = srctype->getVType(src);
    StorageLocationPtr pp = srctype->getVData_NoAlloc(src);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //
    auto einfo = dynamic_cast<const BSQEntityInfo*>(etype);
    auto fldpos = std::find(einfo->fields.cbegin(), einfo->fields.cend(), fldId);
    assert(fldpos != einfo->fields.cend());

    auto fldidx = (size_t)std::distance(einfo->fields.cbegin(), fldpos);
    auto voffset = einfo->fieldoffsets[fldidx];

    this->processEntityDirectLoadAndStore(pp, etype, voffset, dst, dsttype);
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

    const BSQType* ttype = op->layouttype->getVType(sl);
    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    BSQBool hasidx = op->idx < tinfo->maxIndex;

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), hasidx);
}

void Evaluator::evalRecordHasPropertyOp(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);

    const BSQType* rtype = op->layouttype->getVType(sl);
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
    auto sl = this->evalArgument(op->arg);

    const BSQType* ttype = op->layouttype->getVType(sl);
    StorageLocationPtr pp = op->layouttype->getVData_NoAlloc(sl);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

    auto tinfo = dynamic_cast<const BSQTupleInfo*>(ttype);
    BSQBool loadsafe = op->idx < tinfo->maxIndex;
    if(loadsafe)
    {
        this->processTupleVirtualLoadAndStore(pp, op->layouttype, op->idx, op->trgt, op->trgttype);

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
    
    const BSQType* rtype = op->layouttype->getVType(sl);
    StorageLocationPtr pp = op->layouttype->getVData_NoAlloc(sl);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

    auto rinfo = dynamic_cast<const BSQRecordInfo*>(rtype);
    BSQBool loadsafe = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), op->propId) != rinfo->properties.cend();
    if(loadsafe)
    {
        this->processRecordVirtualLoadAndStore(pp, op->layouttype, op->propId, op->trgt, op->trgttype);
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
    StorageLocationPtr src = this->evalArgument(op->arg);
    StorageLocationPtr trgtl = this->evalTargetVar(op->trgt);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
    }
    
    for(size_t i = 0; i < op->idxs.size(); ++i)
    {
        auto dst = SLPTR_INDEX_DATAPTR(trgtl, op->trgttype->idxoffsets[i]);
        auto src = SLPTR_INDEX_DATAPTR(sl, std::get<1>(op->idxs[i]));

        std::get<2>(op->idxs[i])->storeValue(dst, src);
    }
}

void Evaluator::evalProjectRecordOp(const ProjectRecordOp* op)
{
    StorageLocationPtr src = this->evalArgument(op->arg);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
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
    StorageLocationPtr src = this->evalArgument(op->arg);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
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
    
    StorageLocationPtr src = this->evalArgument(op->arg);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeLayoutKind::Struct)
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
    
    StorageLocationPtr src = this->evalArgument(op->arg);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeLayoutKind::Struct)
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
    
    StorageLocationPtr src = this->evalArgument(op->arg);

    void* sl = nullptr;
    if(op->layouttype->tkind == BSQTypeLayoutKind::Struct)
    {
        sl = src;
    }
    else if(op->layouttype->tkind == BSQTypeLayoutKind::Ref)
    {
        sl = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    }
    else
    {
        sl = dynamic_cast<const BSQUnionType*>(op->layouttype)->getVData_NoAlloc(src);
    }

    void* trgtl = nullptr;
    if(op->trgttype->tkind == BSQTypeLayoutKind::Struct)
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
        this->invoke(BSQInvokeDecl::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
    }
}

template <>
void Evaluator::evalInvokeFixedFunctionOp<false>(const InvokeFixedFunctionOp* op)
{
    StorageLocationPtr resl = this->evalTargetVar(op->trgt);
    this->invoke(BSQInvokeDecl::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
}

void Evaluator::evalInvokeVirtualFunctionOp(const InvokeVirtualFunctionOp* op)
{
    auto sl = this->evalArgument(op->args[0]);

    const BSQType* etype = op->rcvrlayouttype->getVType(sl);
    StorageLocationPtr rcvrloc = op->rcvrlayouttype->getVData_NoAlloc(sl);

    auto viter = etype->vtable.find(op->invokeId);
    BSQ_INTERNAL_ASSERT(viter != etype->vtable.cend());

    StorageLocationPtr resl = this->evalTargetVar(op->trgt);
    this->vinvoke(dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[viter->second]), rcvrloc, op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
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
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
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
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
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
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
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
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
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

void Evaluator::evalConstructorEntityDirectOp(const ConstructorEntityDirectOp* op)
{
    StorageLocationPtr sl = this->evalTargetVar(op->trgt);

    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
    {
        tcontents = sl;
    }
    else
    {
        tcontents = Allocator::GlobalAllocator.allocateDynamic(op->oftype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tcontents);
    }

    auto einfo = dynamic_cast<const BSQEntityInfo*>(op->oftype);
    for(size_t i = 0; i < einfo->fieldoffsets.size(); ++i)
    {
        BSQType::g_typetable[einfo->ftypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, einfo->fieldoffsets[i]), this->evalArgument(op->args[i]));
    }
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

template<>
void Evaluator::evalBinKeyEqFastOp<true>(const BinKeyEqFastOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, this->evalArgument(op->argl), this->evalArgument(op->argr)) == 0);
    }
}

template<>
void Evaluator::evalBinKeyEqFastOp<false>(const BinKeyEqFastOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, this->evalArgument(op->argl), this->evalArgument(op->argr)) == 0);
}

template<>
void Evaluator::evalBinKeyEqStaticOp<true>(const BinKeyEqStaticOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
    {
        auto lleval = this->evalArgument(op->argl);
        auto rreval = this->evalArgument(op->argr);

        auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
        auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval; 
    
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, lldata, rrdata) == 0);
    }
}

template<>
void Evaluator::evalBinKeyEqStaticOp<false>(const BinKeyEqStaticOp* op)
{
    auto lleval = this->evalArgument(op->argl);
    auto rreval = this->evalArgument(op->argr);

    auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
    auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval;
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, lldata, rrdata) == 0);
}

template<>
void Evaluator::evalBinKeyEqVirtualOp<true>(const BinKeyEqVirtualOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
    {
        auto lleval = this->evalArgument(op->argl);
        auto rreval = this->evalArgument(op->argr);

        auto lltype = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVType(lleval) : op->argllayout; 
        auto rrtype = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVType(rreval) : op->argrlayout;

        if(lltype->tid != rrtype->tid)
        {
            SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), BSQFALSE);
        }
        else
        {
            auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
            auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval;

            SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->fpkeycmp(lltype, lldata, rrdata) == 0);
        }
    }
}

template<>
void Evaluator::evalBinKeyEqVirtualOp<false>(const BinKeyEqVirtualOp* op)
{
    auto lleval = this->evalArgument(op->argl);
    auto rreval = this->evalArgument(op->argr);

    auto lltype = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVType(lleval) : op->argllayout; 
    auto rrtype = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVType(rreval) : op->argrlayout;

    if(lltype->tid != rrtype->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), BSQFALSE);
    }
    else
    {
        auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
        auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval;
    
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->fpkeycmp(lltype, lldata, rrdata) == 0);
    }
}

void Evaluator::evalBinKeyLessFastOp(const BinKeyLessFastOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, this->evalArgument(op->argl), this->evalArgument(op->argr)) < 0);
}

void Evaluator::evalBinKeyLessStaticOp(const BinKeyLessStaticOp* op)
{
    auto lleval = this->evalArgument(op->argl);
    auto rreval = this->evalArgument(op->argr);

    auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
    auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval; 
    
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), op->oftype->fpkeycmp(op->oftype, lldata, rrdata) < 0);
}

void Evaluator::evalBinKeyLessVirtualOp(const BinKeyLessVirtualOp* op)
{
    auto lleval = this->evalArgument(op->argl);
    auto rreval = this->evalArgument(op->argr);

    auto lltype = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVType(lleval) : op->argllayout; 
    auto rrtype = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVType(rreval) : op->argrlayout;

    if(lltype->tid != rrtype->tid)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->tid < rrtype->tid);
    }
    else
    {
        auto lldata = op->argllayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argllayout)->getVData_NoAlloc(lleval) : lleval; 
        auto rrdata = op->argrlayout->isUnion() ? dynamic_cast<const BSQUnionType*>(op->argrlayout)->getVData_NoAlloc(rreval) : rreval;
    
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), lltype->fpkeycmp(lltype, lldata, rrdata) < 0);
    }
}

inline BSQBool isNoneTest(const BSQUnionType* tt, StorageLocationPtr chkl)
{
    return (BSQBool)(tt->getVType(chkl)->tid == BSQ_TYPE_ID_NONE);
}

inline BSQBool isNothingTest(const BSQUnionType* tt, StorageLocationPtr chkl)
{
    return (BSQBool)(tt->getVType(chkl)->tid == BSQ_TYPE_ID_NOTHING);
}

inline BSQTypeID getTypeIDForTypeOf(const BSQUnionType* tt, StorageLocationPtr chkl)
{
    return tt->getVType(chkl)->tid;
}

template <>
void Evaluator::evalIsNoneOp<true>(const TypeIsNoneOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
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
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
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
void Evaluator::evalIsNothingOp<true>(const TypeIsNothingOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), isNothingTest(op->arglayout, this->evalArgument(op->arg)));
    }
}

template <>
void Evaluator::evalIsNothingOp<false>(const TypeIsNothingOp* op)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), isNothingTest(op->arglayout, this->evalArgument(op->arg)));
}

template <>
void Evaluator::evalTypeTagIsOp<true>(const TypeTagIsOp* op)
{
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
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
    if(this->tryProcessGuardStmt(op->trgt, BSQWellKnownType::g_typeBool, op->sguard))
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
    if(op->oftype->tkind == BSQTypeLayoutKind::Struct)
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
#ifdef BSQ_DEBUG_BUILD 
    //TODO: currently nop for variable lifetime intro 
#endif    
}

void Evaluator::evalVarLifetimeEndOp(const VarLifetimeEndOp* op)
{
#ifdef BSQ_DEBUG_BUILD 
    //TODO: currently nop for variable lifetime end 
#endif    
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
        break;
    }
    case OpCodeTag::AbortOp:
    {
        this->evalAbortOp(static_cast<const AbortOp*>(op));
        break;
    }
    case OpCodeTag::AssertOp:
    {
        this->evalAssertCheckOp(static_cast<const AssertOp*>(op));
        break;
    }
    case OpCodeTag::DebugOp:
    {
        this->evalDebugOp(static_cast<const DebugOp*>(op));
        break;
    }
    case OpCodeTag::LoadUnintVariableValueOp:
    {
        this->evalLoadUnintVariableValueOp(static_cast<const LoadUnintVariableValueOp*>(op));
        break;
    }
    case OpCodeTag::NoneInitUnionOp:
    {
        this->evalNoneInitUnionOp(static_cast<const NoneInitUnionOp*>(op));
        break;
    }
    case OpCodeTag::StoreConstantMaskValueOp:
    {
        this->evalStoreConstantMaskValueOp(static_cast<const StoreConstantMaskValueOp*>(op));
        break;
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
        break;
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
        break;
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
        break;
    }
    case OpCodeTag::LoadConstOp:
    {
        this->evalLoadConstOp(static_cast<const LoadConstOp*>(op));
        break;
    }
    case OpCodeTag::TupleHasIndexOp:
    {
        this->evalTupleHasIndexOp(static_cast<const TupleHasIndexOp*>(op));
        break;
    }
    case OpCodeTag::RecordHasPropertyOp:
    {
        this->evalRecordHasPropertyOp(static_cast<const RecordHasPropertyOp*>(op));
        break;
    }
    case OpCodeTag::LoadTupleIndexDirectOp:
    {
        this->evalLoadTupleIndexDirectOp(static_cast<const LoadTupleIndexDirectOp*>(op));
        break;
    }
    case OpCodeTag::LoadTupleIndexVirtualOp:
    {
        this->evalLoadTupleIndexVirtualOp(static_cast<const LoadTupleIndexVirtualOp*>(op));
        break;
    }
    case OpCodeTag::LoadTupleIndexSetGuardDirectOp:
    {
        this->evalLoadTupleIndexSetGuardDirectOp(static_cast<const LoadTupleIndexSetGuardDirectOp*>(op));
        break;
    }
    case OpCodeTag::LoadTupleIndexSetGuardVirtualOp:
    {
        this->evalLoadTupleIndexSetGuardVirtualOp(static_cast<const LoadTupleIndexSetGuardVirtualOp*>(op));
        break;
    }
    case OpCodeTag::LoadRecordPropertyDirectOp:
    {
        this->evalLoadRecordPropertyDirectOp(static_cast<const LoadRecordPropertyDirectOp*>(op));
        break;
    }
    case OpCodeTag::LoadRecordPropertyVirtualOp:
    {
        this->evalLoadRecordPropertyVirtualOp(static_cast<const LoadRecordPropertyVirtualOp*>(op));
        break;
    }
    case OpCodeTag::LoadRecordPropertySetGuardDirectOp:
    {
        this->evalLoadRecordPropertySetGuardDirectOp(static_cast<const LoadRecordPropertySetGuardDirectOp*>(op));
        break;
    }
    case OpCodeTag::LoadRecordPropertySetGuardVirtualOp:
    {
        this->evalLoadRecordPropertySetGuardVirtualOp(static_cast<const LoadRecordPropertySetGuardVirtualOp*>(op));
        break;
    }
    case OpCodeTag::LoadEntityFieldDirectOp:
    {
        this->evalLoadDirectFieldOp(static_cast<const LoadEntityFieldDirectOp*>(op));
        break;
    }
    case OpCodeTag::LoadEntityFieldVirtualOp:
    {
        this->evalLoadVirtualFieldOp(static_cast<const LoadEntityFieldVirtualOp*>(op));
        break;
    }
    case OpCodeTag::ProjectTupleOp:
    {
        this->evalProjectTupleOp(static_cast<const ProjectTupleOp*>(op));
        break;
    }
    case OpCodeTag::ProjectRecordOp:
    {
        this->evalProjectRecordOp(static_cast<const ProjectRecordOp*>(op));
        break;
    }
    case OpCodeTag::ProjectEntityOp:
    {
        this->evalProjectEntityOp(static_cast<const ProjectEntityOp*>(op));
        break;
    }
    case OpCodeTag::UpdateTupleOp:
    {
        this->evalUpdateTupleOp(static_cast<const UpdateTupleOp*>(op));
        break;
    }
    case OpCodeTag::UpdateRecordOp:
    {
        this->evalUpdateRecordOp(static_cast<const UpdateRecordOp*>(op));
        break;
    }
    case OpCodeTag::UpdateEntityOp:
    {
        this->evalUpdateEntityOp(static_cast<const UpdateEntityOp*>(op));
        break;
    }
    case OpCodeTag::LoadFromEpehmeralListOp:
    {
        this->evalLoadFromEpehmeralListOp(static_cast<const LoadFromEpehmeralListOp*>(op));
        break;
    }
    case OpCodeTag::MultiLoadFromEpehmeralListOp:
    {
        this->evalMultiLoadFromEpehmeralListOp(static_cast<const MultiLoadFromEpehmeralListOp*>(op));
        break;
    }
    case OpCodeTag::SliceEphemeralListOp:
    {
        this->evalSliceEphemeralListOp(static_cast<const SliceEphemeralListOp*>(op));
        break;
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
        break;
    }
    case OpCodeTag::InvokeVirtualFunctionOp:
    {
        this->evalInvokeVirtualFunctionOp(static_cast<const InvokeVirtualFunctionOp*>(op));
        break;
    }
    case OpCodeTag::InvokeVirtualOperatorOp:
    {
        this->evalInvokeVirtualOperatorOp(static_cast<const InvokeVirtualOperatorOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorTupleOp:
    {
        this->evalConstructorTupleOp(static_cast<const ConstructorTupleOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorTupleFromEphemeralListOp:
    {
        this->evalConstructorTupleFromEphemeralListOp(static_cast<const ConstructorTupleFromEphemeralListOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorRecordOp:
    {
        this->evalConstructorRecordOp(static_cast<const ConstructorRecordOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorRecordFromEphemeralListOp:
    {
        this->evalConstructorRecordFromEphemeralListOp(static_cast<const ConstructorRecordFromEphemeralListOp*>(op));
        break;
    }
    case OpCodeTag::EphemeralListExtendOp:
    {
        this->evalEphemeralListExtendOp(static_cast<const EphemeralListExtendOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorEphemeralListOp:
    {
        this->evalConstructorEphemeralListOp(static_cast<const ConstructorEphemeralListOp*>(op));
        break;
    }
    case OpCodeTag::ConstructorEntityDirectOp:
    {
        this->evalConstructorEntityDirectOp(static_cast<const ConstructorEntityDirectOp*>(op));
        break;
    }
    case OpCodeTag::PrefixNotOp:
    {
        this->evalPrefixNotOp(static_cast<const PrefixNotOp*>(op));
        break;
    }
    case OpCodeTag::AllTrueOp:
    {
        this->evalAllTrueOp(static_cast<const AllTrueOp*>(op));
        break;
    }
    case OpCodeTag::SomeTrueOp:
    {
        this->evalSomeTrueOp(static_cast<const SomeTrueOp*>(op));
        break;
    }
    case OpCodeTag::BinKeyEqFastOp:
    {
        auto ope = static_cast<const BinKeyEqFastOp*>(op);
        if(ope->sguard.enabled)
        {
            this->evalBinKeyEqFastOp<true>(ope);
        }
        else
        {
            this->evalBinKeyEqFastOp<false>(ope);
        }
        break;
    }
    case OpCodeTag::BinKeyEqStaticOp:
    {
        auto ope = static_cast<const BinKeyEqStaticOp*>(op);
        if(ope->sguard.enabled)
        {
            this->evalBinKeyEqStaticOp<true>(ope);
        }
        else
        {
            this->evalBinKeyEqStaticOp<false>(ope);
        }
        break;
    }
    case OpCodeTag::BinKeyEqVirtualOp:
    {
        auto ope = static_cast<const BinKeyEqVirtualOp*>(op);
        if(ope->sguard.enabled)
        {
            this->evalBinKeyEqVirtualOp<true>(ope);
        }
        else
        {
            this->evalBinKeyEqVirtualOp<false>(ope);
        }
        break;
    }
    case OpCodeTag::BinKeyLessFastOp:
    {
        this->evalBinKeyLessFastOp(static_cast<const BinKeyLessFastOp*>(op));
        break;
    }
    case OpCodeTag::BinKeyLessStaticOp:
    {
        this->evalBinKeyLessStaticOp(static_cast<const BinKeyLessStaticOp*>(op));
        break;
    }
    case OpCodeTag::BinKeyLessVirtualOp:
    {
        this->evalBinKeyLessVirtualOp(static_cast<const BinKeyLessVirtualOp*>(op));
        break;
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
        break;
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
        break;
    }
    case OpCodeTag::TypeIsNothingOp:
    {
        auto opc = static_cast<const TypeIsNothingOp*>(op);
        if(opc->sguard.enabled)
        {
            this->evalIsNothingOp<true>(opc);
        }
        else
        {
            this->evalIsNothingOp<false>(opc);
        }
        break;
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
        break;
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
        break;
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
        break;
    }
    case OpCodeTag::ReturnAssignOp:
    {
        this->evalReturnAssignOp(static_cast<const ReturnAssignOp*>(op));
        break;
    }
    case OpCodeTag::ReturnAssignOfConsOp:
    {
        this->evalReturnAssignOfConsOp(static_cast<const ReturnAssignOfConsOp*>(op));
        break;
    }
#ifdef BSQ_DEBUG_BUILD 
    case OpCodeTag::VarLifetimeStartOp:
    {
        this->evalVarLifetimeStartOp(static_cast<const VarLifetimeStartOp*>(op));
        break;
    }
    case OpCodeTag::VarLifetimeEndOp:
    {
        this->evalVarLifetimeEndOp(static_cast<const VarLifetimeEndOp*>(op));
        break;
    }
#endif
    case OpCodeTag::NegateIntOp:
    {
        PrimitiveNegateOperatorMacroChecked(this, op, OpCodeTag::NegateDecimalOp, BSQInt, "Int negation overflow/underflow");
        break;
    }
    case OpCodeTag::NegateBigIntOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateBigIntOp, BSQBigInt);
        break;
    }
    case OpCodeTag::NegateRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::NegateFloatOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateFloatOp, BSQFloat);
        break;
    }
    case OpCodeTag::NegateDecimalOp:
    {
        PrimitiveNegateOperatorMacroSafe(this, op, OpCodeTag::NegateDecimalOp, BSQDecimal);
        break;
    }
    case OpCodeTag::AddNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddNatOp, BSQNat, +, __builtin_add_overflow, "Nat addition overflow")
        break;
    }
    case OpCodeTag::AddIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::AddIntOp, BSQInt, +, __builtin_add_overflow, "Int addition overflow/underflow")
        break;
    }
    case OpCodeTag::AddBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddBigNatOp, BSQBigNat, +)
        break;
    }
    case OpCodeTag::AddBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddBigIntOp, BSQBigInt, +)
        break;
    }
    case OpCodeTag::AddRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::AddFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddFloatOp, BSQFloat, +)
        break;
    }
    case OpCodeTag::AddDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::AddDecimalOp, BSQDecimal, +)
        break;
    }
    case OpCodeTag::SubNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubNatOp, BSQNat, -, __builtin_sub_overflow, "Nat subtraction overflow")
        break;
    }
    case OpCodeTag::SubIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::SubIntOp, BSQInt, -, __builtin_sub_overflow, "Int subtraction overflow/underflow")
        break;
    }
    case OpCodeTag::SubBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubBigNatOp, BSQBigNat, -)
        break;
    }
    case OpCodeTag::SubBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubBigIntOp, BSQBigInt, -)
        break;
    }
    case OpCodeTag::SubRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::SubFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubFloatOp, BSQFloat, -)
        break;
    }
    case OpCodeTag::SubDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::SubDecimalOp, BSQDecimal, -)
        break;
    }
    case OpCodeTag::MultNatOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultNatOp, BSQNat, *, __builtin_mul_overflow, "Nat multiplication overflow")
        break;
    }
    case OpCodeTag::MultIntOp:
    {
        PrimitiveBinaryOperatorMacroChecked(this, op, OpCodeTag::MultIntOp, BSQInt, *, __builtin_mul_overflow, "Int multiplication underflow/overflow")
        break;
    }
    case OpCodeTag::MultBigNatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultBigNatOp, BSQBigNat, *)
        break;
    }
    case OpCodeTag::MultBigIntOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultBigIntOp, BSQBigInt, *)
        break;
    }
    case OpCodeTag::MultRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::MultFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultFloatOp, BSQFloat, *)
        break;
    }
    case OpCodeTag::MultDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::MultDecimalOp, BSQDecimal, *)
        break;
    }
    case OpCodeTag::DivNatOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivNatOp, BSQNat)
        break;
    }
    case OpCodeTag::DivIntOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivIntOp, BSQInt)
        break;
    }
    case OpCodeTag::DivBigNatOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivBigNatOp, BSQBigNat)
        break;
    }
    case OpCodeTag::DivBigIntOp:
    {
        PrimitiveBinaryOperatorMacroCheckedDiv(this, op, OpCodeTag::DivBigIntOp, BSQBigInt)
        break;
    }
    case OpCodeTag::DivRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::DivFloatOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::DivFloatOp, BSQFloat, /)
        break;
    }
    case OpCodeTag::DivDecimalOp:
    {
        PrimitiveBinaryOperatorMacroSafe(this, op, OpCodeTag::DivDecimalOp, BSQDecimal, /)
        break;
    }
    case OpCodeTag::EqNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqNatOp, BSQNat, ==)
        break;
    }
    case OpCodeTag::EqIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqIntOp, BSQInt, ==)
        break;
    }
    case OpCodeTag::EqBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqBigNatOp, BSQBigNat, ==)
        break;
    }
    case OpCodeTag::EqBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqBigIntOp, BSQBigInt, ==)
        break;
    }
    case OpCodeTag::EqRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::EqFloatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqFloatOp, BSQFloat, ==)
        break;
    }
    case OpCodeTag::EqDecimalOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::EqDecimalOp, BSQDecimal, ==)
        break;
    }
    case OpCodeTag::NeqNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqNatOp, BSQNat, !=)
        break;
    }
    case OpCodeTag::NeqIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqIntOp, BSQInt, !=)
        break;
    }
    case OpCodeTag::NeqBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqBigNatOp, BSQBigNat, !=)
        break;
    }
    case OpCodeTag::NeqBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqBigIntOp, BSQBigInt, !=)
        break;
    }
    case OpCodeTag::NeqRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::NeqFloatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqFloatOp, BSQFloat, !=)
        break;
    }
    case OpCodeTag::NeqDecimalOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::NeqDecimalOp, BSQDecimal, !=)
        break;
    }
    case OpCodeTag::LtNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtNatOp, BSQNat, <)
        break;
    }
    case OpCodeTag::LtIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtIntOp, BSQInt, <)
        break;
    }
    case OpCodeTag::LtBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtBigNatOp, BSQBigNat, <)
        break;
    }
    case OpCodeTag::LtBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LtBigIntOp, BSQBigInt, <)
        break;
    }
    case OpCodeTag::LtRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::LtFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LtFloatOp, BSQFloat, std::isnan, std::isinf, <)
        break;
    }
    case OpCodeTag::LtDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LtDecimalOp, BSQDecimal, std::isnan, std::isinf, <)
        break;
    }
    case OpCodeTag::LeNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeNatOp, BSQNat, <=)
        break;
    }
    case OpCodeTag::LeIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeIntOp, BSQInt, <=)
        break;
    }
    case OpCodeTag::LeBigNatOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeBigNatOp, BSQBigNat, <=)
        break;
    }
    case OpCodeTag::LeBigIntOp:
    {
        PrimitiveBinaryComparatorMacroSafe(this, op, OpCodeTag::LeBigIntOp, BSQBigInt, <=)
        break;
    }
    case OpCodeTag::LeRationalOp:
    {
        assert(false);
        break;
    }
    case OpCodeTag::LeFloatOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LeFloatOp, BSQFloat, std::isnan, std::isinf, <=)
        break;
    }
    case OpCodeTag::LeDecimalOp:
    {
        PrimitiveBinaryComparatorMacroFP(this, op, OpCodeTag::LeDecimalOp, BSQDecimal, std::isnan, std::isinf, <=)
        break;
    }
    default:
    {
        assert(false);
        break;
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
            break;
        }
        case OpCodeTag::JumpCondOp:
        {
            op = this->evalJumpCondOp(static_cast<const JumpCondOp*>(op));
            break;
        }
        case OpCodeTag::JumpNoneOp:
        {
            op = this->evalJumpNoneOp(static_cast<const JumpNoneOp*>(op));
            break;
        }
        default:
        {
            this->evaluateOpCode(op);
            op = this->advanceCurrentOp();
            break;
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
        std::vector<StorageLocationPtr> pv(args.size(), (StorageLocationPtr)nullptr);
        std::transform(args.cbegin(), args.cend(), pv.begin(), [this](const Argument& arg) {
            return this->evalArgument(arg);
        });

        this->evaluatePrimitiveBody((const BSQInvokePrimitiveDecl*)call, pv, resultsl, call->resultType);
    }
    else
    {
        const BSQInvokeBodyDecl* idecl = (const BSQInvokeBodyDecl*)call;

        size_t cssize = idecl->scalarstackBytes + idecl->mixedstackBytes;
        uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
        GC_MEM_ZERO(cstack, cssize);

        for(size_t i = 0; i < args.size(); ++i)
        {
            StorageLocationPtr argv = this->evalArgument(args[i]);
            StorageLocationPtr pv = Evaluator::evalParameterInfo(idecl->paraminfo[i], cstack, cstack + idecl->scalarstackBytes);
            
            idecl->params[i].ptype->storeValue(pv, argv);
        }

        size_t maskslotbytes = idecl->maskSlots * sizeof(BSQBool);
        BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
        GC_MEM_ZERO(maskslots, maskslotbytes);

        this->invokePrelude(idecl, cstack, maskslots, optmask);
        this->evaluateBody(resultsl, idecl->resultType, idecl->resultArg);
        this->invokePostlude();
    }
}

void Evaluator::vinvoke(const BSQInvokeBodyDecl* idecl, StorageLocationPtr rcvr, const std::vector<Argument>& args, StorageLocationPtr resultsl, BSQBool* optmask)
{
    size_t cssize = idecl->scalarstackBytes + idecl->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    GC_MEM_ZERO(cstack, cssize);

    StorageLocationPtr pv = Evaluator::evalParameterInfo(idecl->paraminfo[0], cstack, cstack + idecl->scalarstackBytes);
    idecl->params[0].ptype->storeValue(pv, rcvr);

    for(size_t i = 1; i < args.size(); ++i)
    {
        StorageLocationPtr argv = this->evalArgument(args[i]);
        StorageLocationPtr pv = Evaluator::evalParameterInfo(idecl->paraminfo[i], cstack, cstack + idecl->scalarstackBytes);
            
        idecl->params[i].ptype->storeValue(pv, argv);
    }

    size_t maskslotbytes = idecl->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    this->invokePrelude(idecl, cstack, maskslots, optmask);
    this->evaluateBody(resultsl, idecl->resultType, idecl->resultArg);
    this->invokePostlude();
}

void Evaluator::invokePrelude(const BSQInvokeBodyDecl* invk, uint8_t* cstack, uint8_t* maskslots, BSQBool* optmask)
{
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame(this->computeCallIntoStepMode(), this->computeCurrentBreakpoint(), invk, cstack, mixedslots, optmask, maskslots, &invk->body);
#else
    this->pushFrame(invk, cstack, mixedslots, optmask, maskslots, &invk->body);
#endif
}
    
void Evaluator::invokePostlude()
{
    this->popFrame();
    GCStack::popFrame();
}

void Evaluator::evaluatePrimitiveBody(const BSQInvokePrimitiveDecl* invk, const std::vector<StorageLocationPtr>& params, StorageLocationPtr resultsl, const BSQType* restype)
{
    LambdaEvalThunk eethunk(this);

    switch (invk->implkey)
    {
    case BSQPrimitiveImplTag::validator_accepts: {
        BSQString str = SLPTR_LOAD_CONTENTS_AS(BSQString, params[0]);
        BSQStringForwardIterator iter(&str, 0);

        const BSQRegex* re = Evaluator::g_validators.find(invk->enclosingtype->tid)->second;
        SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, re->nfare->test(iter));
        break;
    }
    case BSQPrimitiveImplTag::number_nattoint: {
        BSQNat nn = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[0]);
        BSQ_LANGUAGE_ASSERT(nn <= (BSQNat)std::numeric_limits<BSQInt>::max(), &invk->srcFile, 0, "Out-of-bounds Nat to Int");
        
        SLPTR_STORE_CONTENTS_AS(BSQInt, resultsl, (BSQInt)nn);
        break;
    }
    case BSQPrimitiveImplTag::number_inttonat: {
        BSQInt ii = SLPTR_LOAD_CONTENTS_AS(BSQInt, params[0]);
        BSQ_LANGUAGE_ASSERT(ii >= 0, &invk->srcFile, 0, "Out-of-bounds Int to Nat");
        
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, (BSQNat)ii);
        break;
    }
    case BSQPrimitiveImplTag::number_nattobignat: {
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, resultsl, (BSQBigNat)SLPTR_LOAD_CONTENTS_AS(BSQNat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_inttobigint: {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, resultsl, (BSQBigInt)SLPTR_LOAD_CONTENTS_AS(BSQInt, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_bignattonat: {
        BSQBigNat nn = SLPTR_LOAD_CONTENTS_AS(BSQBigNat, params[0]);
        BSQ_LANGUAGE_ASSERT(nn <= (BSQBigNat)std::numeric_limits<BSQNat>::max(), &invk->srcFile, 0, "Out-of-bounds BigNat to Nat");
        
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, (BSQNat)nn);
        break;
    }
    case BSQPrimitiveImplTag::number_biginttoint: {
        BSQBigInt ii = SLPTR_LOAD_CONTENTS_AS(BSQBigInt, params[0]);
        BSQ_LANGUAGE_ASSERT((BSQBigInt)std::numeric_limits<BSQInt>::lowest() <= ii && ii <= (BSQBigInt)std::numeric_limits<BSQInt>::max(), &invk->srcFile, 0, "Out-of-bounds BigInt to Int");
        
        SLPTR_STORE_CONTENTS_AS(BSQInt, resultsl, (BSQInt)ii);
        break;
    }
    case BSQPrimitiveImplTag::number_bignattobigint: {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, resultsl, (BSQBigInt)SLPTR_LOAD_CONTENTS_AS(BSQBigNat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_biginttobignat: {
        BSQBigInt ii = SLPTR_LOAD_CONTENTS_AS(BSQBigInt, params[0]);
        BSQ_LANGUAGE_ASSERT(ii >= 0, &invk->srcFile, 0, "Out-of-bounds Int to Nat");
        
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, resultsl, (BSQBigNat)ii);
        break;
    }
    case BSQPrimitiveImplTag::number_bignattofloat: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, (BSQFloat)SLPTR_LOAD_CONTENTS_AS(BSQBigNat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_bignattodecimal: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, (BSQDecimal)SLPTR_LOAD_CONTENTS_AS(BSQBigNat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_bignattorational: {
        BSQRational rr = {(BSQBigInt)SLPTR_LOAD_CONTENTS_AS(BSQBigNat, params[0]), 1};
        SLPTR_STORE_CONTENTS_AS(BSQRational, resultsl, rr);
        break;
    }
    case BSQPrimitiveImplTag::number_biginttofloat: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, (BSQFloat)SLPTR_LOAD_CONTENTS_AS(BSQBigInt, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_biginttodecimal: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, (BSQDecimal)SLPTR_LOAD_CONTENTS_AS(BSQBigInt, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_biginttorational: {
        BSQRational rr = {SLPTR_LOAD_CONTENTS_AS(BSQBigInt, params[0]), 1};
        SLPTR_STORE_CONTENTS_AS(BSQRational, resultsl, rr);
        break;
    }
    case BSQPrimitiveImplTag::number_floattobigint: {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, resultsl, (BSQBigInt)SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_decimaltobigint: {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, resultsl, (BSQBigInt)SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_rationaltobigint: {
        auto rr = SLPTR_LOAD_CONTENTS_AS(BSQRational, params[0]);
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, resultsl, ((BSQBigInt)rr.numerator) / ((BSQBigInt)rr.denominator));
        break;
    }
    case BSQPrimitiveImplTag::number_floattodecimal: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, (BSQDecimal)SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_floattorational: {
        BSQ_INTERNAL_ASSERT(false);
        break;
    }
    case BSQPrimitiveImplTag::number_decimaltofloat: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, (BSQFloat)SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0]));
        break;
    }
    case BSQPrimitiveImplTag::number_decimaltorational: {
        BSQ_INTERNAL_ASSERT(false);
        break;
    }
    case BSQPrimitiveImplTag::number_rationaltofloat: {
        auto rr = SLPTR_LOAD_CONTENTS_AS(BSQRational, params[0]);
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, ((BSQFloat)rr.numerator) / ((BSQFloat)rr.denominator));
        break;
    }
    case BSQPrimitiveImplTag::number_rationaltodecimal: {
        auto rr = SLPTR_LOAD_CONTENTS_AS(BSQRational, params[0]);
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, ((BSQDecimal)rr.numerator) / ((BSQDecimal)rr.denominator));
        break;
    }
    case BSQPrimitiveImplTag::float_floor: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, std::floor(SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::decimal_floor: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, std::floor(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::float_ceil: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, std::ceil(SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::decimal_ceil: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, std::ceil(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::float_truncate: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, std::trunc(SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::decimal_truncate: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, std::trunc(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0])));
        break;
    }
    case BSQPrimitiveImplTag::float_power: {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, resultsl, std::pow(SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[0]), SLPTR_LOAD_CONTENTS_AS(BSQFloat, params[1])));
        break;
    }
    case BSQPrimitiveImplTag::decimal_power: {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, resultsl, std::pow(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[0]), SLPTR_LOAD_CONTENTS_AS(BSQDecimal, params[1])));
        break;
    }
    case BSQPrimitiveImplTag::string_empty: {
        BSQString str = SLPTR_LOAD_CONTENTS_AS(BSQString, params[0]);

        SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, BSQStringImplType::empty(str));
        break;
    }
    case BSQPrimitiveImplTag::string_append: {
        BSQString res = BSQStringImplType::concat2(params[0], params[1]);

        SLPTR_STORE_CONTENTS_AS(BSQString, resultsl, res);
        break;
    }
    case BSQPrimitiveImplTag::s_strconcat_ne: {
        BSQString res = BSQListOps::s_strconcat_ne(LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]));

        SLPTR_STORE_CONTENTS_AS(BSQString, resultsl, res);
        break;
    }
    case BSQPrimitiveImplTag::s_strjoin_ne: {
        BSQString res = BSQListOps::s_strjoin_ne(LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), params[1]);

        SLPTR_STORE_CONTENTS_AS(BSQString, resultsl, res);
        break;
    }
    case BSQPrimitiveImplTag::bytebuffer_getformat: {
        BSQByteBuffer bb;
        BSQWellKnownType::g_typeByteBuffer->storeValue(&bb, params[0]);

        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, (BSQNat)bb.format);
        break;
    }
    case BSQPrimitiveImplTag::bytebuffer_getcompression: {
        BSQByteBuffer bb;
        BSQWellKnownType::g_typeByteBuffer->storeValue(&bb, params[0]);

        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, (BSQNat)bb.compression);
        break;
    }
     case BSQPrimitiveImplTag::s_list_build_k: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        auto rres = BSQListOps::list_cons(lflavor, params);
        
        LIST_STORE_RESULT_REPR(rres, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_size_ne: {
        auto count = LIST_LOAD_TYPE_INFO_REPR(params[0])->getCount(LIST_LOAD_DATA(params[0]));
        
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, count);
        break;
    }
    case BSQPrimitiveImplTag::s_list_reduce_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        BSQListOps::s_reduce_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("f")->second, params, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_reduce_idx_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        BSQListOps::s_reduce_idx_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("f")->second, params, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_transduce_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        const BSQListTypeFlavor& uflavor = BSQListOps::g_flavormap.find(invk->binds.find("U")->second->tid)->second;
        const BSQType* envtype = invk->binds.find("E")->second;

        BSQListOps::s_transduce_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), uflavor, envtype, invk->pcodes.find("op")->second, params, dynamic_cast<const BSQEphemeralListType*>(invk->resultType), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_transduce_idx_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        const BSQListTypeFlavor& uflavor = BSQListOps::g_flavormap.find(invk->binds.find("U")->second->tid)->second;
        const BSQType* envtype = invk->binds.find("E")->second;

        BSQListOps::s_transduce_idx_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), uflavor, envtype, invk->pcodes.find("op")->second, params, dynamic_cast<const BSQEphemeralListType*>(invk->resultType), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_range_ne: {
        BSQListOps::s_range_ne(invk->binds.find("T")->second, params[0], params[1], params[3], resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_fill_ne: {
        BSQListOps::s_fill_ne(invk->binds.find("T")->second, params[1], params[0], resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_reverse_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
        auto rnode = Allocator::GlobalAllocator.registerCollectionNode(LIST_LOAD_DATA(params[0]));

        auto rr = BSQListOps::s_reverse_ne(lflavor, rnode);
        LIST_STORE_RESULT_REPR(rr, resultsl);

        Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
        break;
    }
    case BSQPrimitiveImplTag::s_list_append_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
        auto rr = BSQListOps::list_append(lflavor, LIST_LOAD_DATA(params[0]), LIST_LOAD_DATA(params[1]));
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_slice_start: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        BSQListSpineIterator liter(LIST_LOAD_TYPE_INFO_REPR(params[0]), LIST_LOAD_DATA(params[0]));
        Allocator::GlobalAllocator.registerCollectionIterator(&liter);

        auto rr = BSQListOps::s_slice_start(lflavor, liter, LIST_LOAD_TYPE_INFO_REPR(params[0]), SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]), 0);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        
        Allocator::GlobalAllocator.releaseCollectionIterator(&liter);
        break;
    }
    case BSQPrimitiveImplTag::s_list_slice_end: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        BSQListSpineIterator liter(LIST_LOAD_TYPE_INFO_REPR(params[0]), LIST_LOAD_DATA(params[0]));
        Allocator::GlobalAllocator.registerCollectionIterator(&liter);

        auto rr = BSQListOps::s_slice_end(lflavor, liter, LIST_LOAD_TYPE_INFO_REPR(params[0]), SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]), 0);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        
        Allocator::GlobalAllocator.releaseCollectionIterator(&liter);
        break;
    }
    case BSQPrimitiveImplTag::s_list_safe_get: {
        BSQListOps::s_safe_get(LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]), invk->binds.find("T")->second, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_find_pred_ne: {
        auto pos = BSQListOps::s_find_pred_ne(eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
        break;
    }
    case BSQPrimitiveImplTag::s_list_find_pred_idx_ne: {
        auto pos = BSQListOps::s_find_pred_idx_ne(eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
        break;
    }
    case BSQPrimitiveImplTag::s_list_find_pred_last_ne: {
        auto pos = BSQListOps::s_find_pred_last_ne(eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
        break;
    }
    case BSQPrimitiveImplTag::s_list_find_pred_last_idx_ne: {
        auto pos = BSQListOps::s_find_pred_last_idx_ne(eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
        break;
    }
    case BSQPrimitiveImplTag::s_list_filter_pred_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        auto rr = BSQListOps::s_filter_pred_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_filter_pred_idx_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        auto rr = BSQListOps::s_filter_pred_idx_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_map_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        const BSQListTypeFlavor& rflavor = BSQListOps::g_flavormap.find(invk->binds.find("U")->second->tid)->second;

        auto rr = BSQListOps::s_map_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("f")->second, params, rflavor);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_map_idx_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        const BSQListTypeFlavor& rflavor = BSQListOps::g_flavormap.find(invk->binds.find("U")->second->tid)->second;

        auto rr = BSQListOps::s_map_idx_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("f")->second, params, rflavor);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_map_sync_ne: {
        const BSQListTypeFlavor& lflavor1 = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;
        const BSQListTypeFlavor& lflavor2 = BSQListOps::g_flavormap.find(invk->binds.find("U")->second->tid)->second;
        const BSQListTypeFlavor& rflavor = BSQListOps::g_flavormap.find(invk->binds.find("V")->second->tid)->second;

        auto rr = BSQListOps::s_map_sync_ne(lflavor1, lflavor2, eethunk, SLPTR_LOAD_CONTENTS_AS(BSQNat, params[3]), LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), LIST_LOAD_DATA(params[1]), LIST_LOAD_TYPE_INFO_REPR(params[1]), invk->pcodes.find("f")->second, params, rflavor);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_sort_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        auto rr = BSQListOps::s_sort_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("cmp")->second, params);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_list_unique_from_sorted_ne: {
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(invk->binds.find("T")->second->tid)->second;

        auto rr = BSQListOps::s_unique_from_sorted_ne(lflavor, eethunk, LIST_LOAD_DATA(params[0]), LIST_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("eq")->second, params);
        LIST_STORE_RESULT_REPR(rr, resultsl);
        break;
    }
     case BSQPrimitiveImplTag::s_map_build_k: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;
        
        auto rr = BSQMapOps::map_cons(mflavor, params);
        MAP_STORE_RESULT_REPR(rr, params.size(), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_size_ne: {
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, MAP_LOAD_COUNT(params[0]));
        break;
    }
    case BSQPrimitiveImplTag::s_map_has_ne: {
        auto rr = BSQMapOps::s_lookup_ne(MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), params[1], invk->binds.find("K")->second);
        SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, (BSQBool)(rr != nullptr));
        break;
    }
    case BSQPrimitiveImplTag::s_map_find_ne: {
        auto ttype = MAP_LOAD_TYPE_INFO_REPR(params[0]);
        auto rr = BSQMapOps::s_lookup_ne(MAP_LOAD_REPR(params[0]), ttype, params[1], invk->binds.find("K")->second);
        BSQ_INTERNAL_ASSERT(rr != nullptr);

        invk->binds.find("K")->second->storeValue(resultsl, ttype->getValueLocation(rr));
        break;
    }
    case BSQPrimitiveImplTag::s_map_union_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;

        uint64_t count = MAP_LOAD_COUNT(params[0]) + MAP_LOAD_COUNT(params[1]);
        auto rr = BSQMapOps::s_union_ne(mflavor, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), MAP_LOAD_REPR(params[1]), MAP_LOAD_TYPE_INFO_REPR(params[1]), count);
        MAP_STORE_RESULT_REPR(rr, count, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_submap_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;

        auto rr = BSQMapOps::s_submap_ne(mflavor, eethunk, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("p")->second, params);
        MAP_STORE_RESULT_REPR(rr.first, rr.second, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_remap_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;
        const BSQMapTypeFlavor& rflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("U")->second->tid))->second;

        auto rr = BSQMapOps::s_remap_ne(mflavor, eethunk, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), invk->pcodes.find("f")->second, params, rflavor);
        MAP_STORE_RESULT_REPR(rr, MAP_LOAD_COUNT(params[0]), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_add_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;

        auto rr = BSQMapOps::s_add_ne(mflavor, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), params[1], params[2]);
        MAP_STORE_RESULT_REPR(rr, MAP_LOAD_COUNT(params[0]) + 1, resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_set_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;

        auto rr = BSQMapOps::s_set_ne(mflavor, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), params[1], params[2]);
        MAP_STORE_RESULT_REPR(rr, MAP_LOAD_COUNT(params[0]), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::s_map_remove_ne: {
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(invk->binds.find("K")->second->tid, invk->binds.find("V")->second->tid))->second;

        auto rr = BSQMapOps::s_remove_ne(mflavor, MAP_LOAD_REPR(params[0]), MAP_LOAD_TYPE_INFO_REPR(params[0]), params[1]);
        MAP_STORE_RESULT_REPR(rr, MAP_LOAD_COUNT(params[0]) - 1, resultsl);
        break;
    }
    default: {
        assert(false);
        break;
    }
    }
}

void Evaluator::invokeGlobalCons(const BSQInvokeBodyDecl* invk, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg)
{
    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);


    this->invokePrelude(invk, cstack, maskslots, nullptr);
    this->evaluateBody(resultsl, restype, resarg);
    this->invokePostlude();
}

uint8_t* Evaluator::prepareMainStack(const BSQInvokeBodyDecl* invk)
{
    size_t cssize = invk->scalarstackBytes + invk->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)zxalloc(cssize);
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)zxalloc(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    this->invokePrelude(invk, cstack, maskslots, nullptr);

    return cstack;
}

void Evaluator::invokeMain(const BSQInvokeBodyDecl* invk, StorageLocationPtr resultsl, const BSQType* restype, Argument resarg)
{
    this->evaluateBody(resultsl, restype, resarg);
    this->invokePostlude();
}

void Evaluator::linvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, StorageLocationPtr resultsl)
{
    size_t cssize = call->scalarstackBytes + call->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    GC_MEM_ZERO(cstack, cssize);

    for(size_t i = 0; i < args.size(); ++i)
    {
        StorageLocationPtr pv = Evaluator::evalParameterInfo(call->paraminfo[i], cstack, cstack + call->scalarstackBytes);
        call->params[i].ptype->storeValue(pv, args[i]);
    }

    size_t maskslotbytes = call->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    this->invokePrelude(call, cstack, maskslots, nullptr);
    this->evaluateBody(resultsl, call->resultType, call->resultArg);
    this->invokePostlude();
}

bool Evaluator::iinvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, BSQBool* optmask)
{
    size_t cssize = call->scalarstackBytes + call->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    GC_MEM_ZERO(cstack, cssize);

    for(size_t i = 0; i < args.size(); ++i)
    {
        StorageLocationPtr pv = Evaluator::evalParameterInfo(call->paraminfo[i], cstack, cstack + call->scalarstackBytes);
        call->params[i].ptype->storeValue(pv, args[i]);
    }

    size_t maskslotbytes = call->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    BSQBool ok = BSQFALSE;
    this->invokePrelude(call, cstack, maskslots, optmask);
    this->evaluateBody(&ok, call->resultType, call->resultArg);
    this->invokePostlude();

    return (bool)ok;
}

void Evaluator::cinvoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, BSQBool* optmask, StorageLocationPtr resultsl)
{
    size_t cssize = call->scalarstackBytes + call->mixedstackBytes;
    uint8_t* cstack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(cssize);
    GC_MEM_ZERO(cstack, cssize);

    for(size_t i = 0; i < args.size(); ++i)
    {
        StorageLocationPtr pv = Evaluator::evalParameterInfo(call->paraminfo[i], cstack, cstack + call->scalarstackBytes);
        call->params[i].ptype->storeValue(pv, args[i]);
    }

    size_t maskslotbytes = call->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    this->invokePrelude(call, cstack, maskslots, optmask);
    this->evaluateBody(resultsl, call->resultType, call->resultArg);
    this->invokePostlude();
}

void LambdaEvalThunk::invoke(const BSQInvokeBodyDecl* call, const std::vector<StorageLocationPtr>& args, StorageLocationPtr resultsl)
{
    static_cast<Evaluator*>(this->ctx)->linvoke(call, args, resultsl);
}

bool ICPPParseJSON::checkInvokeOk(const std::string& checkinvoke, StorageLocationPtr value, Evaluator& ctx)
{
    auto invkid = MarshalEnvironment::g_invokeToIdMap.find(checkinvoke)->second;
    auto invk = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[invkid]);

    std::vector<StorageLocationPtr> args = {value};
    BSQBool bb = BSQFALSE;
    ctx.linvoke(invk, args, &bb);

    return bb;
}

bool ICPPParseJSON::parseNoneImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    //location is aleady zero initialized
    return true;
}

bool ICPPParseJSON::parseNothingImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    //location is aleady zero initialized
    return true;
}

bool ICPPParseJSON::parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, StorageLocationPtr value, Evaluator& ctx)
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, value, (BSQBool)(b ? BSQTRUE : BSQFALSE));
    return true;
}

bool ICPPParseJSON::parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, StorageLocationPtr value, Evaluator& ctx)
{
    SLPTR_STORE_CONTENTS_AS(BSQNat, value, (BSQNat)n);
    return true;
}

bool ICPPParseJSON::parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, StorageLocationPtr value, Evaluator& ctx)
{
    SLPTR_STORE_CONTENTS_AS(BSQInt, value, (BSQInt)i);
    return true;
}

bool ICPPParseJSON::parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, StorageLocationPtr value, Evaluator& ctx)
{
    try
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, value, (BSQBigNat)std::stoull(n));
        return true;
    }
    catch(...)
    {
        ;
    }

    return false;
}

bool ICPPParseJSON::parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, StorageLocationPtr value, Evaluator& ctx)
{
    try
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, value, (BSQBigInt)std::stoll(i));
        return true;
    }
    catch(...)
    {
        ;
    }

    return false;
}

bool ICPPParseJSON::parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, StorageLocationPtr value, Evaluator& ctx)
{
    try
    {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, value, (BSQFloat)std::stod(f));
        return true;
    }
    catch(...)
    {
        ;
    }

    return false;
}

bool ICPPParseJSON::parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, StorageLocationPtr value, Evaluator& ctx)
{
    try
    {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, value, (BSQDecimal)std::stod(d));
        return true;
    }
    catch(...)
    {
        ;
    }

    return false;
}

bool ICPPParseJSON::parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, StorageLocationPtr value, Evaluator& ctx)
{
    try
    {
        BSQRational rv = {(BSQBigInt) std::stoll(n), (BSQNat)d};
        SLPTR_STORE_CONTENTS_AS(BSQRational, value, rv);
        return true;
    }
    catch(...)
    {
        ;
    }

    return false;
}

bool ICPPParseJSON::parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, StorageLocationPtr value, Evaluator& ctx)
{
    BSQString rstr = g_emptyString;
    if(s.empty())
    {
        //already empty
    }
    else if(s.size() < 16) 
    {
        rstr.u_inlineString = BSQInlineString::create((const uint8_t*)s.c_str(), s.size());
    }
    else if(s.size() <= 128)
    {
        auto stp = BSQStringKReprTypeAbstract::selectKReprForSize(s.size());

        rstr.u_data = Allocator::GlobalAllocator.allocateDynamic(stp);
        BSQ_MEM_COPY(rstr.u_data, s.c_str(), s.size());
    }
    else
    {
        //
        //TODO: split the string into multiple parts
        //
         assert(false);
    }
    
    SLPTR_STORE_CONTENTS_AS(BSQString, value, rstr);
    return true;
}

bool ICPPParseJSON::parseByteBufferImpl(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, StorageLocationPtr value, Evaluator& ctx)
{
    Allocator::GlobalAllocator.ensureSpace(BSQWellKnownType::g_typeByteBufferLeaf->allocinfo.heapsize + BSQWellKnownType::g_typeByteBufferNode->allocinfo.heapsize + (2 * sizeof(GC_META_DATA_WORD)));
    BSQByteBufferNode* cnode = (BSQByteBufferNode*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeByteBufferNode);
    cnode->bytecount = std::min((uint64_t)data.size(), (uint64_t)256);
    cnode->bytes = (BSQByteBufferLeaf*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeByteBufferLeaf);
    cnode->next = nullptr;

    void* croot = cnode;
    GCStack::pushFrame(&croot, "2");

    size_t i = 0;
    while(i < data.size())
    {
        std::copy(data.cbegin() + i, data.cbegin() + i + cnode->bytecount, cnode->bytes->bytes);
        i += cnode->bytecount;

        if(i < data.size())
        {
            Allocator::GlobalAllocator.ensureSpace(BSQWellKnownType::g_typeByteBufferLeaf->allocinfo.heapsize + BSQWellKnownType::g_typeByteBufferNode->allocinfo.heapsize + (2 * sizeof(GC_META_DATA_WORD)));
            BSQByteBufferNode* cnode = (BSQByteBufferNode*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeByteBufferNode);
            cnode->bytecount = std::min((uint64_t)data.size(), (uint64_t)256);
            cnode->bytes = (BSQByteBufferLeaf*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeByteBufferLeaf);
            cnode->next = (BSQByteBufferNode*)croot;

            croot = cnode;
        }
    }

    BSQByteBufferNode* nnode = (BSQByteBufferNode*)croot;

    while(nnode->next != nullptr)
    {
        auto nn = nnode->next;
        nnode->next = nnode;
        nnode = nn;
    }

    Allocator::GlobalAllocator.ensureSpace(BSQWellKnownType::g_typeByteBuffer->allocinfo.heapsize + sizeof(GC_META_DATA_WORD));
    BSQByteBuffer* buff = (BSQByteBuffer*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeByteBufferNode);
    buff->bytecount = data.size();
    buff->bytes = nnode;
    buff->compression = (BufferCompression)compress;
    buff->format = (BufferFormat)format;

    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, buff);

    GCStack::popFrame();
    return true;
}

bool ICPPParseJSON::parseDateTimeImpl(const APIModule* apimodule, const IType* itype, DateTime t, StorageLocationPtr value, Evaluator& ctx)
{
    Allocator::GlobalAllocator.ensureSpace(BSQWellKnownType::g_typeDateTime);
    BSQDateTime* dt = (BSQDateTime*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeDateTime);
    dt->year = t.year;
    dt->month = t.month;
    dt->day = t.day;
    dt->hour = t.hour;
    dt->month = t.min;
    dt->tzoffset = t.tzoffset;

    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, dt);
    return true;
}

bool ICPPParseJSON::parseTickTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t t, StorageLocationPtr value, Evaluator& ctx)
{
    SLPTR_STORE_CONTENTS_AS(BSQTickTime, value, (BSQTickTime)t);
    return true;
}

bool ICPPParseJSON::parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, StorageLocationPtr value, Evaluator& ctx)
{
    SLPTR_STORE_CONTENTS_AS(BSQLogicalTime, value, (BSQLogicalTime)j);
    return true;
}

bool ICPPParseJSON::parseUUIDImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, StorageLocationPtr value, Evaluator& ctx)
{
    BSQUUID uuid;
    std::copy(v.cbegin(), v.cbegin() + 16, uuid.bytes);
    
    SLPTR_STORE_CONTENTS_AS(BSQUUID, value, uuid);
    return true;
}

bool ICPPParseJSON::parseContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, StorageLocationPtr value, Evaluator& ctx)
{
    Allocator::GlobalAllocator.ensureSpace(BSQWellKnownType::g_typeContentHash);
    BSQContentHash* hash = (BSQContentHash*)Allocator::GlobalAllocator.allocateSafe(BSQWellKnownType::g_typeContentHash);

    std::copy(v.cbegin(), v.cbegin() + 64, hash->bytes);
    
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, hash);
    return true;
}
    
void ICPPParseJSON::prepareParseTuple(const APIModule* apimodule, const IType* itype, Evaluator& ctx)
{
    BSQTypeID tupid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* tuptype = BSQType::g_typetable[tupid];

    void* tupmem = nullptr;
    RefMask tupmask = nullptr;
    if(tuptype->tkind == BSQTypeLayoutKind::Struct)
    {
        tupmem = zxalloc(tuptype->allocinfo.heapsize);
        tupmask = tuptype->allocinfo.heapmask;
    }
    else
    {
        tupmem = zxalloc(tuptype->allocinfo.inlinedatasize);
        tupmask = tuptype->allocinfo.inlinedmask;
    }
    
    GCStack::pushFrame((void**)tupmem, tupmask);
    this->tuplestack.push_back(std::make_pair(tupmem, tuptype));
}

StorageLocationPtr ICPPParseJSON::getValueForTupleIndex(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx)
{
    void* tupmem = this->tuplestack.back().first;
    const BSQType* tuptype = this->tuplestack.back().second;

    return SLPTR_INDEX_DATAPTR(tupmem, dynamic_cast<const BSQTupleInfo*>(tuptype)->idxoffsets[i]);
}

void ICPPParseJSON::completeParseTuple(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    void* tupmem = this->tuplestack.back().first;
    const BSQType* tuptype = this->tuplestack.back().second;

    void* trgt = nullptr;
    uint64_t bytes = 0;
    if(tuptype->tkind == BSQTypeLayoutKind::Struct)
    {
        trgt = (void*)value;
        bytes = tuptype->allocinfo.inlinedatasize;
    }
    else
    {
        trgt = Allocator::GlobalAllocator.allocateDynamic(tuptype);
        bytes = tuptype->allocinfo.heapsize;

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, trgt);
    }

    GC_MEM_COPY(trgt, tupmem, bytes);
    xfree(tupmem);

    GCStack::popFrame();
    this->tuplestack.pop_back();
}

void ICPPParseJSON::prepareParseRecord(const APIModule* apimodule, const IType* itype, Evaluator& ctx)
{
    BSQTypeID recid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* rectype = BSQType::g_typetable[recid];

    void* recmem = nullptr;
    RefMask recmask = nullptr;
    if(rectype->tkind == BSQTypeLayoutKind::Struct)
    {
        recmem = zxalloc(rectype->allocinfo.heapsize);
        recmask = rectype->allocinfo.heapmask;
    }
    else
    {
        recmem = zxalloc(rectype->allocinfo.inlinedatasize);
        recmask = rectype->allocinfo.inlinedmask;
    }
    
    GCStack::pushFrame((void**)recmem, recmask);
    this->recordstack.push_back(std::make_pair(recmem, rectype));
}

StorageLocationPtr ICPPParseJSON::getValueForRecordProperty(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::string pname, Evaluator& ctx)
{
    void* recmem = this->recordstack.back().first;
    const BSQType* rectype = this->recordstack.back().second;

    BSQRecordPropertyID pid = MarshalEnvironment::g_propertyToIdMap.find(pname)->second;
    return SLPTR_INDEX_DATAPTR(recmem, dynamic_cast<const BSQRecordInfo*>(rectype)->propertyoffsets[pid]);
}

void ICPPParseJSON::completeParseRecord(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    void* recmem = this->recordstack.back().first;
    const BSQType* rectype = this->recordstack.back().second;

    void* trgt = nullptr;
    uint64_t bytes = 0;
    if(rectype->tkind == BSQTypeLayoutKind::Struct)
    {
        trgt = (void*)value;
        bytes = rectype->allocinfo.inlinedatasize;
    }
    else
    {
        trgt = Allocator::GlobalAllocator.allocateDynamic(rectype);
        bytes = rectype->allocinfo.heapsize;

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, trgt);
    }

    GC_MEM_COPY(trgt, recmem, bytes);
    xfree(recmem);

    GCStack::popFrame();
    this->tuplestack.pop_back();
}

void ICPPParseJSON::prepareParseContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t count, Evaluator& ctx)
{
    auto ctype = dynamic_cast<const ContainerType*>(itype);
    BSQTypeID containertypeid = MarshalEnvironment::g_typenameToIdMap.find(ctype->name)->second;
    const BSQType* collectiontype = BSQType::g_typetable[containertypeid];

    this->containerstack.push_back(std::make_pair(collectiontype, (uint64_t)count));
    Allocator::GlobalAllocator.pushTempRootScope();
}

StorageLocationPtr ICPPParseJSON::getValueForContainerElementParse(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx)
{
    const ContainerType* ctype = dynamic_cast<const ContainerType*>(itype);
    
    if(ctype->category == ContainerCategory::List)
    {
        const BSQListType* listtype = dynamic_cast<const BSQListType*>(this->containerstack.back().first);
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(listtype->etype)->second;

        auto rr = Allocator::GlobalAllocator.registerTempRoot(lflavor.entrytype);
        return rr->root;
    }
    else if(ctype->category == ContainerCategory::Stack)
    {
        BSQ_INTERNAL_ASSERT(false);
        return nullptr;
    }
    else if(ctype->category == ContainerCategory::Queue)
    {
        BSQ_INTERNAL_ASSERT(false);
        return nullptr;
    }
    else if(ctype->category == ContainerCategory::Set)
    {
        BSQ_INTERNAL_ASSERT(false);
        return nullptr;
    }
    else
    {
        const BSQMapType* maptype = dynamic_cast<const BSQMapType*>(this->containerstack.back().first);
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(maptype->ktype, maptype->vtype))->second;

        //We are very creative here and use the fact that the kv layout in the tree is identical to the kv layout in the tuple!
        auto rr = Allocator::GlobalAllocator.registerTempRoot(mflavor.treetype);
        return (void*)((uint8_t*)rr->root + mflavor.treetype->keyoffset);
    }
}

void ICPPParseJSON::completeParseContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    const ContainerType* ctype = dynamic_cast<const ContainerType*>(itype);

    if(ctype->category == ContainerCategory::List)
    {
        const BSQListType* listtype = dynamic_cast<const BSQListType*>(this->containerstack.back().first);
        const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(listtype->etype)->second;

        if(this->containerstack.back().second == 0)
        {
            LIST_STORE_RESULT_EMPTY(value);
        }
        else
        {
            auto lstart = Allocator::GlobalAllocator.getTempRootCurrScope().begin();
            void* rres = BSQListOps::s_temp_root_to_list_rec(lflavor, lstart, this->containerstack.back().second);

            LIST_STORE_RESULT_REPR(rres, value);
        }
    }
    else if(ctype->category == ContainerCategory::Stack)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else if(ctype->category == ContainerCategory::Queue)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else if(ctype->category == ContainerCategory::Set)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else
    {
        const BSQMapType* maptype = dynamic_cast<const BSQMapType*>(this->containerstack.back().first);
        const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(maptype->ktype, maptype->vtype))->second;

        if(this->containerstack.back().second == 0)
        {
            MAP_STORE_RESULT_EMPTY(value);
        }
        else
        {
            std::list<BSQTempRootNode>& roots = Allocator::GlobalAllocator.getTempRootCurrScope();
            std::vector<BSQTempRootNode> opv(roots.cbegin(), roots.cend());

            std::stable_sort(opv.begin(), opv.end(), [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
                return mflavor.keytype->fpkeycmp(mflavor.keytype, mflavor.treetype->getKeyLocation(ln.root), mflavor.treetype->getKeyLocation(rn.root)) < 0;
            });

            //check for dups in the input
            auto fl = std::adjacent_find(opv.begin(), opv.end(), [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
                return mflavor.keytype->fpkeycmp(mflavor.keytype, mflavor.treetype->getKeyLocation(ln.root), mflavor.treetype->getKeyLocation(rn.root)) == 0;
            });

            std::string fname("[JSON_PARSE]");
            BSQ_LANGUAGE_ASSERT(fl != opv.end(), (&fname), -1, "Duplicate keys in map");

            std::list<BSQTempRootNode> ltomap(opv.begin(), opv.end());
            auto lstart = ltomap.begin();
            void* rres = BSQMapOps::s_temp_root_to_map_rec(mflavor, lstart, this->containerstack.back().second);

            MAP_STORE_RESULT_REPR(rres, this->containerstack.back().second, value);
        }
    }
    
    this->containerstack.pop_back();
    Allocator::GlobalAllocator.popTempRootScope();
}

void ICPPParseJSON::prepareParseEntity(const APIModule* apimodule, const IType* itype, Evaluator& ctx)
{
    BSQTypeID ooid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* ootype = BSQType::g_typetable[ooid];

    void* oomem = nullptr;
    RefMask oomask = nullptr;
    if(ootype->tkind == BSQTypeLayoutKind::Struct)
    {
        oomem = zxalloc(ootype->allocinfo.heapsize);
        oomask = ootype->allocinfo.heapmask;
    }
    else
    {
        oomem = zxalloc(ootype->allocinfo.inlinedatasize);
        oomask = ootype->allocinfo.inlinedmask;
    }
    
    GCStack::pushFrame((void**)oomem, oomask);
    this->entitystack.push_back(std::make_pair(oomem, ootype));
}

void ICPPParseJSON::prepareParseEntityMask(const APIModule* apimodule, const IType* itype, Evaluator& ctx)
{
    BSQTypeID ooid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQEntityInfo* ootype = dynamic_cast<const BSQEntityInfo*>(BSQType::g_typetable[ooid]);

    auto mcount = std::count_if(ootype->fields.cbegin(), ootype->fields.cend(), [](BSQFieldID fid) {
        auto fdecl = BSQField::g_fieldtable[fid];
        return fdecl->isOptional;
    });

    BSQBool* mask = (BSQBool*)zxalloc(mcount * sizeof(BSQBool));
    this->entitymaskstack.push_back(mask);
}

StorageLocationPtr ICPPParseJSON::getValueForEntityField(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::pair<std::string, std::string> fnamefkey, Evaluator& ctx)
{
    void* oomem = this->entitystack.back().first;
    const BSQType* ootype = this->entitystack.back().second;

    BSQFieldID fid = MarshalEnvironment::g_fieldToIdMap.find(fnamefkey.second)->second;
    return SLPTR_INDEX_DATAPTR(oomem, dynamic_cast<const BSQEntityInfo*>(ootype)->fieldoffsets[fid]);
}

void ICPPParseJSON::completeParseEntity(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    const EntityType* etype = dynamic_cast<const EntityType*>(itype);

    void* oomem = this->entitystack.back().first;
    const BSQType* ootype = this->entitystack.back().second;

    std::vector<StorageLocationPtr> cargs;
    std::transform(etype->consfields.cbegin(), etype->consfields.cend(), std::back_inserter(cargs), [&](const std::pair<std::string, std::string>& fnamefkey) {
        BSQFieldID fid = MarshalEnvironment::g_fieldToIdMap.find(fnamefkey.second)->second;
        return SLPTR_INDEX_DATAPTR(oomem, dynamic_cast<const BSQEntityInfo*>(ootype)->fieldoffsets[fid]);
    });

    BSQBool* mask = this->entitymaskstack.back();

    if(etype->validatefunc.has_value())
    {
        auto chkid = MarshalEnvironment::g_invokeToIdMap.find(etype->validatefunc.value())->second;
        auto chkcall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[chkid]);

        std::string pfile = "[INPUT PARSE]";
        bool checkok = ctx.iinvoke(chkcall, cargs, mask);
        BSQ_LANGUAGE_ASSERT(checkok, (&pfile), -1, "Input Data Validation Failed");
    }

    if(etype->consfunc.has_value())
    {
        auto consid = MarshalEnvironment::g_invokeToIdMap.find(etype->consfunc.value())->second;
        auto conscall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[consid]);

        std::string pfile = "[INPUT PARSE]";
        ctx.cinvoke(conscall, cargs, mask, value);
    }
    else
    {
        void* trgt = nullptr;
        uint64_t bytes = 0;
        if(ootype->tkind == BSQTypeLayoutKind::Struct)
        {
            trgt = (void*)value;
            bytes = ootype->allocinfo.inlinedatasize;
        }
        else
        {
            trgt = Allocator::GlobalAllocator.allocateDynamic(ootype);
            bytes = ootype->allocinfo.heapsize;

            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(value, trgt);
        }

        GC_MEM_COPY(trgt, oomem, bytes);
    }

    xfree(oomem);
    xfree(mask);

    GCStack::popFrame();
    this->tuplestack.pop_back();
}

void ICPPParseJSON::setMaskFlag(const APIModule* apimodule, StorageLocationPtr flagloc, size_t i, bool flag, Evaluator& ctx)
{
    *(((BSQBool*)flagloc) + i) = (BSQBool)flag;
}

StorageLocationPtr ICPPParseJSON::parseUnionChoice(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t pick, Evaluator& ctx)
{
    auto utype = dynamic_cast<const UnionType*>(itype);
    auto oftype = utype->opts[pick];

    auto bsqutypeid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    auto bsqutype = dynamic_cast<const BSQUnionType*>(BSQType::g_typetable[bsqutypeid]);
    if(bsqutype->tkind == BSQTypeLayoutKind::UnionRef)
    {
        return value;
    }
    else
    {
        auto ttypeid = MarshalEnvironment::g_typenameToIdMap.find(oftype)->second;
        auto ttype = BSQType::g_typetable[ttypeid];

        SLPTR_STORE_UNION_INLINE_TYPE(ttype, value);
        return SLPTR_LOAD_UNION_INLINE_DATAPTR(value);
    }
}

std::optional<bool> ICPPParseJSON::extractBoolImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    return std::make_optional((bool)SLPTR_LOAD_CONTENTS_AS(BSQBool, value));
}

std::optional<uint64_t> ICPPParseJSON::extractNatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    return std::make_optional((uint64_t)SLPTR_LOAD_CONTENTS_AS(BSQNat, value));
}

std::optional<int64_t> ICPPParseJSON::extractIntImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    return std::make_optional((int64_t)SLPTR_LOAD_CONTENTS_AS(BSQInt, value));
}

std::optional<std::string> ICPPParseJSON::extractBigNatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = (uint64_t)SLPTR_LOAD_CONTENTS_AS(BSQBigNat, value);
    return std::make_optional(std::to_string(val));
}

std::optional<std::string> ICPPParseJSON::extractBigIntImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = (int64_t)SLPTR_LOAD_CONTENTS_AS(BSQBigInt, value);
    return std::make_optional(std::to_string(val));
}

std::optional<std::string> ICPPParseJSON::extractFloatImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = (double)SLPTR_LOAD_CONTENTS_AS(BSQFloat, value);
    return std::make_optional(std::to_string(val));
}

std::optional<std::string> ICPPParseJSON::extractDecimalImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = (double)SLPTR_LOAD_CONTENTS_AS(BSQDecimal, value);
    return std::make_optional(std::to_string(val));
}

std::optional<std::pair<std::string, uint64_t>> ICPPParseJSON::extractRationalImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = SLPTR_LOAD_CONTENTS_AS(BSQRational, value);
    return std::make_optional(std::make_pair(std::to_string(val.numerator), val.denominator));
}

std::optional<std::string> ICPPParseJSON::extractStringImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto val = SLPTR_LOAD_CONTENTS_AS(BSQString, value);

    std::string rstr;
    BSQStringForwardIterator iter(&val, 0);

    rstr.reserve(BSQStringImplType::utf8ByteCount(val));
    while(iter.valid())
    {
        rstr.push_back((char)iter.get_byte());
        iter.advance_byte();
    }

    return rstr;
}

std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> ICPPParseJSON::extractByteBufferImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    BSQByteBuffer* bb = (BSQByteBuffer*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(value);
    auto pprops = std::make_pair((uint8_t)bb->compression, (uint8_t)bb->format);

    std::vector<uint8_t> bytes;
    bytes.reserve(bb->bytecount);

    BSQByteBufferNode* bbn = bb->bytes;
    while(bbn != nullptr)
    {
        std::copy(bbn->bytes->bytes, bbn->bytes->bytes + bbn->bytecount, std::back_inserter(bytes));
        bbn = bbn->next;
    }

    return std::make_optional(std::make_pair(bytes, pprops));
}

std::optional<DateTime> ICPPParseJSON::extractDateTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    BSQDateTime* t = (BSQDateTime*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(value);

    DateTime dt;
    dt.year = t->year;
    dt.month = t->month;
    dt.day = t->day;
    dt.hour = t->hour;
    dt.min = t->min;
    dt.tzoffset = t->tzoffset;

    return std::make_optional(dt);
}

std::optional<uint64_t> ICPPParseJSON::extractTickTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    return std::make_optional((uint64_t)SLPTR_LOAD_CONTENTS_AS(BSQTickTime, value));
}

std::optional<uint64_t> ICPPParseJSON::extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    return std::make_optional((uint64_t)SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, value));
}

std::optional<std::vector<uint8_t>> ICPPParseJSON::extractUUIDImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto uuid = SLPTR_LOAD_CONTENTS_AS(BSQUUID, value);

    std::vector<uint8_t> vv;
    std::copy(uuid.bytes, uuid.bytes + 16, std::back_inserter(vv));

    return std::make_optional(vv);
}

std::optional<std::vector<uint8_t>> ICPPParseJSON::extractContentHashImpl(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto hash = (BSQContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(value);

    std::vector<uint8_t> vv;
    std::copy(hash->bytes, hash->bytes + 64, std::back_inserter(vv));

    return std::make_optional(vv);
}

StorageLocationPtr ICPPParseJSON::extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx)
{
    BSQTypeID tupid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* tuptype = BSQType::g_typetable[tupid];

    return tuptype->indexStorageLocationOffset(value, dynamic_cast<const BSQTupleInfo*>(tuptype)->idxoffsets[i]);
}

StorageLocationPtr ICPPParseJSON::extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::string pname, Evaluator& ctx)
{
    BSQTypeID recid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* rectype = BSQType::g_typetable[recid];

    BSQRecordPropertyID pid = MarshalEnvironment::g_propertyToIdMap.find(itype->name)->second;
    return rectype->indexStorageLocationOffset(value, dynamic_cast<const BSQRecordInfo*>(rectype)->propertyoffsets[pid]);
}

StorageLocationPtr ICPPParseJSON::extractValueForEntityField(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, std::pair<std::string, std::string> fnamefkey, Evaluator& ctx)
{
    BSQTypeID ooid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    const BSQType* ootype = BSQType::g_typetable[ooid];

    BSQFieldID fid = MarshalEnvironment::g_fieldToIdMap.find(fnamefkey.second)->second;
    return SLPTR_INDEX_DATAPTR(value, dynamic_cast<const BSQEntityInfo*>(ootype)->fieldoffsets[fid]);
}

void ICPPParseJSON::prepareExtractContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto ctype = dynamic_cast<const ContainerType*>(itype);
    BSQTypeID containertypeid = MarshalEnvironment::g_typenameToIdMap.find(ctype->name)->second;
    const BSQType* collectiontype = BSQType::g_typetable[containertypeid];

    this->parsecontainerstack.push_back({});

    if(ctype->category == ContainerCategory::List)
    {
        if(LIST_LOAD_TYPE_INFO(value)->tid != BSQ_TYPE_ID_NONE)
        {
            const BSQListType* listtype = dynamic_cast<const BSQListType*>(collectiontype);
            const BSQListTypeFlavor& lflavor = BSQListOps::g_flavormap.find(listtype->etype)->second;

            BSQListOps::s_enumerate_for_extract(lflavor, LIST_LOAD_DATA(value), this->parsecontainerstack.back());
        }
    }
    else if(ctype->category == ContainerCategory::Stack)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else if(ctype->category == ContainerCategory::Queue)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else if(ctype->category == ContainerCategory::Set)
    {
        BSQ_INTERNAL_ASSERT(false);
    }
    else
    {
        if(MAP_LOAD_TYPE_INFO(value)->tid != BSQ_TYPE_ID_NONE)
        {
            const BSQMapType* maptype = dynamic_cast<const BSQMapType*>(this->containerstack.back().first);
            const BSQMapTypeFlavor& mflavor = BSQMapOps::g_flavormap.find(std::make_pair(maptype->ktype, maptype->vtype))->second;

            BSQMapOps::s_enumerate_for_extract(mflavor, MAP_LOAD_REPR(value), this->parsecontainerstack.back());
        }
    }

    this->parsecontainerstackiter.push_back(this->parsecontainerstack.back().begin());
}

std::optional<size_t> ICPPParseJSON::extractLengthForContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    const ContainerType* ctype = dynamic_cast<const ContainerType*>(itype);

    if(ctype->category == ContainerCategory::List)
    {
        auto ttype = LIST_LOAD_TYPE_INFO(value);
        if(ttype->tid == BSQ_TYPE_ID_NONE)
        {
            return 0;
        }
        else
        {
            return std::make_optional((size_t) dynamic_cast<const BSQListReprType*>(ttype)->getCount(LIST_LOAD_DATA(value)));
        }
    }
    else if(ctype->category == ContainerCategory::Stack)
    {
        BSQ_INTERNAL_ASSERT(false);
        return std::nullopt;
    }
    else if(ctype->category == ContainerCategory::Queue)
    {
        BSQ_INTERNAL_ASSERT(false);
        return std::nullopt;
    }
    else if(ctype->category == ContainerCategory::Set)
    {
        BSQ_INTERNAL_ASSERT(false);
        return std::nullopt;
    }
    else
    {
        return std::make_optional((size_t) MAP_LOAD_COUNT(value));
    }
}

StorageLocationPtr ICPPParseJSON::extractValueForContainer(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, size_t i, Evaluator& ctx)
{
    auto loc = *(this->parsecontainerstackiter.back());
    this->parsecontainerstackiter.back()++;

    return loc;
}

void ICPPParseJSON::completeExtractContainer(const APIModule* apimodule, const IType* itype, Evaluator& ctx)
{
    this->parsecontainerstackiter.pop_back();
    this->parsecontainerstack.pop_back();
}

std::optional<size_t> ICPPParseJSON::extractUnionChoice(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto utype = dynamic_cast<const UnionType*>(itype);

    auto bsqutypeid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    auto bsqutype = dynamic_cast<const BSQUnionType*>(BSQType::g_typetable[bsqutypeid]);

    std::string oname;
    if(bsqutype->tkind == BSQTypeLayoutKind::UnionRef)
    {
        oname = SLPTR_LOAD_HEAP_TYPE(value)->name;
    }
    else
    {
        oname = SLPTR_LOAD_UNION_INLINE_TYPE(value)->name;
    }

    auto ppos = std::find(utype->opts.cbegin(), utype->opts.cend(), oname);
    return std::make_optional(std::distance(utype->opts.cbegin(), ppos));
}

StorageLocationPtr ICPPParseJSON::extractUnionValue(const APIModule* apimodule, const IType* itype, StorageLocationPtr value, Evaluator& ctx)
{
    auto utype = dynamic_cast<const UnionType*>(itype);

    auto bsqutypeid = MarshalEnvironment::g_typenameToIdMap.find(itype->name)->second;
    auto bsqutype = dynamic_cast<const BSQUnionType*>(BSQType::g_typetable[bsqutypeid]);

    if(bsqutype->tkind == BSQTypeLayoutKind::UnionRef)
    {
        return value;
    }
    else
    {
        return SLPTR_LOAD_UNION_INLINE_DATAPTR(value);
    }
}
