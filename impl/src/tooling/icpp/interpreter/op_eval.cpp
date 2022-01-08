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
BSQ_LANGUAGE_ASSERT(!err, THIS->cframe->dbg_file, THIS->cframe->dbg_line, ERROR); \
\
SLPTR_STORE_CONTENTS_AS(REPRTYPE, THIS->evalTargetVar(bop->trgt), res);

//Big Macro for generating code for primitive checked binary operations
#define PrimitiveBinaryOperatorMacroChecked(THIS, OP, TAG, REPRTYPE, OPERATORW, OPERATORP, ERROR) const PrimitiveBinaryOperatorOp<TAG>* bop = static_cast<const PrimitiveBinaryOperatorOp<TAG>*>(op); \
REPRTYPE res; \
bool err = OPERATORP(SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->larg)), SLPTR_LOAD_CONTENTS_AS(REPRTYPE, THIS->evalArgument(bop->rarg)), &res); \
BSQ_LANGUAGE_ASSERT(!err, THIS->cframe->dbg_file, THIS->cframe->dbg_line, ERROR); \
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
BSQ_LANGUAGE_ASSERT(rarg != (REPRTYPE)0, THIS->cframe->dbg_file, THIS->cframe->dbg_line, "Division by zero"); \
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
SLPTR_STORE_CONTENTS_AS(BSQBool, THIS->evalTargetVar(bop->trgt), larg OPERATOR rarg);


#define BI_LAMBDA_CALL_SETUP_TEMP(TTYPE, TEMPSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_IDX(TTYPE, TEMPSL, PARAMS, PC, LPARAMS, IDXSL) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL, IDXSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_AND_RES(TTYPE, TEMPSL, RTYPE, RESSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        RESSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_POP() GCStack::popFrame();

jmp_buf Evaluator::g_entrybuff;
EvaluatorFrame Evaluator::g_callstack[BSQ_MAX_STACK];
uint8_t* Evaluator::g_constantbuffer = nullptr;

std::vector<const BSQInvokeDecl*> Evaluator::g_invokes;

std::map<BSQTypeID, const BSQRegex*> Evaluator::g_validators;
std::vector<const BSQRegex*> Evaluator::g_regexs;

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
    SLPTR_STORE_CONTENTS_AS(BSQNone, tl, BSQNoneValue);
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
    
    const BSQType* rtype = op->layouttype->getVType(sl);
    StorageLocationPtr pp = op->layouttype->getVData_NoAlloc(sl);

    //
    //TODO: this is where it might be nice to do some mono/polymorphic inline caching vtable goodness
    //

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
        this->invoke(Evaluator::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
    }
}

template <>
void Evaluator::evalInvokeFixedFunctionOp<false>(const InvokeFixedFunctionOp* op)
{
    StorageLocationPtr resl = this->evalTargetVar(op->trgt);
    this->invoke(Evaluator::g_invokes[op->invokeId], op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
}

void Evaluator::evalInvokeVirtualFunctionOp(const InvokeVirtualFunctionOp* op)
{
    auto sl = this->evalArgument(op->args[0]);

    const BSQType* etype = op->rcvrlayouttype->getVType(sl);
    StorageLocationPtr rcvrloc = op->rcvrlayouttype->getVData_NoAlloc(sl);

    auto viter = etype->vtable.find(op->invokeId);
    BSQ_INTERNAL_ASSERT(viter != etype->vtable.cend());

    StorageLocationPtr resl = this->evalTargetVar(op->trgt);
    this->vinvoke(dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[viter->second]), rcvrloc, op->args, resl, op->optmaskoffset != -1 ? this->cframe->masksbase + op->optmaskoffset : nullptr);
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
        BSQType::g_typetable[entityinfo->fields[i]]->storeValue(SLPTR_INDEX_DATAPTR(tcontents, entityinfo->fieldoffsets[i]), this->evalArgument(op->args[i]));
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
    this->pushFrame<false>(&invk->srcFile, &invk->name, cstack, mixedslots, optmask, maskslots, &invk->body);
#else
    this->pushFrame<false>(, cstack, mixedslots, optmask, maskslots, &invk->body);
#endif
}
    
void Evaluator::invokePostlude()
{
    this->popFrame();
    GCStack::popFrame();
}

void Evaluator::evaluatePrimitiveBody(const BSQInvokePrimitiveDecl* invk, const std::vector<StorageLocationPtr>& params, StorageLocationPtr resultsl, const BSQType* restype)
{
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
    case BSQPrimitiveImplTag::mask_empty: {
        auto bvmask = SLPTR_LOAD_CONTENTS_AS(BSQMask, params[0]);
        SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, (BSQBool)std::equal(bvmask.bits, bvmask.bits + 4, g_empty_bsqmask.bits));
        break;
    }
    case BSQPrimitiveImplTag::mask_bit: {
        auto bvmask = SLPTR_LOAD_CONTENTS_AS(BSQMask, params[0]);
        auto i = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);
        SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, bvmask.bits[i]);
        break;
    }
    case BSQPrimitiveImplTag::pv_count: {
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(params[0]));
        auto ct = std::count_if(mask.bits, mask.bits + 4, [](BSQBool bv) { return bv; });
        SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, (BSQNat)ct);
        break;
    }
    case BSQPrimitiveImplTag::pv_get: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        pvtype->get(params[0], SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]), resultsl);
        break;
    }
    case BSQPrimitiveImplTag::pv_select: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtype);
        auto sl = SLPTR_LOAD_HEAP_DATAPTR(params[0]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl);

        size_t pos = 0;
        for(size_t i = 0; i < 4; ++i) {
            if(mask.bits[i]) {
                ((BSQMask*)respv)->bits[pos] = BSQTRUE;

                auto into = pvtype->storagepos(respv, pos++);
                pvtype->get(sl, i, into);
            }
        }

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
        break;
    }
    case BSQPrimitiveImplTag::pv_slice_start: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtype);
        auto sl = SLPTR_LOAD_HEAP_DATAPTR(params[0]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl);
        auto nstart = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);

        size_t pos = 0;
        for(size_t i = nstart; i < 4; ++i) {
            if(mask.bits[i]) {
                ((BSQMask*)respv)->bits[pos] = BSQTRUE;

                auto into = pvtype->storagepos(respv, pos++);
                pvtype->get(sl, i, into);
            }
        }

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
        break;
    }
    case BSQPrimitiveImplTag::pv_slice_end: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtype);
        auto sl = SLPTR_LOAD_HEAP_DATAPTR(params[0]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl);
        auto nend = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);

        size_t pos = 0;
        for(size_t i = 0; i < nend; ++i) {
            if(mask.bits[i]) {
                ((BSQMask*)respv)->bits[pos] = BSQTRUE;

                auto into = pvtype->storagepos(respv, pos++);
                pvtype->get(sl, i, into);
            }
        }

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
        break;
    }
    case BSQPrimitiveImplTag::pv_reverse: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtype);
        auto sl = SLPTR_LOAD_HEAP_DATAPTR(params[0]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl);

        size_t pos = 0;
        auto ct = std::count_if(mask.bits, mask.bits + 4, [](BSQBool bv) { return bv; }) - 1;

        SLPTR_STORE_CONTENTS_AS(BSQMask, sl, mask);
        for(size_t i = 0; i < ct; ++i) {
            auto into = pvtype->storagepos(respv, pos++);
            pvtype->get(sl, ct - i, into);
        }

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
        break;
    }
    case BSQPrimitiveImplTag::pv_append: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtype);
        size_t pos = 0;

        auto sl1 = SLPTR_LOAD_HEAP_DATAPTR(params[0]);
        auto mask1 = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl1);
        for(size_t i = 0; i < 4 & mask1.bits[i]; ++i) {
            auto into = pvtype->storagepos(respv, pos++);
            pvtype->get(sl1, i, into);
        }

        auto sl2 = SLPTR_LOAD_HEAP_DATAPTR(params[1]);
        auto mask2 = SLPTR_LOAD_CONTENTS_AS(BSQMask, sl2);
        for(size_t i = 0; i < 4 & mask2.bits[i]; ++i) {
            auto into = pvtype->storagepos(respv, pos++);
            pvtype->get(sl2, i, into);
        }

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
        break;
    }
    case BSQPrimitiveImplTag::apply_pred: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BI_LAMBDA_CALL_SETUP_TEMP(etype, esl, params, pc, lparams)

            size_t pos = 0;
            BSQMask* rrm = (BSQMask*)resultsl;
            while(mask.bits[pos] & (pos < 4)) {
                pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), pos, esl);
                this->linvoke(icall, lparams, rrm->bits + pos);
                pos++;
            }

            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::apply_pred_idx: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BSQNat idx = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);
            BI_LAMBDA_CALL_SETUP_TEMP_IDX(etype, esl, params, pc, lparams, &idx)

            size_t pos = 0;
            BSQMask* rrm = (BSQMask*)resultsl;
            while(mask.bits[pos] & (pos < 4)) {
                pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), pos, esl);
                this->linvoke(icall, lparams, rrm->bits + pos);
                pos++;
                idx++;
            }

            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_find_pred: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BI_LAMBDA_CALL_SETUP_TEMP(etype, esl, params, pc, lparams)

            size_t pos = 0;
            BSQBool found = BSQFALSE;
            while(mask.bits[pos] & (pos < 4)) {
                pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), pos, esl);
                this->linvoke(icall, lparams, &found);
                if(found) {
                    break;
                }
                pos++;
            }

            SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_find_pred_idx: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BSQNat idx = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);
            BI_LAMBDA_CALL_SETUP_TEMP_IDX(etype, esl, params, pc, lparams, &idx)

            size_t pos = 0;
            BSQBool found = BSQFALSE;
            while(mask.bits[pos] & (pos < 4)) {
                pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), pos, esl);
                this->linvoke(icall, lparams, &found);
                if(found) {
                    break;
                }
                pos++;
                idx++;
            }

            SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_find_last_pred: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BI_LAMBDA_CALL_SETUP_TEMP(etype, esl, params, pc, lparams)

            size_t pos = 0;
            BSQBool found = BSQFALSE;
            while(pos < 4) {
                if(mask.bits[3 - pos])
                {
                    pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), 3 - pos, esl);
                    this->linvoke(icall, lparams, &found);
                    if(found) 
                    {
                        break;
                    }
                }
                pos++;
            }

            SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_find_last_pred_idx: {
        auto pvtype = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etype = BSQType::g_typetable[pvtype->elemtype];

        const BSQPCode* pc = invk->pcodes.find("p")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BSQNat idx = SLPTR_LOAD_CONTENTS_AS(BSQNat, params[1]);
            BI_LAMBDA_CALL_SETUP_TEMP_IDX(etype, esl, params, pc, lparams, &idx)

            size_t pos = 0;
            BSQBool found = BSQFALSE;
            while(pos < 4) {
                if(mask.bits[3 - pos])
                {
                    pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), 3 - pos, esl);
                    this->linvoke(icall, lparams, &found);
                    if(found) 
                    {
                        break;
                    }
                }
                pos++;
            }

            SLPTR_STORE_CONTENTS_AS(BSQNat, resultsl, pos);
            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_map: {
        auto pvtypeT = dynamic_cast<const BSQPartialVectorType*>(invk->enclosingtype);
        auto etypeT = BSQType::g_typetable[pvtypeT->elemtype];

        auto pvtypeR = dynamic_cast<const BSQPartialVectorType*>(invk->resultType);
        auto etypeR = BSQType::g_typetable[pvtypeR->elemtype];

        const BSQPCode* pc = invk->pcodes.find("f")->second;
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(Evaluator::g_invokes[pc->code]);
        auto mask = SLPTR_LOAD_CONTENTS_AS(BSQMask, SLPTR_LOAD_HEAP_DATAPTR(params[0]));
        {
            BI_LAMBDA_CALL_SETUP_TEMP_AND_RES(etypeT, esl, pvtypeR, rsl, params, pc, lparams)

            size_t pos = 0;
            BSQMask* rrm = (BSQMask*)rsl;
            while(mask.bits[pos] & (pos < 4)) {
                auto into = pvtype->storagepos(rsl, pos++);
                pvtype->get(SLPTR_LOAD_HEAP_DATAPTR(params[0]), pos, esl);
                this->linvoke(icall, lparams, );
                pos++;
            }

            auto respv = Allocator::GlobalAllocator.allocateDynamic(pvtypeR);
            GC_MEM_COPY(respv, rsl, pvtypeR->allocinfo.inlinedatasize);
            SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(resultsl, respv);
            BI_LAMBDA_CALL_SETUP_POP()
        }
        break;
    }
    case BSQPrimitiveImplTag::pv_map_idx: {
        xxxx;
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
    uint8_t* mixedslots = cstack + invk->scalarstackBytes;
    GC_MEM_ZERO(cstack, cssize);

    size_t maskslotbytes = invk->maskSlots * sizeof(BSQBool);
    BSQBool* maskslots = (BSQBool*)BSQ_STACK_SPACE_ALLOC(maskslotbytes);
    GC_MEM_ZERO(maskslots, maskslotbytes);

    GCStack::pushFrame((void**)mixedslots, invk->mixedMask);
#ifdef BSQ_DEBUG_BUILD
    this->pushFrame<false>(&invk->srcFile, &invk->name, nullptr, cstack, mixedslots, nullptr, maskslots, &invk->body);
#else
    this->pushFrame<false>(nullptr, cstack, mixedslots, nullptr, maskslots, &invk->body);
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
    this->pushFrame<false>(&invk->srcFile, &invk->name, (StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, maskslots, &invk->body);
#else
    this->pushFrame<false>((StorageLocationPtr*)argsbase, cstack, mixedslots, nullptr, maskslots, &invk->body);
#endif

    this->evaluateBody(resultsl, restype, resarg);

    this->popFrame();
}

/*

bool entityNoneJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_null())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNoneType*>(BSQType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
        return true;
    }
}

bool entityBoolJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_boolean())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQBoolType*>(BSQType::g_typeBool)->storeValueDirect(sl, j.get<bool>() ? BSQTRUE : BSQFALSE);
        return true;
    }
}

bool entityNatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto uval = parseToUnsignedNumber(j);
    if(!uval.has_value())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNatType*>(BSQType::g_typeNat)->storeValueDirect(sl, uval.value());
        return true;
    }
}

bool entityBigNatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto bnval = parseToBigUnsignedNumber(j);
    if(!bnval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, std::stoull(bnval.value()));
    return true;
}

bool entityIntJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto ival = parseToSignedNumber(j);
    if(!ival.has_value())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQIntType*>(BSQType::g_typeInt)->storeValueDirect(sl, ival.value());
        return true;
    }
}

bool entityBigIntJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto bival = parseToBigUnsignedNumber(j);
    if(!bival.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, std::stoll(bival.value()));
    return true;
}

bool entityFloatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto fval = parseToRealNumber(j);
    if(!fval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQFloatType*>(BSQType::g_typeFloat)->storeValueDirect(sl, std::stod(fval.value()));
    return true;
}

bool entityDecimalJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto dval = parseToDecimalNumber(j);
    if(!dval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQDecimalType*>(BSQType::g_typeDecimal)->storeValueDirect(sl, std::stod(dval.value()));
    return true;
}

bool entityRationalJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_array() || j.size() != 2)
    {
        return false;
    }

    auto numtype = dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt);
    auto denomtype = dynamic_cast<const BSQNatType*>(BSQType::g_typeNat);

    BSQRational rr;
    auto oknum = numtype->consops.fpJSONParse(numtype, j[0], &rr.numerator);
    auto okdenom = denomtype->consops.fpJSONParse(denomtype, j[1], &rr.denominator);

    if(!oknum || !okdenom)
    {
        return false;
    }

    dynamic_cast<const BSQRationalType*>(BSQType::g_typeRational)->storeValueDirect(sl, rr);
    return true;
}


bool entityStringJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = j.get<std::string>();
        BSQString s = g_emptyString;
        if(sstr.size() == 0)
        {
            //already empty
        }
        else if(sstr.size() < 16) 
        {
            s.u_inlineString = BSQInlineString::create((const uint8_t*)sstr.c_str(), sstr.size());
        }
        else if(sstr.size() <= 256)
        {
            auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&sstr](const std::pair<size_t, const BSQType*>& cc) {
                return cc.first > sstr.size();
            });
            s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp->second);
            BSQ_MEM_COPY(s.u_data, sstr.c_str(), sstr.size());
        }
        else
        {
            //
            //TODO: split the string into multiple parts
            //
            assert(false);
        }
        
        dynamic_cast<const BSQStringType*>(BSQType::g_typeString)->storeValueDirect(sl, s);
        return true;
    }
}


bool entityLogicalTimeJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    std::optional<std::string> nval = parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQLogicalTimeType*>(BSQType::g_typeLogicalTime)->storeValueDirect(sl, std::stoull(nval.value()));
    return true;
}


bool enumJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_string())
    {
        return false;
    }
    else
    {
        auto ename = j.get<std::string>();

        auto etype = dynamic_cast<const BSQEnumType*>(btype);
        auto cpos = std::find_if(etype->enuminvs.cbegin(), etype->enuminvs.cend(), [&ename](const std::pair<std::string, uint32_t>& entry) {
            return entry.first == ename;
        })->second;
    
        etype->underlying->storeValue(sl, Environment::g_constantbuffer + cpos);
        return true;
    }
}

bool tupleJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto tupinfo = dynamic_cast<const BSQTupleInfo*>(btype);
    if(!j.is_array() || tupinfo->ttypes.size() != j.size())
    {
        return false;
    }

    if(btype->tkind == BSQTypeLayoutKind::Struct)
    {
        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            assert(i < j.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            bool ok = etype->consops.fpJSONParse(etype, j[i], SLPTR_INDEX_DATAPTR(sl, tupinfo->idxoffsets[i]));
            if(!ok)
            {
                return false;
            }
        }
    }
    else
    {
        auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.assigndatasize);
        GCStack::pushFrame(&vbuff, btype->allocinfo.heapmask);

        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            assert(i < j.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            bool ok = etype->consops.fpJSONParse(etype, j[i], SLPTR_INDEX_DATAPTR(vbuff, tupinfo->idxoffsets[i]));
            if(!ok)
            {
                return false;
            }
        }

        auto tt = Allocator::GlobalAllocator.allocateDynamic(btype);
        GC_MEM_COPY(tt, vbuff, btype->allocinfo.assigndatasize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tt);

        GCStack::popFrame();
    }

    return true;
}

bool recordJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto recinfo = dynamic_cast<const BSQRecordInfo*>(btype);
    if(!j.is_object() || recinfo->rtypes.size() != j.size())
    {
        return false;
    }

    auto allprops = std::all_of(recinfo->properties.cbegin(), recinfo->properties.cend(), [&j](const BSQRecordPropertyID prop){
                return j.contains(BSQType::g_propertynamemap[prop]);
            });
    if(!allprops)
    {
        return false;
    }

    if(btype->tkind == BSQTypeLayoutKind::Struct)
    {
        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertynamemap[recinfo->properties[i]];

            bool ok = etype->consops.fpJSONParse(etype, j[pname], SLPTR_INDEX_DATAPTR(sl, recinfo->propertyoffsets[i]));
            if(!ok)
            {
                return false;
            }
        }
    }
    else
    {
        auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);
        GCStack::pushFrame(&vbuff, btype->allocinfo.heapmask);

        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertynamemap[recinfo->properties[i]];

            bool ok = etype->consops.fpJSONParse(etype, j[pname], SLPTR_INDEX_DATAPTR(vbuff, recinfo->propertyoffsets[i]));
            if(!ok)
            {
                return false;
            }
        }

        auto tt = Allocator::GlobalAllocator.allocateDynamic(btype);
        GC_MEM_COPY(tt, vbuff, btype->allocinfo.assigndatasize);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tt);

        GCStack::popFrame();
    }

    return true;
}

const BSQType* unionJSONParse_impl_select(const BSQUnionType* utype, json j, StorageLocationPtr sl)
{
    std::vector<const BSQType*> opts;
    std::transform(utype->subtypes.cbegin(), utype->subtypes.cend(), std::back_inserter(opts), [](const BSQTypeID tid) {
        return BSQType::g_typetable[tid];
    });

    if(j.is_object())
    {
        //TODO: map option once we have map type
        auto mapopt = opts.cend();
        //std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
        //    return dynamic_cast<const BSQListType*>(opt) != nullptr;
        //});

        auto recordopt = std::find_if(opts.cbegin(), opts.cend(), [&j](const BSQType* opt) {
            const BSQRecordInfo* ropt = dynamic_cast<const BSQRecordInfo*>(opt);
            if(ropt == nullptr || ropt->properties.size() != j.size())
            {
                return false;
            }
            else
            {
                return std::all_of(ropt->properties.cbegin(), ropt->properties.cend(), [&j](const BSQRecordPropertyID prop){
                    return j.contains(BSQType::g_propertymap[prop]);
                });
            }
        });

        auto oftype = (mapopt != opts.cend()) ? *mapopt : *recordopt;
        oftype->consops.fpJSONParse(oftype, j, sl);
        return oftype;
    }
    else if(j.is_array())
    {
        auto listopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQListType*>(opt) != nullptr;
        });

        auto tupleopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQTupleInfo*>(opt) != nullptr;
        });

        auto oftype = (listopt != opts.cend()) ? *listopt : *tupleopt;
        oftype->consops.fpJSONParse(oftype, j, sl);
        return oftype;
    }
    else
    {
        for(size_t i = 0; i < opts.size(); ++i)
        {
            auto opt = opts[i];

            auto ismap = false;
            auto islist = dynamic_cast<const BSQListType*>(opt) != nullptr;
            auto isrecord = dynamic_cast<const BSQRecordInfo*>(opt) != nullptr;
            auto istuple = dynamic_cast<const BSQTupleInfo*>(opt) != nullptr;
            if(!ismap && !islist && !isrecord && !istuple)
            {
                auto okparse = opt->consops.fpJSONParse(opt, j, sl);
                if(okparse)
                {
                    return opt;
                }
            }
        }

        return nullptr;
    }
}


bool unionJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto utype = dynamic_cast<const BSQUnionType*>(btype);

    auto rsl = sl;
    if(utype->isInline())
    {
        rsl = SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);
    }

    auto ptype = unionJSONParse_impl_select(utype, j, rsl);
    if(ptype == nullptr)
    {
        return false;
    }

    if(utype->isInline())
    {
        SLPTR_STORE_UNION_INLINE_TYPE(ptype, sl);
    }

    return true;
}
*/