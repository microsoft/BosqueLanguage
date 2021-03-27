//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

std::wstring* Evaluator::getCurrentFile()
{
    return xxx;
}

uint64_t Evaluator::getCurrentLine()
{
    return xxxx;
}

uint64_t Evaluator::getCurrentColumn()
{
    return xxxx;
}

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

void Evaluator::evalDeadFlow()
{
    //This should be unreachable
    BSQ_INTERNAL_ASSERT(false);
}

void Evaluator::evalAbort(const AbortOp *op)
{
    BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
}

void Evaluator::evalAssertCheck(const AssertOp *op)
{
    auto val = this->evalArgument(op->arg);
    if (!SLPTR_LOAD_CONTENTS_AS(BSQBool, val))
    {
        BSQ_LANGUAGE_ABORT(op->msg, this.getCurrentFile(), this.getCurrentLine());
    }
}

void Evaluator::evalDebug(const DebugOp *op)
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

void Evaluator::evalLoadUnintVariableValue(const LoadUnintVariableValueOp* op)
{
    op->oftype->slclear(this->evalTargetVar(op->trgt));
}

void Evaluator::evalConvertValue(const ConvertValueOp* op)
{
    xxxx;
}

void Evaluator::evalLoadConst(const LoadConstOp* op)
{
    op->oftype->slcopy(this->evalTargetVar(op->trgt), Evaluator::evalConstArgument(op->arg));
}

const BSQTupleType* Evaluator::loadTupleTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return ((BSQTupleType*)SLPTR_LOAD_UNION_INLINE_TYPE(sl));
    }
    else if(layout == BSQTypeKind::HeapUnion)
    {
        return ((BSQTupleType*)SLPTR_LOAD_UNION_HEAP_TYPE(sl));
    }
    else
    {
        assert(layout == BSQTypeKind::AbstractTuple);

        if(((const BSQAbstractTupleType*)layouttype)->isValue)
        {
            return ((BSQTupleType*)SLPTR_LOAD_UNION_INLINE_TYPE(sl));
        }
        else
        {
            return ((BSQTupleType*)SLPTR_LOAD_UNION_HEAP_TYPE(sl));
        }
    }
}

StorageLocationPtr Evaluator::loadTupleDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);

    }
    else if(layout == BSQTypeKind::HeapUnion)
    {
        return SLPTR_LOAD_UNION_HEAP_DATAPTR(sl);
    }
    else
    {
        assert(layout == BSQTypeKind::AbstractTuple);

        if(((const BSQAbstractTupleType*)layouttype)->isValue)
        {
            return SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);
        }
        else
        {
            return SLPTR_LOAD_UNION_HEAP_DATAPTR(sl);
        }
    }
}

const BSQRecordType* Evaluator::loadRecordTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return ((BSQRecordType*)SLPTR_LOAD_UNION_INLINE_TYPE(sl));
    }
    else if(layout == BSQTypeKind::HeapUnion)
    {
        return ((BSQRecordType*)SLPTR_LOAD_UNION_HEAP_TYPE(sl));
    }
    else
    {
        assert(layout == BSQTypeKind::AbstractRecord);

        if(((const BSQAbstractRecordType*)layouttype)->isValue)
        {
            return ((BSQRecordType*)SLPTR_LOAD_UNION_INLINE_TYPE(sl));
        }
        else
        {
            return ((BSQRecordType*)SLPTR_LOAD_UNION_HEAP_TYPE(sl));
        }
    }
}

StorageLocationPtr Evaluator::loadRecordDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);
    }
    else if(layout == BSQTypeKind::HeapUnion)
    {
        return SLPTR_LOAD_UNION_HEAP_DATAPTR(sl);
    }
    else
    {
        assert(layout == BSQTypeKind::AbstractRecord);

        if(((const BSQAbstractRecordType*)layouttype)->isValue)
        {
            return SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);
        }
        else
        {
            return SLPTR_LOAD_UNION_HEAP_DATAPTR(sl);
        }
    }
}

const BSQType* Evaluator::loadEntityTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    xxxx;
}

StorageLocationPtr Evaluator::loadEntityDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    xxxx;
}

void Evaluator::processTupleDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    auto tdata = isvalue ? src : SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    dsttype->slcopy(this->evalTargetVar(dst), SLPTR_INDEX(tdata, slotoffset));
}

void Evaluator::processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQTupleType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype)
{
    auto voffset = srctype->idxoffsets[idx];

    this->processTupleDirectLoadAndStore(src, srctype->isValue, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    auto tdata = isvalue ? src : SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    dsttype->slcopy(this->evalTargetVar(dst), SLPTR_INDEX(tdata, slotoffset));
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQRecordType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    auto proppos = std::find(srctype->properties.cbegin(), srctype->properties.cend(), propId);
    assert(proppos != srctype->properties.cend());

    auto propidx = std::distance(srctype->properties.cbegin(), proppos);
    auto voffset = srctype->propertyoffsets[propidx];

    this->processRecordDirectLoadAndStore(src, srctype->isValue, voffset, dst, dsttype);
}
    
void Evaluator::processEntityDirectLoadAndStore(StorageLocationPtr src, BSQBool isvalue, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    auto tdata = isvalue ? src : SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src);
    dsttype->slcopy(this->evalTargetVar(dst), SLPTR_INDEX(tdata, slotoffset));
}

void Evaluator::processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQStdEntityType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype)
{
    auto fldpos = std::find(srctype->fields.cbegin(), srctype->fields.cend(), fldId);
    assert(fldpos != srctype->fields.cend());

    auto fldidx = std::distance(srctype->fields.cbegin(), fldpos);
    auto voffset = srctype->fieldoffsets[fldidx];

    this->processEntityDirectLoadAndStore(src, srctype->isValue, voffset, dst, dsttype);
}

void Evaluator::processGuardVarStore(const BSQGuard& gv, BSQBool f)
{
    if(gv.gindex == -1)
    {
        SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(gv.gvar), f);
    }
    else
    {
        auto mask = this->evalMaskLocation(gv.gmaskoffset);
        mask[gv.gindex] = f;
    }
}

void Evaluator::evalTupleHasIndex(const TupleHasIndexOp* op)
{
    auto sl = this->evalArgument(op->arg);
    BSQTupleIndex maxidx = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype)->maxIndex;

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)(op->idx < maxidx));
}

void Evaluator::evalRecordHasProperty(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);
    const std::vector<BSQRecordPropertyID>& properties = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype)->properties;
    BSQBool hasprop = std::find(properties.cbegin(), properties.cend(), op->propId) != properties.cend();

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), hasprop);
}

void Evaluator::evalLoadTupleIndexDirect(const LoadTupleIndexDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->argtype->isValue, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexVirtual(const LoadTupleIndexVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype);
    this->processTupleVirtualLoadAndStore(sl, argtype, op->idx, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexSetGuardDirect(const LoadTupleIndexSetGuardDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->argtype->isValue, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadTupleIndexSetGuardVirtual(const LoadTupleIndexSetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype);

    BSQBool loadsafe = op->idx < argtype->maxIndex;
    if(loadsafe)
    {
        this->processTupleVirtualLoadAndStore(sl, argtype, op->idx, op->trgt, op->trgttype);
    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadRecordPropertyDirect(const LoadRecordPropertyDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->argtype->isValue, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertyVirtual(const LoadRecordPropertyVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype);
    this->processRecordVirtualLoadAndStore(sl, argtype, op->propId, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertySetGuardDirect(const LoadRecordPropertySetGuardDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->argtype->isValue, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadRecordPropertySetGuardVirtual(const LoadRecordPropertySetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype);
    const std::vector<BSQRecordPropertyID>& properties = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype)->properties;

    BSQBool loadsafe = std::find(properties.cbegin(), properties.cend(), op->propId) != properties.cend();
    if(loadsafe)
    {
        this->processRecordVirtualLoadAndStore(sl, argtype, op->propId, op->trgt, op->trgttype);
    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadDirectField(const LoadEntityFieldDirectOp* op)
{
    this->processEntityDirectLoadAndStore(this->evalArgument(op->arg), op->argtype->isValue, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadVirtualField(const LoadEntityFieldVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadEntityTypeFromAbstractLocation(sl, op->layouttype);
    this->processEntityVirtualLoadAndStore(sl, (BSQStdEntityType*)argtype, op->fieldId, op->trgt, op->trgttype);
}

void Evaluator::evalInvokeFixedFunction(const InvokeFixedFunctionOp* op)
{
    xxxx;
}

void Evaluator::evalInvokeVirtualFunction(const InvokeVirtualFunctionOp* op)
{
    //NOT IMPLEMENTED
    assert(false);
}

void Evaluator::evalInvokeVirtualOperator(const InvokeVirtualOperatorOp* op)
{
    //NOT IMPLEMENTED
    assert(false);
}

void Evaluator::evalConstructorTuple(const ConstructorTupleOp* op)
{
    StorageLocationPtr sl = this->evalTargetVar(op->trgt);
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->isValue)
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
        op->oftype->ttypes[i]->slcopy(SLPTR_INDEX(tcontents, op->oftype->idxoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorRecord(const ConstructorRecordOp* op)
{
    StorageLocationPtr sl = this->evalTargetVar(op->trgt);
    StorageLocationPtr tcontents = nullptr;
    if(op->oftype->isValue)
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
        op->oftype->rtypes[i]->slcopy(SLPTR_INDEX(tcontents, op->oftype->propertyoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorEphemeralList(const ConstructorEphemeralListOp* op)
{
    StorageLocationPtr tcontents = this->evalTargetVar(op->trgt);

    for(size_t i = 0; i < op->oftype->idxoffsets.size(); ++i)
    {
        op->oftype->etypes[i]->slcopy(SLPTR_INDEX(tcontents, op->oftype->idxoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorPrimaryCollectionEmpty(const ConstructorPrimaryCollectionEmptyOp* op)
{
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), nullptr);
}

void Evaluator::evalConstructorPrimaryCollectionSingletons(const ConstructorPrimaryCollectionSingletonsOp* op)
{
    xxxx;
}

void Evaluator::evalConstructorPrimaryCollectionCopies(const ConstructorPrimaryCollectionCopiesOp* op)
{
    assert(false);
}

void Evaluator::evalConstructorPrimaryCollectionMixed(const ConstructorPrimaryCollectionMixedOp* op)
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




