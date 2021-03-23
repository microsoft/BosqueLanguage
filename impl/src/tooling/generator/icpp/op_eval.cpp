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
    auto sl = this->evalArgument(op->arg);
    auto voffset = op->argtype->idxoffsets[op->idx];

    auto tdata = op->argtype->isValue ? sl : SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(sl);
    op->trgttype->slcopy(this->evalTargetVar(op->trgt), SLPTR_INDEX(tdata, voffset));
}

void Evaluator::evalLoadTupleIndexVirtual(const LoadTupleIndexVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    const BSQTupleType* ttype = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype)->maxIndex;

    xxxx;
}

void Evaluator::evalLoadTupleIndexSetGuardDirect(const LoadTupleIndexSetGuardDirectOp* op)
{
    xxxx;
}

void Evaluator::evalLoadTupleIndexSetGuardVirtual(const LoadTupleIndexSetGuardVirtualOp* op)
{
    xxxx;
}

void Evaluator::evalLoadRecordProperty(const LoadRecordPropertyOp* op)
{
    xxxx;
}

void Evaluator::evalLoadRecordPropertySetGuard(const LoadRecordPropertySetGuardOp* op)
{
    xxxx;
}

void Evaluator::evalLoadField(const LoadFieldOp* op)
{
    xxxx;
}







