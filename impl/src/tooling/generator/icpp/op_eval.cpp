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
    op->oftype->slclear(this->evalTargetVar(op->trgt));
}

void Evaluator::evalBoxUniqueStructToInlineOp(const BoxOp<OpCodeTag::BoxUniqueStructToInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalBoxUniqueRefToInlineOp(const BoxOp<OpCodeTag::BoxUniqueRefToInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalBoxUniqueStructToHeapOp(const BoxOp<OpCodeTag::BoxUniqueStructToHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalBoxUniqueRefToHeapOp(const BoxOp<OpCodeTag::BoxUniqueRefToHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalBoxInlineBoxToHeapOp(const BoxOp<OpCodeTag::BoxInlineBoxToHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalExtractUniqueStructFromInlineOp(const ExtractOp<OpCodeTag::ExtractUniqueStructFromInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalExtractUniqueRefFromInlineOp(const ExtractOp<OpCodeTag::ExtractUniqueRefFromInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalExtractUniqueStructFromHeapOp(const ExtractOp<OpCodeTag::ExtractUniqueStructFromHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalExtractUniqueRefFromHeapOp(const ExtractOp<OpCodeTag::ExtractUniqueRefFromHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalExtractInlineBoxFromHeapOp(const ExtractOp<OpCodeTag::ExtractInlineBoxFromHeapOp>* op)
{
    xxxx;
}

void Evaluator::evalWidenInlineOp(const BoxOp<OpCodeTag::WidenInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalNarrowInlineOp(const ExtractOp<OpCodeTag::NarrowInlineOp>* op)
{
    xxxx;
}

void Evaluator::evalLoadConstOp(const LoadConstOp* op)
{
    op->oftype->slcopy(this->evalTargetVar(op->trgt), Evaluator::evalConstArgument(op->arg));
}

const BSQType* Evaluator::loadTupleTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return (SLPTR_LOAD_UNION_INLINE_TYPE(sl));
    }
    else
    {
        assert(layout == BSQTypeKind::HeapUnion);
        return (SLPTR_LOAD_UNION_HEAP_TYPE(sl));
    }
}

StorageLocationPtr Evaluator::loadTupleDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
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

const BSQType* Evaluator::loadRecordTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    auto layout = layouttype->tkind;
    if(layout == BSQTypeKind::InlineUnion)
    {
        return (SLPTR_LOAD_UNION_INLINE_TYPE(sl));
    }
    else
    {
        assert(layout == BSQTypeKind::HeapUnion);
        return (SLPTR_LOAD_UNION_HEAP_TYPE(sl));
    }
}

StorageLocationPtr Evaluator::loadRecordDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
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

const BSQType* Evaluator::loadEntityTypeFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    xxxx;
}

StorageLocationPtr Evaluator::loadEntityDataFromAbstractLocation(StorageLocationPtr sl, const BSQType* layouttype)
{
    xxxx;
}

void Evaluator::processTupleDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->slcopy(this->evalTargetVar(dst), srctype->slindex(src, slotoffset));
}

void Evaluator::processTupleVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQTupleIndex idx, TargetVar dst, const BSQType* dsttype)
{
    auto tupleInfo = ((BSQTupleTypeInfo*)srctype->getExtraTypeInfo());
    auto voffset = tupleInfo->idxoffsets[idx];

    this->processTupleDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}

void Evaluator::processRecordDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->slcopy(this->evalTargetVar(dst), srctype->slindex(src, slotoffset));
}

void Evaluator::processRecordVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQRecordPropertyID propId, TargetVar dst, const BSQType* dsttype)
{
    auto recordInfo = ((BSQRecordTypeInfo*)srctype->getExtraTypeInfo());

    auto proppos = std::find(recordInfo->properties.cbegin(), recordInfo->properties.cend(), propId);
    assert(proppos != recordInfo->properties.cend());

    auto propidx = std::distance(recordInfo->properties.cbegin(), proppos);
    auto voffset = recordInfo->propertyoffsets[propidx];

    this->processRecordDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
}
    
void Evaluator::processEntityDirectLoadAndStore(StorageLocationPtr src, const BSQType* srctype, uint32_t slotoffset, TargetVar dst, const BSQType* dsttype)
{
    dsttype->slcopy(this->evalTargetVar(dst), srctype->slindex(src, slotoffset));
}

void Evaluator::processEntityVirtualLoadAndStore(StorageLocationPtr src, const BSQType* srctype, BSQFieldID fldId, TargetVar dst, const BSQType* dsttype)
{
    auto entityInfo = ((BSQEntityTypeInfo*)srctype->getExtraTypeInfo());

    auto fldpos = std::find(entityInfo->fields.cbegin(), entityInfo->fields.cend(), fldId);
    assert(fldpos != entityInfo->fields.cend());

    auto fldidx = std::distance(entityInfo->fields.cbegin(), fldpos);
    auto voffset = entityInfo->fieldoffsets[fldidx];

    this->processEntityDirectLoadAndStore(src, srctype, voffset, dst, dsttype);
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

void Evaluator::evalTupleHasIndexOp(const TupleHasIndexOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto tupleInfo = (BSQTupleTypeInfo*)this->loadTupleTypeFromAbstractLocation(sl, op->layouttype)->getExtraTypeInfo();
    BSQTupleIndex maxidx = (tupleInfo)->maxIndex;

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), (BSQBool)(op->idx < maxidx));
}

void Evaluator::evalRecordHasPropertyOp(const RecordHasPropertyOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto recordInfo = (BSQRecordTypeInfo*)this->loadRecordTypeFromAbstractLocation(sl, op->layouttype)->getExtraTypeInfo();
    const std::vector<BSQRecordPropertyID>& properties = recordInfo->properties;
    BSQBool hasprop = std::find(properties.cbegin(), properties.cend(), op->propId) != properties.cend();

    SLPTR_STORE_CONTENTS_AS(BSQBool, this->evalTargetVar(op->trgt), hasprop);
}

void Evaluator::evalLoadTupleIndexDirectOp(const LoadTupleIndexDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->argtype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexVirtualOp(const LoadTupleIndexVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype);
    this->processTupleVirtualLoadAndStore(sl, argtype, op->idx, op->trgt, op->trgttype);
}

void Evaluator::evalLoadTupleIndexSetGuardDirectOp(const LoadTupleIndexSetGuardDirectOp* op)
{
    this->processTupleDirectLoadAndStore(this->evalArgument(op->arg), op->argtype, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadTupleIndexSetGuardVirtualOp(const LoadTupleIndexSetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadTupleTypeFromAbstractLocation(sl, op->layouttype);
    
    BSQBool loadsafe = op->idx < ((BSQTupleTypeInfo*)argtype->getExtraTypeInfo())->maxIndex;
    if(loadsafe)
    {
        this->processTupleVirtualLoadAndStore(sl, argtype, op->idx, op->trgt, op->trgttype);
    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadRecordPropertyDirectOp(const LoadRecordPropertyDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->argtype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertyVirtualOp(const LoadRecordPropertyVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype);
    this->processRecordVirtualLoadAndStore(sl, argtype, op->propId, op->trgt, op->trgttype);
}

void Evaluator::evalLoadRecordPropertySetGuardDirectOp(const LoadRecordPropertySetGuardDirectOp* op)
{
    this->processRecordDirectLoadAndStore(this->evalArgument(op->arg), op->argtype, op->slotoffset, op->trgt, op->trgttype);
    this->processGuardVarStore(op->guard, true);
}

void Evaluator::evalLoadRecordPropertySetGuardVirtualOp(const LoadRecordPropertySetGuardVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadRecordTypeFromAbstractLocation(sl, op->layouttype);
    const std::vector<BSQRecordPropertyID>& properties = ((BSQRecordTypeInfo*)argtype->getExtraTypeInfo())->properties;

    BSQBool loadsafe = std::find(properties.cbegin(), properties.cend(), op->propId) != properties.cend();
    if(loadsafe)
    {
        this->processRecordVirtualLoadAndStore(sl, argtype, op->propId, op->trgt, op->trgttype);
    }
    this->processGuardVarStore(op->guard, loadsafe);
}

void Evaluator::evalLoadDirectFieldOp(const LoadEntityFieldDirectOp* op)
{
    this->processEntityDirectLoadAndStore(this->evalArgument(op->arg), op->argtype, op->slotoffset, op->trgt, op->trgttype);
}

void Evaluator::evalLoadVirtualFieldOp(const LoadEntityFieldVirtualOp* op)
{
    auto sl = this->evalArgument(op->arg);
    auto argtype = this->loadEntityTypeFromAbstractLocation(sl, op->layouttype);
    this->processEntityVirtualLoadAndStore(sl, argtype, op->fieldId, op->trgt, op->trgttype);
}

void Evaluator::evalInvokeFixedFunctionOp(const InvokeFixedFunctionOp* op)
{
    xxxx;
}

void Evaluator::evalInvokeFixedFunctionWGuardOp(const InvokeFixedFunctionWGuardOp* op)
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

    auto tinfo = (BSQTupleTypeInfo*)op->oftype->getExtraTypeInfo();
    for(size_t i = 0; i < tinfo->idxoffsets.size(); ++i)
    {
        tinfo->ttypes[i]->slcopy(SLPTR_INDEX(tcontents, tinfo->idxoffsets[i]), this->evalArgument(op->args[i]));
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

    auto rinfo = (BSQRecordTypeInfo*)op->oftype->getExtraTypeInfo();
    for(size_t i = 0; i < rinfo->propertyoffsets.size(); ++i)
    {
        rinfo->rtypes[i]->slcopy(SLPTR_INDEX(tcontents, rinfo->propertyoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorEphemeralListOp(const ConstructorEphemeralListOp* op)
{
    StorageLocationPtr tcontents = this->evalTargetVar(op->trgt);

    for(size_t i = 0; i < op->oftype->idxoffsets.size(); ++i)
    {
        op->oftype->etypes[i]->slcopy(SLPTR_INDEX(tcontents, op->oftype->idxoffsets[i]), this->evalArgument(op->args[i]));
    }
}

void Evaluator::evalConstructorPrimaryCollectionEmptyOp(const ConstructorPrimaryCollectionEmptyOp* op)
{
    xxxx;
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(this->evalTargetVar(op->trgt), rv);
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

void Evaluator::evalIsNoneOp(const IsNoneOp* op)
{
    xxxx;
}

void Evaluator::evalIsSomeOp(const IsSomeOp* op)
{
    xxxx;
}

void Evaluator::evalTypeTagIsOp(const TypeTagIsOp* op)
{
    xxxx;
}

void Evaluator::evalTypeTagSubtypeOfOp(const TypeTagSubtypeOfOp* op)
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


