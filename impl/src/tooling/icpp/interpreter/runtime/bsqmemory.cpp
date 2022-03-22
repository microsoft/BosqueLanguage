//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

const BSQType** BSQType::g_typetable = nullptr;

GCStackEntry GCStack::frames[BSQ_MAX_STACK];
uint32_t GCStack::stackp = 0;

void BumpSpaceAllocator::ensureSpace_slow()
{
    Allocator::GlobalAllocator.collect();
}

Allocator Allocator::GlobalAllocator;

BSQCollectionGCReprNode* Allocator::collectionnodesend = Allocator::collectionnodes;
BSQCollectionGCReprNode Allocator::collectionnodes[BSQ_MAX_STACK];
std::list<BSQCollectionIterator*> Allocator::collectioniters;
std::vector<std::list<BSQTempRootNode>> Allocator::alloctemps;

#ifdef BSQ_DEBUG_BUILD
    std::map<size_t, void*> Allocator::dbg_idToObjMap;
#endif

void gcProcessRootOperator_nopImpl(const BSQType* btype, void** data)
{
    return;
}

void gcProcessRootOperator_inlineImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<true>(data, btype->allocinfo.inlinedmask);
}

void gcProcessRootOperator_refImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlot<true>(data);
}

void gcProcessRootOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<true>(data);
}

void gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<true>(data);
}

void gcProcessHeapOperator_nopImpl(const BSQType* btype, void** data)
{
    return;
}

void gcProcessHeapOperator_inlineImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<true>(data, btype->allocinfo.inlinedmask);
}

void gcProcessHeapOperator_refImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlot<true>(data);
}

void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<true>(data);
}

void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<true>(data);
}

void gcDecOperator_nopImpl(const BSQType* btype, void** data)
{
    return;
}

void gcDecOperator_inlineImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecSlotsWithMask(data, btype->allocinfo.inlinedmask);
}

void gcDecOperator_refImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrement(*data);
}

void gcDecOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementString(*data);
}

void gcDecOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementBigNum(*data);
}

void gcClearOperator_nopImpl(const BSQType* btype, void** data)
{
    return;
}

void gcClearOperator_inlineImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlotsWithMask(data, btype->allocinfo.inlinedmask);
}

void gcClearOperator_refImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMark(*data);
}

void gcClearOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkString(*data);
}

void gcClearOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkBigNum(*data);
}

void gcMakeImmortalOperator_nopImpl(const BSQType* btype, void** data)
{
    return;
}

void gcMakeImmortalOperator_inlineImpl(const BSQType* btype, void** data)
{
    Allocator::gcMakeImmortalSlotsWithMask(data, btype->allocinfo.inlinedmask);
}

void gcMakeImmortalOperator_refImpl(const BSQType* btype, void** data)
{
    Allocator::gcMakeImmortal(*data);
}

void gcMakeImmortalOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcMakeImmortalString(*data);
}

void gcMakeImmortalOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcMakeImmortalBigNum(*data);
}
