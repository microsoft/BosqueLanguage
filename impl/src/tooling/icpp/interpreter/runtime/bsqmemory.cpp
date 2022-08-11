//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

size_t BSQType::g_typeTableSize = 0;
const BSQType** BSQType::g_typetable = nullptr;

uint8_t GCStack::sdata[BSQ_MAX_STACK] = {0};
uint8_t* GCStack::stackp = GCStack::sdata;

bool GCStack::global_init_complete = false;
PageInfo* GCStack::global_memory = nullptr;
BSQType* GCStack::global_type = nullptr;

PageInfo AllocPages::g_sential_page = {0};

Allocator Allocator::GlobalAllocator;

void gcProcessHeapOperator_nopImpl(const BSQType* btype, void** data, void* fromObj)
{
    return;
}

void gcProcessHeapOperator_inlineImpl(const BSQType* btype, void** data, void* fromObj)
{
    Allocator::gcProcessSlotsWithMask(data, fromObj, btype->allocinfo.inlinedmask);
}

void gcProcessHeapOperator_refImpl(const BSQType* btype, void** data, void* fromObj)
{
    Allocator::gcProcessSlotHeap(data, fromObj);
}

void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data, void* fromObj)
{
    Allocator::gcProcessSlotWithString(data, fromObj);
}

void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data, void* fromObj)
{
    Allocator::gcProcessSlotWithBigNum(data, fromObj);
}

void gcProcessHeapOperator_collectionImpl(const BSQType* btype, void** data, void* fromObj)
{
    Allocator::gcProcessSlotWithCollection(data, fromObj);
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
    Allocator::GlobalAllocator.processDecHeapRC(*data);
}

void gcDecOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementString(data);
}

void gcDecOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementBigNum(data);
}

void gcDecOperator_collectionImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementCollection(data);
}

void gcEvacuateParentOperator_nopImpl(const BSQType* btype, void** data, void* obj)
{
    return;
}

void gcEvacuateParentOperator_inlineImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateParentWithMask(data, obj, btype->allocinfo.inlinedmask);
}

void gcEvacuateParentOperator_refImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::GlobalAllocator.processHeapEvacuateParentViaUnique(data, obj);
}

void gcEvacuateParentOperator_stringImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateParentString(data, obj);
}

void gcEvacuateParentOperator_bignumImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateParentBigNum(data, obj);
}

void gcEvacuateParentOperator_collectionImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateParentCollection(data, obj);
}

void gcEvacuateChildOperator_nopImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    return;
}

void gcEvacuateChildOperator_inlineImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    Allocator::gcEvacuateChildWithMask(data, oobj, nobj, btype->allocinfo.inlinedmask);
}

void gcEvacuateChildOperator_refImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    Allocator::GlobalAllocator.processHeapEvacuateChildViaUnique(data, oobj, nobj);
}

void gcEvacuateChildOperator_stringImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    Allocator::gcEvacuateChildString(data, oobj, nobj);
}

void gcEvacuateChildOperator_bignumImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    Allocator::gcEvacuateChildBigNum(data, oobj, nobj);
}

void gcEvacuateChildOperator_collectionImpl(const BSQType* btype, void** data, void* oobj, void* nobj)
{
    Allocator::gcEvacuateChildCollection(data, oobj, nobj);
}
