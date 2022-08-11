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

void gcEvacuateOperator_nopImpl(const BSQType* btype, void** data, void* obj)
{
    return;
}

void gcEvacuateOperator_inlineImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateWithMask(data, obj, btype->allocinfo.inlinedmask);
}

void gcEvacuateOperator_refImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::GlobalAllocator.processHeapEvacuate(obj, data);
}

void gcEvacuateOperator_stringImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateString(data, obj);
}

void gcEvacuateOperator_bignumImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateBigNum(data, obj);
}

void gcEvacuateOperator_collectionImpl(const BSQType* btype, void** data, void* obj)
{
    Allocator::gcEvacuateCollection(data, obj);
}
