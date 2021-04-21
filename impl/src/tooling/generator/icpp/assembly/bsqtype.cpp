//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"

void gcDecOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementSlots(data, btype->ptrcount);
}

void gcDecOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecSlotsWithMask(data, btype->refmask);
}

void gcClearOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlots(data, btype->ptrcount);
}

void gcClearOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlotsWithMask(data, btype->refmask);
}

void gcProcessRootOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlots<true>(data, btype->ptrcount);
}

void gcProcessRootOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<true>(data, btype->refmask);
}

void gcProcessHeapOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlots<false>(data, btype->ptrcount);
}

void gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<false>(data, btype->refmask);
}

template <>
GCProcessOperatorFP BSQType::getProcessFP<true>() const
{
    return this->fpProcessObjRoot;
}

template <>
inline GCProcessOperatorFP BSQType::getProcessFP<false>() const
{
    return this->fpProcessObjHeap;
}

std::string tupleDisplay_impl(const BSQType* btype, void** data)
{
    xxxx;
}

std::string recordDisplay_impl(const BSQType* btype, void** data)
{
    xxxx;
}

std::string entityDisplay_impl(const BSQType* btype, void** data)
{
    xxxx;
}

std::string ephemeralDisplay_impl(const BSQType* btype, void** data)
{
    xxxx;
}
