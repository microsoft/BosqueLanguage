//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

const BSQType** BSQType::g_typetable = nullptr;

void gcDecOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementSlots(data, btype->ptrcount);
}

void gcDecOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecSlotsWithMask(data, btype->refmask);
}

void gcDecOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementString(data);
}

void gcClearOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlots(data, btype->ptrcount);
}

void gcClearOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlotsWithMask(data, btype->refmask);
}

void gcClearOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkString(data);
}

void gcProcessRootOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlots<true>(data, btype->ptrcount);
}

void gcProcessRootOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<true>(data, btype->refmask);
}

void gcProcessRootOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<true>(data);
}

void gcProcessHeapOperator_packedImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlots<false>(data, btype->ptrcount);
}

void gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<false>(data, btype->refmask);
}

void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<false>(data);
}

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQTupleType* ttype = (const BSQTupleType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#[" : "@[";
    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        auto itype = ttype->ttypes[i];
        auto idata = isstruct ? SLPTR_INDEX_INLINE(data, ttype->idxoffsets[i]) : SLPTR_INDEX_HEAP(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "]";

    return res;
}

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQRecordType* ttype = (const BSQRecordType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#{" : "@{";
    for(size_t i = 0; i < ttype->properties.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += Environment::g_propertymap[ttype->properties[i]] + ":";

        auto itype = ttype->rtypes[i];
        auto idata = isstruct ? SLPTR_INDEX_INLINE(data, ttype->propertyoffsets[i]) : SLPTR_INDEX_HEAP(data, ttype->propertyoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQEntityType* ttype = (const BSQEntityType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = ttype->name + (isstruct ? "#{" : "@{");
    for(size_t i = 0; i < ttype->fields.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += Environment::g_fieldmap[ttype->fields[i]] + ":";

        auto itype = ttype->ftypes[i];
        auto idata = isstruct ? SLPTR_INDEX_INLINE(data, ttype->fieldoffsets[i]) : SLPTR_INDEX_HEAP(data, ttype->fieldoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQEphemeralListType* ttype = (const BSQEphemeralListType*)btype;
    std::string res = "@(|";
    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        auto itype = ttype->etypes[i];
        auto idata = SLPTR_INDEX_INLINE(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "|)";

    return res;
}

std::string inlineUnionDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(data);
    return rtype->fpDisplay(rtype, SLPTR_LOAD_UNION_INLINE_DATAPTR(data));
}

std::string heapUnionDisplay_impl(const BSQType* btype, void** data)
{
    auto rtype = SLPTR_LOAD_UNION_HEAP_TYPE(data);
    return rtype->fpDisplay(rtype, SLPTR_LOAD_UNION_HEAP_DATAPTR(data));
}
