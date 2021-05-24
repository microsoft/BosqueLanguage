//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

const BSQType** BSQType::g_typetable = nullptr;

void gcDecOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecSlotsWithMask(data, btype->refmask);
}

void gcDecOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementString(data);
}

void gcDecOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementBigNum(data);
}

void gcClearOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkSlotsWithMask(data, btype->refmask);
}

void gcClearOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkString(data);
}

void gcClearOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkBigNum(data);
}

void gcProcessRootOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<true>(data, btype->refmask);
}

void gcProcessRootOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<true>(data);
}

void gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<true>(data);
}

void gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotsWithMask<false>(data, btype->refmask);
}

void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<false>(data);
}

void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<false>(data);
}

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQTupleAbstractType* ttype = (const BSQTupleAbstractType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#[" : "@[";
    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        auto itype = Environment::g_typemap[ttype->ttypes[i]];
        auto idata = ttype->indexStorageLocationOffset(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "]";

    return res;
}

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQRecordAbstractType* ttype = (const BSQRecordAbstractType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#{" : "@{";
    for(size_t i = 0; i < ttype->properties.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += Environment::g_propertymap[ttype->properties[i]] + ":";

        auto itype = Environment::g_typemap[ttype->rtypes[i]];
        auto idata = ttype->indexStorageLocationOffset(data, ttype->propertyoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQEntityAbstractType* ttype = (const BSQEntityAbstractType*)btype;
    bool isstruct = ttype->tkind == BSQTypeKind::Struct;
    std::string res = ttype->name + (isstruct ? "#{" : "@{");
    for(size_t i = 0; i < ttype->fields.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += Environment::g_fieldmap[ttype->fields[i]] + ":";

        auto itype = Environment::g_typemap[ttype->ftypes[i]];
        auto idata = ttype->indexStorageLocationOffset(data, ttype->fieldoffsets[i]);
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

        auto itype = Environment::g_typemap[ttype->etypes[i]];
        auto idata = SLPTR_INDEX_DATAPTR(data, ttype->idxoffsets[i]);
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
    auto rtype = SLPTR_LOAD_HEAP_TYPE(data);
    if(rtype->isStructStorage())
    {
        return rtype->fpDisplay(rtype, SLPTR_LOAD_HEAP_DATAPTR(data));
    }
    else
    {
        return rtype->fpDisplay(rtype, data);
    }
}
