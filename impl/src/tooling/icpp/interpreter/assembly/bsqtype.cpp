//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

const BSQType** BSQType::g_typetable = nullptr;
std::map<BSQRecordPropertyID, std::string> BSQType::g_propertymap;
std::map<BSQFieldID, std::string> BSQType::g_fieldmap;

void** gcDecOperator_registerImpl(const BSQType* btype, void** data)
{
    return data + (btype->allocinfo.inlinedatasize / sizeof(void*));
}

void** gcDecOperator_maskImpl(const BSQType* btype, void** data)
{
    return Allocator::gcDecSlotsWithMask(data, btype->allocinfo.inlinedmask);
}

void** gcDecOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementString(data);
    return data + 1;
}

void** gcDecOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcDecrementBigNum(data);
    return data + 1;
}

void** gcClearOperator_registerImpl(const BSQType* btype, void** data)
{
    return data + (btype->allocinfo.inlinedatasize / sizeof(void*));
}

void** gcClearOperator_maskImpl(const BSQType* btype, void** data)
{
    return Allocator::gcClearMarkSlotsWithMask(data, btype->allocinfo.inlinedmask);
}

void** gcClearOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkString(data);
    return data + 1;
}

void** gcClearOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcClearMarkBigNum(data);
    return data + 1;
}

void** gcProcessRootOperator_registerImpl(const BSQType* btype, void** data)
{
    return data + (btype->allocinfo.inlinedatasize / sizeof(void*));
}

void** gcProcessRootOperator_maskImpl(const BSQType* btype, void** data)
{
    return Allocator::gcProcessSlotsWithMask<true>(data, btype->allocinfo.inlinedmask);
}

void** gcProcessRootOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<true>(data);
    return data + 1;
}

void** gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<true>(data);
    return data + 1;
}

void** gcProcessHeapOperator_registerImpl(const BSQType* btype, void** data)
{
    return data + (btype->allocinfo.inlinedatasize / sizeof(void*));
}

void** gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data)
{
    return Allocator::gcProcessSlotsWithMask<false>(data, btype->allocinfo.inlinedmask);
}

void** gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithString<false>(data);
    return data + 1;
}

void** gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data)
{
    Allocator::gcProcessSlotWithBigNum<false>(data);
    return data + 1;
}

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQTupleInfo* ttype = dynamic_cast<const BSQTupleInfo*>(btype);
    bool isstruct = btype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#[" : "@[";
    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        xxxx;

        auto itype = BSQType::g_typetable[ttype->ttypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "]";

    return res;
}

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQRecordInfo* ttype = dynamic_cast<const BSQRecordInfo*>(btype);
    bool isstruct = btype->tkind == BSQTypeKind::Struct;
    std::string res = isstruct ? "#{" : "@{";
    for(size_t i = 0; i < ttype->properties.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQType::g_propertymap[ttype->properties[i]] + ":";

        xxxx;

        auto itype = BSQType::g_typetable[ttype->rtypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->propertyoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQEntityInfo* ttype = dynamic_cast<const BSQEntityInfo*>(btype);
    bool isstruct = btype->tkind == BSQTypeKind::Struct;
    std::string res = btype->name + (isstruct ? "#{" : "@{");
    for(size_t i = 0; i < ttype->fields.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQType::g_fieldmap[ttype->fields[i]] + ":";

        xxxx;

        auto itype = BSQType::g_typetable[ttype->ftypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->fieldoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQEphemeralListType* ttype = dynamic_cast<const BSQEphemeralListType*>(btype);
    std::string res = "@(|";
    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        xxxx;

        auto itype = BSQType::g_typetable[ttype->etypes[i]];
        auto idata = SLPTR_INDEX_DATAPTR(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "|)";

    return res;
}

std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(data);
    return rtype->fpDisplay(rtype, SLPTR_LOAD_UNION_INLINE_DATAPTR(data));
}
