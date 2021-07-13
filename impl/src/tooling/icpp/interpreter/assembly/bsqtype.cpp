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

        auto itype = BSQType::g_typetable[ttype->ttypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "]";

    return res;
}

int tupleStructKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    const BSQTupleInfo* ttype = dynamic_cast<const BSQTupleInfo*>(btype);
    const BSQStructType* tsi = dynamic_cast<const BSQStructType*>(btype);

    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        auto itype = BSQType::g_typetable[ttype->ttypes[i]];
        auto offset = ttype->idxoffsets[i];

        auto cvr = itype->fpkeycmp(itype, tsi->indexStorageLocationOffset(data1, offset), tsi->indexStorageLocationOffset(data2, offset));
        if(cvr != 0)
        {
            return cvr;
        }
    }
    
    return 0;
}

int tupleRefKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    const BSQTupleInfo* ttype = dynamic_cast<const BSQTupleInfo*>(btype);
    const BSQRefType* tsi = dynamic_cast<const BSQRefType*>(btype);

    for(size_t i = 0; i < ttype->idxoffsets.size(); ++i)
    {
        auto itype = BSQType::g_typetable[ttype->ttypes[i]];
        auto offset = ttype->idxoffsets[i];

        auto cvr = itype->fpkeycmp(itype, tsi->indexStorageLocationOffset(data1, offset), tsi->indexStorageLocationOffset(data2, offset));
        if(cvr != 0)
        {
            return cvr;
        }
    }
    
    return 0;
}

bool tupleJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto tupinfo = dynamic_cast<const BSQTupleInfo*>(btype);
    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);

    if(!j.is_array() || tupinfo->ttypes.size() != j.size())
    {
        return false;
    }

    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            assert(i < j.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            bool ok = etype->consops.fpJSONParse(etype, j[i], &vbuff);
            if(!ok)
            {
                return false;
            }

            etype->storeValue(SLPTR_INDEX_DATAPTR(sl, tupinfo->idxoffsets[i]), &vbuff);
        }
    }
    else
    {
        auto tt = Allocator::GlobalAllocator.allocateDynamic(btype);
        Allocator::GlobalAllocator.pushRoot(&tt);

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tt);
        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            assert(i < j.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            bool ok = etype->consops.fpJSONParse(etype, j[i], &vbuff);
            if(!ok)
            {
                return false;
            }

            BSQType::g_typetable[tupinfo->ttypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), tupinfo->idxoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }

    return true;
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

        auto itype = BSQType::g_typetable[ttype->rtypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->propertyoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "}";

    return res;
}

int recordStructKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    const BSQRecordInfo* ttype = dynamic_cast<const BSQRecordInfo*>(btype);
    const BSQStructType* tsi = dynamic_cast<const BSQStructType*>(btype);

    for(size_t i = 0; i < ttype->propertyoffsets.size(); ++i)
    {
        auto itype = BSQType::g_typetable[ttype->rtypes[i]];
        auto offset = ttype->propertyoffsets[i];

        auto cvr = itype->fpkeycmp(itype, tsi->indexStorageLocationOffset(data1, offset), tsi->indexStorageLocationOffset(data2, offset));
        if(cvr != 0)
        {
            return cvr;
        }
    }
    
    return 0;
}

int recordRefKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    const BSQRecordInfo* ttype = dynamic_cast<const BSQRecordInfo*>(btype);
    const BSQRefType* tsi = dynamic_cast<const BSQRefType*>(btype);

    for(size_t i = 0; i < ttype->propertyoffsets.size(); ++i)
    {
        auto itype = BSQType::g_typetable[ttype->rtypes[i]];
        auto offset = ttype->propertyoffsets[i];

        auto cvr = itype->fpkeycmp(itype, tsi->indexStorageLocationOffset(data1, offset), tsi->indexStorageLocationOffset(data2, offset));
        if(cvr != 0)
        {
            return cvr;
        }
    }
    
    return 0;
}

bool recordJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto recinfo = dynamic_cast<const BSQRecordInfo*>(btype);
    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);

    if(!j.is_object() || recinfo->rtypes.size() != j.size())
    {
        return false;
    }

    auto allprops = std::all_of(recinfo->properties.cbegin(), recinfo->properties.cend(), [&j](const BSQRecordPropertyID prop){
                return j.contains(BSQType::g_propertymap[prop]);
            });
    if(!allprops)
    {
        return false;
    }

    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertymap[recinfo->properties[i]];

            bool ok = etype->consops.fpJSONParse(etype, j[pname], &vbuff);
            if(!ok)
            {
                return false;
            }

            etype->storeValue(SLPTR_INDEX_DATAPTR(sl, recinfo->propertyoffsets[i]), &vbuff);
        }
    }
    else
    {
        auto tt = Allocator::GlobalAllocator.allocateDynamic(btype);
        Allocator::GlobalAllocator.pushRoot(&tt);

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tt);
        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertymap[recinfo->properties[i]];

            bool ok = etype->consops.fpJSONParse(etype, j[pname], &vbuff);
            if(!ok)
            {
                return false;
            }

            etype->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), recinfo->propertyoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }

    return true;
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

        auto itype = BSQType::g_typetable[ttype->etypes[i]];
        auto idata = SLPTR_INDEX_DATAPTR(data, ttype->idxoffsets[i]);
        res += itype->fpDisplay(itype, idata);
    }
    res += "|)";

    return res;
}

bool ephemeralJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto elinfo = dynamic_cast<const BSQEphemeralListType*>(btype);
    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);

    if(!j.is_array() || j.size() != elinfo->idxoffsets.size())
    {
        return false;
    }

    for (size_t i = 0; i < elinfo->idxoffsets.size(); ++i)
    {
        auto etype = BSQType::g_typetable[elinfo->etypes[i]];
        bool ok = etype->consops.fpJSONParse(etype, j[i], &vbuff);
        if(!ok)
        {
            return false;
        }

        etype->storeValue(SLPTR_INDEX_DATAPTR(sl, elinfo->idxoffsets[i]), &vbuff);
    }

    return true;
}

std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(data);
    return rtype->fpDisplay(rtype, SLPTR_LOAD_UNION_INLINE_DATAPTR(data));
}

int unionInlineKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto tdiff = SLPTR_LOAD_UNION_INLINE_TYPE(data1)->tid - SLPTR_LOAD_UNION_INLINE_TYPE(data2)->tid;
    if(tdiff != 0)
    {
        return tdiff;
    }
    else
    {
        auto tt = SLPTR_LOAD_UNION_INLINE_TYPE(data1);
        return tt->fpkeycmp(tt, SLPTR_LOAD_UNION_INLINE_DATAPTR(data1), SLPTR_LOAD_UNION_INLINE_DATAPTR(data2));
    }
}

int unionRefKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto tdiff = SLPTR_LOAD_HEAP_TYPE_ANY(data1)->tid - SLPTR_LOAD_HEAP_TYPE_ANY(data2)->tid;
    if(tdiff != 0)
    {
        return tdiff;
    }
    else
    {
        auto tt = SLPTR_LOAD_HEAP_TYPE_ANY(data1);
        return tt->fpkeycmp(tt, data1, data2);
    }
}

const BSQType* unionJSONParse_impl_select(const BSQUnionType* utype, json j, StorageLocationPtr sl)
{
    std::vector<const BSQType*> opts;
    std::transform(utype->subtypes.cbegin(), utype->subtypes.cend(), std::back_inserter(opts), [](const BSQTypeID tid) {
        return BSQType::g_typetable[tid];
    });

    if(j.is_object())
    {
        //TODO: map option once we have map type
        auto mapopt = opts.cend();
        //std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
        //    return dynamic_cast<const BSQListType*>(opt) != nullptr;
        //});

        auto recordopt = std::find_if(opts.cbegin(), opts.cend(), [&j](const BSQType* opt) {
            const BSQRecordInfo* ropt = dynamic_cast<const BSQRecordInfo*>(opt);
            if(ropt == nullptr || ropt->properties.size() != j.size())
            {
                return false;
            }
            else
            {
                return std::all_of(ropt->properties.cbegin(), ropt->properties.cend(), [&j](const BSQRecordPropertyID prop){
                    return j.contains(BSQType::g_propertymap[prop]);
                });
            }
        });

        auto oftype = (mapopt != opts.cend()) ? *mapopt : *recordopt;
        oftype->consops.fpJSONParse(oftype, j, sl);
        return oftype;
    }
    else if(j.is_array())
    {
        auto listopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQListType*>(opt) != nullptr;
        });

        auto tupleopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQTupleInfo*>(opt) != nullptr;
        });

        auto oftype = (listopt != opts.cend()) ? *listopt : *tupleopt;
        oftype->consops.fpJSONParse(oftype, j, sl);
        return oftype;
    }
    else
    {
        for(size_t i = 0; i < opts.size(); ++i)
        {
            auto opt = opts[i];

            auto ismap = false;
            auto islist = dynamic_cast<const BSQListType*>(opt) != nullptr;
            auto isrecord = dynamic_cast<const BSQRecordInfo*>(opt) != nullptr;
            auto istuple = dynamic_cast<const BSQTupleInfo*>(opt) != nullptr;
            if(!ismap && !islist && !isrecord && !istuple)
            {
                auto okparse = opt->consops.fpJSONParse(opt, j, sl);
                if(okparse)
                {
                    return opt;
                }
            }
        }

        return nullptr;
    }
}

bool unionJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto utype = dynamic_cast<const BSQUnionType*>(btype);

    auto rsl = sl;
    if(utype->isInline())
    {
        rsl = SLPTR_LOAD_UNION_INLINE_DATAPTR(sl);
    }

    auto ptype = unionJSONParse_impl_select(utype, j, rsl);
    if(ptype == nullptr)
    {
        return false;
    }

    if(utype->isInline())
    {
        SLPTR_STORE_UNION_INLINE_TYPE(ptype, sl);
    }

    return true;
}
