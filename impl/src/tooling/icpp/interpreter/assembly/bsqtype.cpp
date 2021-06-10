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

bool tupleStructEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    const BSQTupleInfo* ttype1 = dynamic_cast<const BSQTupleInfo*>(data1);
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

bool tupleStructLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    xxxx;
}

bool tupleRefEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    xxxx;
}

bool tupleRefLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    xxxx;
}

bool tupleJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    auto tupinfo = dynamic_cast<const BSQTupleInfo*>(btype);

    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);
    const boost::json::array& jtuple = jv.as_array();

    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            assert(i < jtuple.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            etype->consops.fpJSONParse(etype, jtuple.at(i), &vbuff);

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
            assert(i < jtuple.size());

            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            etype->consops.fpJSONParse(etype, jtuple.at(i), &vbuff);

            BSQType::g_typetable[tupinfo->ttypes[i]]->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), tupinfo->idxoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }

    return true;
}

void tupleGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto tupinfo = dynamic_cast<const BSQTupleInfo*>(btype);

    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);
    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < tupinfo->idxoffsets.size(); ++i)
        {
            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            etype->consops.fpGenerateRandom(etype, rnd, &vbuff);

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
            auto etype = BSQType::g_typetable[tupinfo->ttypes[i]];
            etype->consops.fpGenerateRandom(etype, rnd, &vbuff);
            
            etype->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), tupinfo->idxoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }
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

bool recordJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    auto recinfo = dynamic_cast<const BSQRecordInfo*>(btype);

    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);
    const boost::json::object& jrecord = jv.as_object();

    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertymap[recinfo->properties[i]];

            assert(jrecord.contains(pname));
            etype->consops.fpJSONParse(etype, jrecord.at(pname), &vbuff);

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

            assert(jrecord.contains(pname));
            etype->consops.fpJSONParse(etype, jrecord.at(pname), &vbuff);

            etype->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), recinfo->propertyoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }

    return true;
}

void recordGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto recinfo = dynamic_cast<const BSQRecordInfo*>(btype);

    auto vbuff = BSQ_STACK_SPACE_ALLOC(btype->allocinfo.inlinedatasize);

    if(btype->tkind == BSQTypeKind::Struct)
    {
        for(size_t i = 0; i < recinfo->properties.size(); ++i)
        {
            auto etype = BSQType::g_typetable[recinfo->rtypes[i]];
            auto pname = BSQType::g_propertymap[recinfo->properties[i]];
            etype->consops.fpGenerateRandom(etype, rnd, &vbuff);

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
            etype->consops.fpGenerateRandom(etype, rnd, &vbuff);

            etype->storeValue(SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(&tt), recinfo->propertyoffsets[i]), &vbuff);
        }

        Allocator::GlobalAllocator.popRoot();
    }
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

bool ephemeralJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    auto elinfo = dynamic_cast<const BSQEphemeralListType*>(btype);
    const boost::json::array& jel = jv.as_array();

    for (size_t i = 0; i < elinfo->idxoffsets.size(); ++i)
    {
        assert(i < jel.size());

        auto etype = BSQType::g_typetable[elinfo->etypes[i]];
        etype->consops.fpJSONParse(etype, jel.at(i), SLPTR_INDEX_DATAPTR(sl, elinfo->idxoffsets[i]));
    }

    return true;
}

void ephemeralGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto elinfo = dynamic_cast<const BSQEphemeralListType*>(btype);

    for (size_t i = 0; i < elinfo->idxoffsets.size(); ++i)
    {
        auto etype = BSQType::g_typetable[elinfo->etypes[i]];
        etype->consops.fpGenerateRandom(etype, rnd, SLPTR_INDEX_DATAPTR(sl, elinfo->idxoffsets[i]));
    }
}

std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rtype = SLPTR_LOAD_UNION_INLINE_TYPE(data);
    return rtype->fpDisplay(rtype, SLPTR_LOAD_UNION_INLINE_DATAPTR(data));
}

const BSQType* unionJSONParse_impl_select(const BSQUnionType* utype, const boost::json::value& jv, StorageLocationPtr sl)
{
    std::vector<const BSQType*> opts;
    std::transform(utype->subtypes.cbegin(), utype->subtypes.cend(), std::back_inserter(opts), [](const BSQTypeID tid) {
        return BSQType::g_typetable[tid];
    });

    if(jv.is_object())
    {
        auto rv = jv.as_object();

        //TODO: map option once we have map type
        auto mapopt = opts.cend();
        //std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
        //    return dynamic_cast<const BSQListType*>(opt) != nullptr;
        //});

        auto recordopt = std::find_if(opts.cbegin(), opts.cend(), [&rv](const BSQType* opt) {
            const BSQRecordInfo* ropt = dynamic_cast<const BSQRecordInfo*>(opt);
            if(ropt == nullptr || ropt->properties.size() != rv.size())
            {
                return false;
            }
            else
            {
                return std::all_of(ropt->properties.cbegin(), ropt->properties.cend(), [&rv](const BSQRecordPropertyID prop){
                    return rv.contains(BSQType::g_propertymap[prop]);
                });
            }
        });

        auto oftype = (mapopt != opts.cend()) ? *mapopt : *recordopt;
        oftype->consops.fpJSONParse(oftype, jv, sl);
        return oftype;
    }
    else if(jv.is_array())
    {
        auto listopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQListType*>(opt) != nullptr;
        });

        auto tupleopt = std::find_if(opts.cbegin(), opts.cend(), [](const BSQType* opt) {
            return dynamic_cast<const BSQTupleInfo*>(opt) != nullptr;
        });

        auto oftype = (listopt != opts.cend()) ? *listopt : *tupleopt;
        oftype->consops.fpJSONParse(oftype, jv, sl);
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
                auto okparse = opt->consops.fpJSONParse(opt, jv, sl);
                if(okparse)
                {
                    return opt;
                }
            }
        }

        assert(false);
        return nullptr;
    }
}

bool unionJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    auto utype = dynamic_cast<const BSQUnionType*>(btype);

    auto ptype = unionJSONParse_impl_select(utype, jv, SLPTR_LOAD_UNION_INLINE_DATAPTR(sl));
    if(utype->isInline())
    {
        SLPTR_STORE_UNION_INLINE_TYPE(ptype, sl);
        
    }

    return true;
}

void unionGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto utype = dynamic_cast<const BSQUnionType*>(btype);

    std::uniform_int_distribution<int> distribution(0, utype->subtypes.size());
    auto oftype = BSQType::g_typetable[distribution(rnd)];

    if(utype->isInline())
    {
        SLPTR_STORE_UNION_INLINE_TYPE(oftype, sl);
        oftype->consops.fpGenerateRandom(oftype, rnd, SLPTR_LOAD_UNION_INLINE_DATAPTR(sl));
    }
    else
    {
        oftype->consops.fpGenerateRandom(oftype, rnd, sl);
    }
}
