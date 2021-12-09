//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

const BSQField** BSQField::g_fieldtable = nullptr;

const BSQType** BSQType::g_typetable = nullptr;

const BSQType* BSQType::g_typeNone = new BSQNoneType();
const BSQType* BSQType::g_typeNothing = new BSQNothingType();
const BSQType* BSQType::g_typeBool = new BSQBoolType();
const BSQType* BSQType::g_typeNat = new BSQNatType();
const BSQType* BSQType::g_typeInt = new BSQIntType();
const BSQType* BSQType::g_typeBigNat = new BSQBigNatType();
const BSQType* BSQType::g_typeBigInt = new BSQBigIntType();
const BSQType* BSQType::g_typeFloat = new BSQFloatType();
const BSQType* BSQType::g_typeDecimal = new BSQDecimalType();
const BSQType* BSQType::g_typeRational = new BSQRationalType();

const BSQType* BSQType::g_typeStringKRepr16 = new BSQStringKReprType<16>(BSQ_TYPE_ID_STRINGREPR_K16);
const BSQType* BSQType::g_typeStringKRepr32 = new BSQStringKReprType<32>(BSQ_TYPE_ID_STRINGREPR_K32); 
const BSQType* BSQType::g_typeStringKRepr64 = new BSQStringKReprType<64>(BSQ_TYPE_ID_STRINGREPR_K64);
const BSQType* BSQType::g_typeStringKRepr96 = new BSQStringKReprType<96>(BSQ_TYPE_ID_STRINGREPR_K96);
const BSQType* BSQType::g_typeStringKRepr128 = new BSQStringKReprType<128>(BSQ_TYPE_ID_STRINGREPR_K128);
const std::pair<size_t, const BSQType*> BSQType::g_typeStringKCons[5] = {std::make_pair((size_t)16, BSQType::g_typeStringKRepr16), std::make_pair((size_t)32, BSQType::g_typeStringKRepr32), std::make_pair((size_t)64, BSQType::g_typeStringKRepr64), std::make_pair((size_t)96, BSQType::g_typeStringKRepr96), std::make_pair((size_t)128, BSQType::g_typeStringKRepr128) };

const BSQType* BSQType::g_typeStringTreeRepr = new BSQStringTreeReprType();

const BSQType* BSQType::g_typeString = new BSQStringType();

const BSQType* BSQType::g_typeByteBufferLeaf = new BSQByteBufferLeafType();
const BSQType* BSQType::g_typeByteBufferNode = new BSQByteBufferNodeType();
const BSQType* BSQType::g_typeByteBuffer = new BSQByteBufferType();
const BSQType* BSQType::g_typeISOTime = new BSQISOTimeType();
const BSQType* BSQType::g_typeLogicalTime = new BSQLogicalTimeType();
const BSQType* BSQType::g_typeUUID = new BSQUUIDType();
const BSQType* BSQType::g_typeContentHash = new BSQContentHashType();
const BSQType* BSQType::g_typeRegex = new BSQRegexType();

std::map<BSQRecordPropertyID, std::string> BSQRecordInfo::g_propertynamemap;

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

void BSQRefType::extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const
{
    auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
}

void BSQRefType::injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const
{
    SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
}

void BSQStructType::extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const
{
    auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
    BSQ_MEM_COPY(trgt, udata, this->allocinfo.assigndatasize);
}

void BSQStructType::injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const
{
    SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
    BSQ_MEM_COPY(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src, this->allocinfo.assigndatasize);
}

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQTupleInfo* ttype = dynamic_cast<const BSQTupleInfo*>(btype);
    std::string res = "[";
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

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQRecordInfo* ttype = dynamic_cast<const BSQRecordInfo*>(btype);
    std::string res = "{";
    for(size_t i = 0; i < ttype->properties.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQRecordInfo::g_propertynamemap[ttype->properties[i]] + ":";

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
    std::string res = btype->name + "@{";
    for(size_t i = 0; i < ttype->fields.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQField::g_fieldtable[ttype->fields[i]]->fname + ":";

        auto itype = BSQType::g_typetable[BSQField::g_fieldtable[ttype->fields[i]]->declaredType];
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
