//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"

const BSQField** BSQField::g_fieldtable = nullptr;

const BSQType* BSQWellKnownType::g_typeNone = CONS_BSQ_NONE_TYPE();
const BSQType* BSQWellKnownType::g_typeNothing = CONS_BSQ_NOTHING_TYPE();
const BSQType* BSQWellKnownType::g_typeBool = CONS_BSQ_BOOL_TYPE();
const BSQType* BSQWellKnownType::g_typeNat = CONS_BSQ_NAT_TYPE(BSQ_TYPE_ID_NAT, "Nat");
const BSQType* BSQWellKnownType::g_typeInt = CONS_BSQ_INT_TYPE(BSQ_TYPE_ID_INT, "Int");
const BSQType* BSQWellKnownType::g_typeBigNat = CONS_BSQ_BIG_NAT_TYPE(BSQ_TYPE_ID_BIGNAT, "BigNat");
const BSQType* BSQWellKnownType::g_typeBigInt = CONS_BSQ_BIG_INT_TYPE(BSQ_TYPE_ID_BIGINT, "BigInt");
const BSQType* BSQWellKnownType::g_typeFloat = CONS_BSQ_FLOAT_TYPE(BSQ_TYPE_ID_FLOAT, "Float");
const BSQType* BSQWellKnownType::g_typeDecimal = CONS_BSQ_DECIMAL_TYPE(BSQ_TYPE_ID_DECIMAL, "Decimal");
const BSQType* BSQWellKnownType::g_typeRational = CONS_BSQ_RATIONAL_TYPE(BSQ_TYPE_ID_RATIONAL, "Rational");

const BSQType* BSQWellKnownType::g_typeStringKRepr16 = new BSQStringKReprType<16>();
const BSQType* BSQWellKnownType::g_typeStringKRepr32 = new BSQStringKReprType<32>(); 
const BSQType* BSQWellKnownType::g_typeStringKRepr64 = new BSQStringKReprType<64>();
const BSQType* BSQWellKnownType::g_typeStringKRepr96 = new BSQStringKReprType<96>();
const BSQType* BSQWellKnownType::g_typeStringKRepr128 = new BSQStringKReprType<128>();
const std::pair<size_t, const BSQType*> BSQWellKnownType::g_typeStringKCons[5] = {std::make_pair((size_t)16, BSQWellKnownType::g_typeStringKRepr16), std::make_pair((size_t)32, BSQWellKnownType::g_typeStringKRepr32), std::make_pair((size_t)64, BSQWellKnownType::g_typeStringKRepr64), std::make_pair((size_t)96, BSQWellKnownType::g_typeStringKRepr96), std::make_pair((size_t)128, BSQWellKnownType::g_typeStringKRepr128) };

const BSQType* BSQWellKnownType::g_typeStringTreeRepr = new BSQStringTreeReprType();

const BSQType* BSQWellKnownType::g_typeString = CONS_BSQ_STRING_TYPE(BSQ_TYPE_ID_STRING, "String");

const BSQType* BSQWellKnownType::g_typeByteBufferLeaf = CONS_BSQ_BYTE_BUFFER_LEAF_TYPE();
const BSQType* BSQWellKnownType::g_typeByteBufferNode = CONS_BSQ_BYTE_BUFFER_NODE_TYPE();
const BSQType* BSQWellKnownType::g_typeByteBuffer = CONS_BSQ_BYTE_BUFFER_TYPE(BSQ_TYPE_ID_BYTEBUFFER, "BytBuffer");
const BSQType* BSQWellKnownType::g_typeDateTime = CONS_BSQ_DATE_TIME_TYPE(BSQ_TYPE_ID_DATETIME, "DateTime");
const BSQType* BSQWellKnownType::g_typeUTCDateTime = CONS_BSQ_UTC_DATE_TIME_TYPE(BSQ_TYPE_ID_UTC_DATETIME, "UTCDateTime");
const BSQType* BSQWellKnownType::g_typeCalendarDate = CONS_BSQ_CALENDAR_DATE_TYPE(BSQ_TYPE_ID_CALENDAR_DATE, "CalendarDate");
const BSQType* BSQWellKnownType::g_typeRelativeTime = CONS_BSQ_RELATIVE_TIME_TYPE(BSQ_TYPE_ID_RELATIVE_TIME, "RelativeTime");
const BSQType* BSQWellKnownType::g_typeTickTime = CONS_BSQ_TICK_TIME_TYPE(BSQ_TYPE_ID_TICKTIME, "TickTime");
const BSQType* BSQWellKnownType::g_typeLogicalTime = CONS_BSQ_LOGICAL_TIME_TYPE(BSQ_TYPE_ID_LOGICALTIME, "LogicalTime");
const BSQType* BSQWellKnownType::g_typeISOTimeStamp = CONS_BSQ_ISO_TIME_STAMP_TYPE(BSQ_TYPE_ID_ISO_TIMESTAMP, "ISOTimeStamp");
const BSQType* BSQWellKnownType::g_typeUUID4 = CONS_BSQ_UUID4_TYPE(BSQ_TYPE_ID_UUID4, "UUID4");
const BSQType* BSQWellKnownType::g_typeUUID7 = CONS_BSQ_UUID7_TYPE(BSQ_TYPE_ID_UUID7, "UUID7");
const BSQType* BSQWellKnownType::g_typeSHAContentHash = CONS_BSQ_SHA_CONTENT_HASH_TYPE(BSQ_TYPE_ID_SHA_CONTENT_HASH, "SHAContentHash");
const BSQType* BSQWellKnownType::g_typeLatLongCoordinate = CONS_BSQ_LAT_LONG_COORDINATE_TYPE(BSQ_TYPE_ID_LAT_LONG_COORDINATE, "LatLongCoordinate");
const BSQType* BSQWellKnownType::g_typeRegex = CONS_BSQ_REGEX_TYPE();

std::map<BSQRecordPropertyID, std::string> BSQRecordInfo::g_propertynamemap;

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    PROCESS_DISPLAY_MODE(btype, mode, data);

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

        res += itype->fpDisplay(itype, idata, mode);
    }
    res += "]";

    return res;
}

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    PROCESS_DISPLAY_MODE(btype, mode, data);

    const BSQRecordInfo* ttype = dynamic_cast<const BSQRecordInfo*>(btype);
    std::string res = "{";
    for(size_t i = 0; i < ttype->properties.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQRecordInfo::g_propertynamemap[ttype->properties[i]] + "=";

        auto itype = BSQType::g_typetable[ttype->rtypes[i]];
        auto idata = btype->indexStorageLocationOffset(data, ttype->propertyoffsets[i]);
        res += itype->fpDisplay(itype, idata, mode);
    }
    res += "}";

    return res;
}

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    PROCESS_DISPLAY_MODE(btype, mode, data);

    const BSQEntityInfo* ttype = dynamic_cast<const BSQEntityInfo*>(btype);
    std::string res = btype->name + "{";
    for(size_t i = 0; i < ttype->fields.size(); ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }

        res += BSQField::g_fieldtable[ttype->fields[i]]->fname + "=";

        auto itype = BSQType::g_typetable[BSQField::g_fieldtable[ttype->fields[i]]->declaredType];
        auto idata = btype->indexStorageLocationOffset(data, ttype->fieldoffsets[i]);
        res += itype->fpDisplay(itype, idata, mode);
    }
    res += "}";

    return res;
}

std::string constructableEntityDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    const BSQType* oftype = BSQType::g_typetable[dynamic_cast<const BSQConstructableEntityInfo*>(btype)->oftype];

    return btype->name + "{" + oftype->fpDisplay(oftype, data, mode) + "}";
}

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
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
        res += itype->fpDisplay(itype, idata, mode);
    }
    res += "|)";

    return res;
}

std::string globalObjectDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return std::string("[GlobalObject]");
}

std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto rtype = dynamic_cast<const BSQUnionType*>(btype)->getVType(data);
    return rtype->fpDisplay(rtype, dynamic_cast<const BSQUnionType*>(btype)->getVData_NoAlloc(data), mode);
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
    auto tdiff = SLPTR_LOAD_HEAP_TYPE(data1)->tid - SLPTR_LOAD_HEAP_TYPE(data2)->tid;
    if(tdiff != 0)
    {
        return tdiff;
    }
    else
    {
        auto tt = SLPTR_LOAD_HEAP_TYPE(data1);
        return tt->fpkeycmp(tt, data1, data2);
    }
}

void coerce(const BSQType* from, const BSQType* into, StorageLocationPtr trgt, StorageLocationPtr src)
{
    if(into->tkind == BSQTypeLayoutKind::UnionUniversal)
    {
        const BSQUnionUniversalType* uutype = dynamic_cast<const BSQUnionUniversalType*>(into);
        if(from->tkind == BSQTypeLayoutKind::UnionUniversal)
        {
            uutype->coerceFromUnionUniversal(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionInline)
        {
            uutype->coerceFromUnionInline(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionRef)
        {
            uutype->coerceFromUnionRef(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else
        {
            uutype->coerceFromAtomic(from, trgt, src);
        }
    }
    else if(into->tkind == BSQTypeLayoutKind::UnionInline)
    {
        const BSQUnionInlineType* iltype = dynamic_cast<const BSQUnionInlineType*>(into);

        if(from->tkind == BSQTypeLayoutKind::UnionUniversal)
        {
            iltype->coerceFromUnionUniversal(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionInline)
        {
            iltype->coerceFromUnionInline(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionRef)
        {
            iltype->coerceFromUnionRef(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else
        {
            iltype->coerceFromAtomic(from, trgt, src);
        }
    }
    else if(into->tkind == BSQTypeLayoutKind::UnionRef)
    {
        const BSQUnionRefType* urtype = dynamic_cast<const BSQUnionRefType*>(into);

        if(from->tkind == BSQTypeLayoutKind::UnionUniversal)
        {
            urtype->coerceFromUnionUniversal(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionInline)
        {
            urtype->coerceFromUnionInline(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionRef)
        {
            urtype->coerceFromUnionRef(dynamic_cast<const BSQUnionType*>(from), trgt, src);
        }
        else
        {
            urtype->coerceFromAtomic(from, trgt, src);
        }
    }
    else
    {
        if(from->tkind == BSQTypeLayoutKind::UnionUniversal)
        {
            dynamic_cast<const BSQUnionUniversalType*>(from)->extractToAtomic(into, trgt, src);
        }
        else if(from->tkind == BSQTypeLayoutKind::UnionInline)
        {
            dynamic_cast<const BSQUnionInlineType*>(from)->extractToAtomic(into, trgt, src);
        }
        else
        {
            BSQ_INTERNAL_ASSERT(from->tkind == BSQTypeLayoutKind::UnionRef);

            dynamic_cast<const BSQUnionRefType*>(from)->extractToAtomic(into, trgt, src);
        }
    }
}

std::pair<const BSQType*, StorageLocationPtr> extractFromUnionVCall(const BSQUnionType* fromlayout, const BSQType* intoflow, StorageLocationPtr trgt, StorageLocationPtr src)
{
    coerce(fromlayout, intoflow, trgt, src);

    if(intoflow->tkind == BSQTypeLayoutKind::UnionInline)
    {
        return std::make_pair(SLPTR_LOAD_UNION_INLINE_TYPE(trgt), SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt));
    }
    else 
    {
        BSQ_INTERNAL_ASSERT(intoflow->tkind == BSQTypeLayoutKind::UnionRef);

        return std::make_pair(SLPTR_LOAD_HEAP_TYPE(trgt), trgt);
    }
}

////
//Primitive value representations

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "none";
}

int entityNoneKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return 0;
}

std::string entityNothingDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "nothing";
}

int entityNothingKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return 0;
}

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBool, data) ? "true" : "false";
}

int entityBoolKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQBool, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQBool, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return !v1 ? -1 : 1;
    }
}

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQNat, data)) + ((btype->name == "Nat") ? "n" : ("_" + btype->name));
}

int entityNatKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQNat, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQNat, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return (v1 < v2) ? -1 : 1;
    }
}

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQInt, data)) + ((btype->name == "Int") ? "i" : ("_" + btype->name));
}

int entityIntKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQInt, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQInt, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return (v1 < v2) ? -1 : 1;
    }
}

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data)) + ((btype->name == "BigNat") ? "N" : ("_" + btype->name));
}

int entityBigNatKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return(v1 < v2) ? -1 : 1;
    }
}

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data)) + ((btype->name == "BigInt") ? "I" : ("_" + btype->name));
}

int entityBigIntKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return (v1 < v2) ? -1 : 1;
    }
}

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    char cbuff[32];
    memset(cbuff, 0, sizeof(cbuff));
    snprintf(cbuff, sizeof(cbuff), "%.9g", SLPTR_LOAD_CONTENTS_AS(BSQFloat, data));

    return std::string(cbuff) + ((btype->name == "Float") ? "f" : ("_" + btype->name));
}

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    char cbuff[32];
    memset(cbuff, 0, sizeof(cbuff));
    snprintf(cbuff, sizeof(cbuff), "%.9g", SLPTR_LOAD_CONTENTS_AS(BSQDecimal, data));

    return std::string(cbuff) + ((btype->name == "Decmial") ? "d" : ("_" + btype->name));
}

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto rval = SLPTR_LOAD_CONTENTS_AS(BSQRational, data);

    return std::to_string(rval.numerator) + "/" + std::to_string(rval.denominator) + ((btype->name == "Rational") ? "R" : ("_" + btype->name));
}

std::string entityStringReprDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQStringForwardIterator iter((BSQString*)data, 0);

    std::string res = "\"";
    while(iter.valid())
    {
        res += (char)iter.get();
        iter.advance();
    }
    res += "\"";

    return res;
}

void* BSQStringKReprTypeAbstract::slice(StorageLocationPtr data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->utf8ByteCount(data)))
    {
        return SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);
    }

    auto kreprtype = BSQStringKReprTypeAbstract::selectKReprForSize(nend - nstart);
    auto res = Allocator::GlobalAllocator.allocateDynamic(kreprtype);

    auto frombuff = BSQStringKReprTypeAbstract::getUTF8Bytes(SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data)) + nstart;

    *res = BSQStringKReprTypeAbstract::getUTF8ByteCount(SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data));
    GC_MEM_COPY(BSQStringKReprTypeAbstract::getUTF8Bytes(res), frombuff, nend - nstart);
    
    return res;
}

void* BSQStringTreeReprType::slice(StorageLocationPtr data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->utf8ByteCount(data)))
    {
        return SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);
    }

    auto s1type = GET_TYPE_META_DATA_AS(BSQStringReprType, ((BSQStringTreeRepr*)data)->srepr1);
    auto s2type = GET_TYPE_META_DATA_AS(BSQStringReprType, ((BSQStringTreeRepr*)data)->srepr2);

    void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 4);
    GC_MEM_ZERO(stck, sizeof(void*) * 4);

    void* res = nullptr;
    auto s1size = s1type->utf8ByteCount(((BSQStringTreeRepr*)data)->srepr1);
    if(nend <= s1size)
    {
        stck[0] = ((BSQStringTreeRepr*)data)->srepr1;
        res = s1type->slice(stck, nstart, nend);
    }
    else if(s1size <= nstart)
    {
        stck[0] = ((BSQStringTreeRepr*)data)->srepr2;
        res = s2type->slice(stck, nstart - s1size, nend - s1size);
    }
    else
    {
        auto s1 = ((BSQStringTreeRepr*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->srepr1;
        stck[0] = s1;
        stck[1] = s1type->slice(stck, nstart, s1type->utf8ByteCount(s1));

        auto s2 = ((BSQStringTreeRepr*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->srepr2;
        stck[2] = s2;
        stck[3] = s2type->slice(stck + 2, 0, nend - s1type->utf8ByteCount(s2));

        res = Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringTreeRepr);
        *((BSQStringTreeRepr*)res) = {stck[1], stck[3], nend - nstart};
    }

    GCStack::popFrame(sizeof(void*) * 4);
    return res;
}

void initializeForwardIterRecProcess(int64_t pos, void* data, BSQStringForwardIterator* iter)
{
    auto stype = GET_TYPE_META_DATA_AS(BSQStringReprType, data);
    if(stype->isKReprNode())
    {
        iter->cbuff = BSQStringKReprTypeAbstract::getUTF8Bytes(data);
        iter->maxpos = (int16_t)BSQStringKReprTypeAbstract::getUTF8ByteCount(data);
        iter->cpos = (uint16_t)pos;
    }
    else
    {
        auto tsdata = static_cast<BSQStringTreeRepr*>(data);

        auto s1size = GET_TYPE_META_DATA_AS(BSQStringReprType, tsdata->srepr1)->utf8ByteCount(tsdata->srepr1);
        if(pos < s1size)
        {
            initializeForwardIterRecProcess(pos, tsdata->srepr1, iter);
        }
        else
        {
            initializeForwardIterRecProcess(pos - s1size, tsdata->srepr2, iter);
        }
    }
}

void BSQStringForwardIterator::initializeIteratorPosition(int64_t curr)
{
    if(curr == this->strmax)
    {
        this->cbuff = nullptr;
        this->maxpos = 0;
        this->cpos = 0;
    }
    else if(IS_INLINE_STRING(this->sstr))
    {
        this->cbuff = BSQInlineString::utf8Bytes(this->sstr->u_inlineString);
        this->maxpos = (int16_t)BSQInlineString::utf8ByteCount(this->sstr->u_inlineString);
        this->cpos = (int16_t)curr;
    }
    else
    {
        initializeForwardIterRecProcess(curr, this->sstr->u_data, this);
    }
}

void BSQStringForwardIterator::increment_utf8byte()
{
    this->curr++;
    this->cpos++;
    
    if(this->cpos == this->maxpos)
    {
        this->initializeIteratorPosition(this->curr);
    }
}

void initializeReverseIterRecProcess(int64_t pos, void* data, BSQStringReverseIterator* iter)
{
    auto stype = GET_TYPE_META_DATA_AS(BSQStringReprType, data);
    if(stype->isKReprNode())
    {
        iter->cbuff = BSQStringKReprTypeAbstract::getUTF8Bytes(data);
        iter->cpos = (int16_t)pos;
    }
    else
    {
        auto tsdata = static_cast<BSQStringTreeRepr*>(data);

        auto s1size = GET_TYPE_META_DATA_AS(BSQStringReprType, tsdata->srepr1)->utf8ByteCount(tsdata->srepr1);
        if(pos < s1size)
        {
            initializeReverseIterRecProcess(pos, tsdata->srepr1, iter);
        }
        else
        {
            initializeReverseIterRecProcess(pos - s1size, tsdata->srepr2, iter);
        }
    }
}

void BSQStringReverseIterator::initializeIteratorPosition(int64_t curr)
{
    if(curr == -1)
    {
        this->cbuff = nullptr;
        this->cpos = -1;
    }
    else if(IS_INLINE_STRING(this->sstr))
    {
        this->cbuff = BSQInlineString::utf8Bytes(this->sstr->u_inlineString);
        this->cpos = (int16_t)curr;
    }
    else
    {
        initializeReverseIterRecProcess(curr, this->sstr->u_data, this);
    }
}

void BSQStringReverseIterator::increment_utf8byte()
{
    this->curr--;
    this->cpos--;
    
    if(this->cpos == -1)
    {
        this->initializeIteratorPosition(this->curr);
    }
}

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQString str = SLPTR_LOAD_CONTENTS_AS(BSQString, data);

    std::string res;
    res.reserve((size_t)BSQStringImplType::utf8ByteCount(str));

    BSQStringForwardIterator iter(&str, 0);
    while(iter.valid())
    {
        res.push_back((char)iter.get());
        iter.advance();
    }

    return "\"" + res + "\"";
}

int entityStringKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringImplType::keycmp(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
}

uint8_t* BSQStringImplType::boxInlineString(BSQInlineString istr)
{
    auto res = (uint8_t*)Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringKRepr16);
    *res = (uint8_t)BSQInlineString::utf8ByteCount(istr);
    BSQ_MEM_COPY(res + 1, BSQInlineString::utf8Bytes(istr), *res);

    return res;
}

int BSQStringImplType::keycmp(BSQString v1, BSQString v2)
{
    if(BSQStringImplType::empty(v1) & BSQStringImplType::empty(v2))
    {
        return 0;
    }
    else if(BSQStringImplType::empty(v1))
    {
        return -1;
    }
    else if(BSQStringImplType::empty(v2))
    {
        return 1;
    }
    else if(IS_INLINE_STRING(&v1) && IS_INLINE_STRING(&v2))
    {
        return memcmp(BSQInlineString::utf8Bytes(v1.u_inlineString), BSQInlineString::utf8Bytes(v2.u_inlineString), 16);
    }
    else
    {
        auto bdiff = BSQStringImplType::utf8ByteCount(v1) - BSQStringImplType::utf8ByteCount(v2);
        if(bdiff != 0)
        {
            return bdiff < 0 ? -1 : 1;
        }   
        else
        {
            //
            //TODO: we want to add some order magic where we intern longer concat strings in sorted tree and can then just compare pointer equality or parent order instead of looking at full data 
            //

            BSQStringForwardIterator iter1(&v1, 0);
            BSQStringForwardIterator iter2(&v2, 0);

            while(iter1.valid() & iter2.valid())
            {
                auto diff = iter1.get_byte() - iter2.get_byte();
                if(diff != 0)
                {
                    return diff;
                }

                iter1.advance_byte();
                iter2.advance_byte();
            }

            return 0;
        }
    }
}

BSQString BSQStringImplType::concat2(StorageLocationPtr s1, StorageLocationPtr s2)
{
    BSQString res;
    BSQString* stck = (BSQString*)GCStack::allocFrame(sizeof(BSQString) * 2);
    
    stck[0] = SLPTR_LOAD_CONTENTS_AS(BSQString, s1);
    stck[1] = SLPTR_LOAD_CONTENTS_AS(BSQString, s2);
    
    if(BSQStringImplType::empty(stck[0]) & BSQStringImplType::empty(stck[1]))
    {
        res = g_emptyString;
    }
    else if(BSQStringImplType::empty(stck[0]))
    {
        res = stck[1];
    }
    else if(BSQStringImplType::empty(stck[1]))
    {
        res = stck[0];
    }
    else
    {
        auto len1 = BSQStringImplType::utf8ByteCount(stck[0]);
        auto len2 = BSQStringImplType::utf8ByteCount(stck[1]);

        BSQString res = g_emptyString;
        if(IS_INLINE_STRING(&stck[0]) & IS_INLINE_STRING(&stck[1]))
        {
            if(len1 + len2 < 16)
            {
                BSQInlineString::utf8ByteCount_Initialize(res.u_inlineString, (uint64_t)(len1 + len2));
                GC_MEM_COPY(BSQInlineString::utf8Bytes(res.u_inlineString), BSQInlineString::utf8Bytes(stck[0].u_inlineString), (size_t)len1);
                GC_MEM_COPY(BSQInlineString::utf8Bytes(res.u_inlineString) + len1, BSQInlineString::utf8Bytes(stck[1].u_inlineString), (size_t)len2);
            }
            else
            {
                assert(len1 + len2 <= 30);

                auto crepr = (uint8_t*)Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                *crepr = (uint8_t)(len1 + len2);
                BSQ_MEM_COPY(curr, BSQInlineString::utf8Bytes(stck[0].u_inlineString), len1);
                BSQ_MEM_COPY(curr + len1, BSQInlineString::utf8Bytes(stck[1].u_inlineString), len2);

                res.u_data = crepr;
            }
        }
        else
        {
            if(len1 + len2 < 32)
            {
                auto crepr = (uint8_t*)Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                *crepr = (uint8_t)(len1 + len2);

                BSQStringForwardIterator iter1(&stck[0], 0);
                while(iter1.valid())
                {
                    *curr = iter1.get_byte();
                    curr++;
                    iter1.advance_byte();
                }

                BSQStringForwardIterator iter2(&stck[1], 0);
                while(iter2.valid())
                {
                    *curr = iter2.get_byte();
                    curr++;
                    iter2.advance_byte();
                }

                res.u_data = crepr;
            }
            else
            {
                //
                //TODO: want to rebalance here later
                //

                auto crepr = (BSQStringTreeRepr*)Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringTreeRepr);
                crepr->size = (uint64_t)(len1 + len2);
                crepr->srepr1 = IS_INLINE_STRING(s1) ? BSQStringImplType::boxInlineString(stck[0].u_inlineString) : stck[0].u_data;
                crepr->srepr2 = IS_INLINE_STRING(s2) ? BSQStringImplType::boxInlineString(stck[1].u_inlineString) : stck[1].u_data;
                
                res.u_data = crepr;
            }
        }
    }

    GCStack::popFrame(sizeof(BSQString) * 2);
    return res;
}

BSQString BSQStringImplType::slice(StorageLocationPtr str, int64_t startpos, int64_t endpos)
{
    BSQString res;
    BSQString* stck = (BSQString*)GCStack::allocFrame(sizeof(BSQString));
    
    stck[0] = SLPTR_LOAD_CONTENTS_AS(BSQString, str);

    if(startpos >= endpos)
    {
        return g_emptyString;
    }
    else
    {
        int64_t dist = endpos - startpos;

        BSQString res = {0};
        if(IS_INLINE_STRING(&stck[0]))
        {
            res.u_inlineString = BSQInlineString::create(BSQInlineString::utf8Bytes(stck[0].u_inlineString) + startpos, (uint64_t)dist);
        }
        else
        {
            if(dist < 16)
            {
                BSQInlineString::utf8ByteCount_Initialize(res.u_inlineString, (uint64_t)dist);
                uint8_t* curr = BSQInlineString::utf8Bytes(res.u_inlineString);

                BSQStringForwardIterator iter(&stck[0], startpos);
                while(startpos < endpos)
                {
                    *curr = iter.get_byte();
                    iter.advance_byte();
                }
            }
            else if(dist < 32)
            {
                res.u_data = Allocator::GlobalAllocator.allocateDynamic(BSQWellKnownType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(res.u_data);
               
                BSQStringForwardIterator iter(&stck[0], startpos);
                while(startpos < endpos)
                {
                    *curr = iter.get_byte();
                    iter.advance_byte();
                }
            }
            else
            {
                //
                //TODO: want to rebalance here later
                //

                auto reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, stck[0].u_data);
                res.u_data = reprtype->slice(stck[0].u_data, startpos, endpos);
            }
        }

        GCStack::popFrame(sizeof(BSQString));
        return res;
    }
}

std::string entityByteBufferLeafDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "[ByteBufferEntry]"; 
}

std::string entityByteBufferNodeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "[ByteBufferNode]";   
}

std::string entityByteBufferDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQByteBuffer* bbuff = SLPTR_LOAD_CONTENTS_AS(BSQByteBuffer*, data);
    std::string bstr;
    bstr.reserve(bbuff->bytecount * 5);

    bstr += "[";
    BSQByteBufferNode* curr = bbuff->bytes;
    bool first = true;
    while(curr != nullptr)
    {
        for(size_t i = 0; i < curr->bytecount; ++i)
        {
            if(!first) 
            {
                bstr += ", ";
            }
            first = false;
            bstr += std::to_string(curr->bytes->bytes[i]);
        }

        curr = curr->next;
    }
    bstr += "]";

    return bstr;
}

std::string emitDateTimeRaw_v(uint16_t y, uint8_t m, uint8_t d, uint8_t hh, uint8_t mm)
{
    struct tm dt = {0};
    dt.tm_year = y;
    dt.tm_mon = m;
    dt.tm_mday = d;
    dt.tm_hour = hh;
    dt.tm_min = mm;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%dT%H:%M", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

std::string entityDateTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQDateTime t = SLPTR_LOAD_CONTENTS_AS(BSQDateTime, data);

    auto tzstr = std::string(t.tzdata);
    if(tzstr == "UTC")
    {
        auto tstr = emitDateTimeRaw_v(t.year, t.month, t.day, t.hour, t.min) + "Z"; 
        return tstr + ((btype->name == "DateTime") ? "" : ("_" + btype->name));
    }
    else
    {
        auto tstr = emitDateTimeRaw_v(t.year, t.month, t.day, t.hour, t.min) + " " + tzstr;

        return tstr + ((btype->name == "DateTime") ? "" : ("_" + btype->name));
    }
}

std::string entityUTCDateTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQUTCDateTime t = SLPTR_LOAD_CONTENTS_AS(BSQUTCDateTime, data);

    auto tstr = emitDateTimeRaw_v(t.year, t.month, t.day, t.hour, t.min) + "Z"; 
    return tstr + ((btype->name == "UTCDateTime") ? "" : ("_" + btype->name));
}

int entityUTCDateTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    BSQUTCDateTime t1 = SLPTR_LOAD_CONTENTS_AS(BSQUTCDateTime, data1);
    BSQUTCDateTime t2 = SLPTR_LOAD_CONTENTS_AS(BSQUTCDateTime, data2);

    if(t1.year != t2.year)
    {
        return (t1.year < t2.year) ? -1 : 1;
    }
    else
    {
        if(t1.month != t2.month)
        {
            return (t1.month < t2.month) ? -1 : 1;
        }
        else
        {
            if(t1.day != t2.day)
            {
                return (t1.day < t2.day) ? -1 : 1;
            }
            else
            {
                if(t1.hour != t2.hour)
                {
                    return (t1.hour < t2.hour) ? -1 : 1;
                }
                else
                {
                    if(t1.min != t2.min)
                    {
                        return (t1.min < t2.min) ? -1 : 1;
                    }
                    else
                    {
                        return 0;
                    }
                }
            }
        }
    }
}

std::string entityCalendarDateDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQCalendarDate d = SLPTR_LOAD_CONTENTS_AS(BSQCalendarDate, data);

    struct tm dt = {0};
    dt.tm_year = d.year;
    dt.tm_mon = d.month;
    dt.tm_mday = d.day;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%d", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

int entityCalendarDateKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    BSQCalendarDate t1 = SLPTR_LOAD_CONTENTS_AS(BSQCalendarDate, data1);
    BSQCalendarDate t2 = SLPTR_LOAD_CONTENTS_AS(BSQCalendarDate, data2);

    if(t1.year != t2.year)
    {
        return (t1.year < t2.year) ? -1 : 1;
    }
    else
    {
        if(t1.month != t2.month)
        {
            return (t1.month < t2.month) ? -1 : 1;
        }
        else
        {
            if(t1.day != t2.day)
            {
                return (t1.day < t2.day) ? -1 : 1;
            }
            else
            {
                return 0;
            }
        }
    }
}

std::string entityRelativeTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQRelativeTime rt = SLPTR_LOAD_CONTENTS_AS(BSQRelativeTime, data);

    struct tm dt = {0};
    dt.tm_hour = rt.hour;
    dt.tm_min = rt.min;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%H:%M", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

int entityRelativeTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    BSQRelativeTime t1 = SLPTR_LOAD_CONTENTS_AS(BSQRelativeTime, data1);
    BSQRelativeTime t2 = SLPTR_LOAD_CONTENTS_AS(BSQRelativeTime, data2);

    if(t1.hour != t2.hour)
    {
        return (t1.hour < t2.hour) ? -1 : 1;
    }
    else
    {
        if(t1.min != t2.min)
        {
            return (t1.min < t2.min) ? -1 : 1;
        }
        else
        {
            return 0;
        }
    }
}

std::string entityTickTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "T" + std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQTickTime, data)) + ((btype->name == "TickTime") ? "ns" : ("_" + btype->name));
}

int entityTickTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    BSQTickTime t1 = SLPTR_LOAD_CONTENTS_AS(BSQTickTime, data1);
    BSQTickTime t2 = SLPTR_LOAD_CONTENTS_AS(BSQTickTime, data2);

    if(t1 == t2)
    {
        return 0;
    }
    else
    {
        return (t1 < t2) ? -1 : 1;
    }
}

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "L" + std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data)) + ((btype->name == "LogicalTime") ? "" : ("_" + btype->name));
}

int entityLogicalTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data2);
    if(v1 == v2)
    {
        return 0;
    }
    else
    {
        return (v1 < v2) ? -1 : 1;
    }
}

std::string entityISOTimeStampDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    BSQISOTimeStamp t = SLPTR_LOAD_CONTENTS_AS(BSQISOTimeStamp, data);

    struct tm dt = {0};
    dt.tm_year = t.year;
    dt.tm_mon = t.month;
    dt.tm_mday = t.day;
    dt.tm_hour = t.hour;
    dt.tm_min = t.min;
    dt.tm_sec = t.seconds;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%dT%H:%M:%S", &dt);
    std::string isobase(sstrt, sstrt + dtlen);

    char ssmillis[8] = {0};
    size_t millislen = sprintf(ssmillis, ".%03iZ", t.millis);
    std::string millis(ssmillis, ssmillis + millislen);

    return isobase + millis + ((btype->name == "ISOTimeStamp") ? "" : ("_" + btype->name));
}

int entityISOTimeStampKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    BSQISOTimeStamp t1 = SLPTR_LOAD_CONTENTS_AS(BSQISOTimeStamp, data1);
    BSQISOTimeStamp t2 = SLPTR_LOAD_CONTENTS_AS(BSQISOTimeStamp, data2);

    if(t1.year != t2.year)
    {
        return (t1.year < t2.year) ? -1 : 1;
    }
    else
    {
        if(t1.month != t2.month)
        {
            return (t1.month < t2.month) ? -1 : 1;
        }
        else
        {
            if(t1.day != t2.day)
            {
                return (t1.day < t2.day) ? -1 : 1;
            }
            else
            {
                if(t1.hour != t2.hour)
                {
                    return (t1.hour < t2.hour) ? -1 : 1;
                }
                else
                {
                    if(t1.min != t2.min)
                    {
                        return (t1.min < t2.min) ? -1 : 1;
                    }
                    else
                    {
                        if(t1.seconds != t2.seconds)
                        {
                            return (t1.seconds < t2.seconds) ? -1 : 1;
                        }
                        else
                        {
                            if(t1.millis != t2.millis)
                            {
                                return (t1.millis < t2.millis) ? -1 : 1;
                            }
                            else
                            {
                                return 0;
                            }
                        }
                    }
                }
            }
        }
    }
}

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto uuid = SLPTR_LOAD_CONTENTS_AS(BSQUUID, data);

    unsigned int bb4 = *reinterpret_cast<const uint32_t*>(uuid.bytes);
    unsigned int bb2_1 = *reinterpret_cast<const uint16_t*>(uuid.bytes + 4);
    unsigned int bb2_2 = *reinterpret_cast<const uint16_t*>(uuid.bytes + 6);
    unsigned int bb2_3 = *reinterpret_cast<const uint16_t*>(uuid.bytes + 8);
    unsigned int bb6 = *reinterpret_cast<const uint64_t*>(uuid.bytes + 10) & 0xFFFFFFFFFFFF;
    
    char sstrt[64] = {0};
    sprintf(sstrt, "%06x-%04x-%04x-%04x-%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + 64);

    return res;
}

int entityUUIDKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = SLPTR_LOAD_CONTENTS_AS(BSQUUID, data1);
    auto v2 = SLPTR_LOAD_CONTENTS_AS(BSQUUID, data2);

    auto cmp = std::mismatch(v1.bytes, v1.bytes + sizeof(v1.bytes), v2.bytes);
    if(cmp.first == v1.bytes + sizeof(v1.bytes))
    {
        return 0;
    }
    else
    {
        return (*(cmp.first) < *(cmp.second)) ? -1 : 1;
    }
}

std::string entitySHAContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto v1 = (BSQSHAContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);

    std::string rr = "0x";
    for(auto iter = v1->bytes; iter < v1->bytes + sizeof(v1->bytes); ++iter)
    {
        char sstrt[8] = {0};
        sprintf(sstrt, "%02x", *iter);

        std::string ss(sstrt, sstrt + 2);
        rr += ss;
    }

    return rr;
}

int entitySHAContentHashKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = (BSQSHAContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1);
    auto v2 = (BSQSHAContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2);

    auto cmp = std::mismatch(v1->bytes, v1->bytes + sizeof(v1->bytes), v2->bytes);
    if(cmp.first == v1->bytes + sizeof(v1->bytes))
    {
        return 0;
    }
    else
    {
        return (*(cmp.first) < *(cmp.second)) ? -1 : 1;
    }
}

std::string entityLatLongCoordinateDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto v = SLPTR_LOAD_CONTENTS_AS(BSQLatLongCoordinate, data);

    return std::string("(") + std::to_string(v.latitude) + std::string(", ") + std::to_string(v.longitude) + std::string(")");
}

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return ((BSQRegex*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->restr;
}

std::string entityEnumDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto val = SLPTR_LOAD_CONTENTS_AS(uint64_t, data);
    return static_cast<const BSQEnumType*>(btype)->enumnames[val];
}

