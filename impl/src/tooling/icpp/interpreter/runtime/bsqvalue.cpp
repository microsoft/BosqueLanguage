//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "environment.h"

const BSQType* BSQType::g_typeNone = new BSQNoneType();
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
const BSQType* BSQType::g_typeStringKRepr256 = new BSQStringKReprType<256>(BSQ_TYPE_ID_STRINGREPR_K256);
const std::pair<size_t, const BSQType*> BSQType::g_typeStringKCons[6] = {std::make_pair((size_t)16, BSQType::g_typeStringKRepr16), std::make_pair((size_t)32, BSQType::g_typeStringKRepr32), std::make_pair((size_t)64, BSQType::g_typeStringKRepr64), std::make_pair((size_t)96, BSQType::g_typeStringKRepr96), std::make_pair((size_t)128, BSQType::g_typeStringKRepr128), std::make_pair((size_t)256, BSQType::g_typeStringKRepr256) };

const BSQType* BSQType::g_typeStringConcatRepr = new BSQStringConcatReprType();
const BSQType* BSQType::g_typeStringSliceRepr = new BSQStringSliceReprType();

const BSQType* BSQType::g_typeString = new BSQStringType();
const BSQType* BSQType::g_typeStringPos = new BSQStringIteratorType();
const BSQType* BSQType::g_typeByteBuffer = new BSQByteBufferType();
const BSQType* BSQType::g_typeISOTime = new BSQISOTimeType();
const BSQType* BSQType::g_typeLogicalTime = new BSQLogicalTimeType();
const BSQType* BSQType::g_typeUUID = new BSQUUIDType();
const BSQType* BSQType::g_typeContentHash = new BSQContentHashType();
const BSQType* BSQType::g_typeRegex = new BSQRegexType();

static std::regex re_numberino_n("^[+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_i("^[-+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_f("^[-+]?(0|[1-9][0-9]*)|([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$");

std::optional<uint64_t> parseToUnsignedNumber(json j)
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = j.get<uint64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_n))
            {
                try
                {
                    nval = std::stoull(sstr);
                }
                catch(...)
                {
                    ;
                }
            }
        }
    }

    return nval;
}

std::optional<int64_t> parseToSignedNumber(json j)
{
    std::optional<int64_t> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = j.get<int64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_i))
            {
                try
                {
                    nval = std::stoll(sstr);
                }
                catch(...)
                {
                    ;
                }
            }
        }
    }

    return nval;
}

std::optional<std::string> parseToBigUnsignedNumber(json j)
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_n))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> parseToBigSignedNumber(json j)
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_i))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> parseToRealNumber(json j)
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number() || j.is_string())
    { 
        if(j.is_number())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_f))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> parseToDecimalNumber(json j)
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number() || j.is_string())
    { 
        if(j.is_number())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_f))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "none";
}

int entityNoneKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return 0;
}

bool entityNoneJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_null())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNoneType*>(BSQType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
        return true;
    }
}

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data)
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

bool entityBoolJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_boolean())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQBoolType*>(BSQType::g_typeBool)->storeValueDirect(sl, j.get<bool>() ? BSQTRUE : BSQFALSE);
        return true;
    }
}

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQNat, data)) + "n";
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

bool entityNatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto uval = parseToUnsignedNumber(j);
    if(!uval.has_value())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNatType*>(BSQType::g_typeNat)->storeValueDirect(sl, uval.value());
        return true;
    }
}

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQInt, data)) + "i";
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

bool entityIntJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto ival = parseToSignedNumber(j);
    if(!ival.has_value())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQIntType*>(BSQType::g_typeInt)->storeValueDirect(sl, ival.value());
        return true;
    }
}

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data)) + "N";
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

bool entityBigNatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto bnval = parseToBigUnsignedNumber(j);
    if(!bnval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, std::stoull(bnval.value()));
    return true;
}

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data)) + "I";
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

bool entityBigIntJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto bival = parseToBigUnsignedNumber(j);
    if(!bival.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, std::stoll(bival.value()));
    return true;
}

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQFloat, data)) + "f";
}

bool entityFloatJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto fval = parseToRealNumber(j);
    if(!fval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQFloatType*>(BSQType::g_typeFloat)->storeValueDirect(sl, std::stod(fval.value()));
    return true;
}

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, data)) + "d";
}

bool entityDecimalJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    auto dval = parseToDecimalNumber(j);
    if(!dval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQDecimalType*>(BSQType::g_typeDecimal)->storeValueDirect(sl, std::stod(dval.value()));
    return true;
}

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rval = SLPTR_LOAD_CONTENTS_AS(BSQRational, data);

    auto numtype = dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt);
    auto denomtype = dynamic_cast<const BSQNatType*>(BSQType::g_typeNat);

    return numtype->fpDisplay(numtype, &rval.numerator) + "/" + denomtype->fpDisplay(denomtype, &rval.denominator) + "R";
}

bool entityRationalJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_array() || j.size() != 2)
    {
        return false;
    }

    auto numtype = dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt);
    auto denomtype = dynamic_cast<const BSQNatType*>(BSQType::g_typeNat);

    BSQRational rr;
    auto oknum = numtype->consops.fpJSONParse(numtype, j[0], &rr.numerator);
    auto okdenom = denomtype->consops.fpJSONParse(denomtype, j[1], &rr.denominator);

    if(!oknum || !okdenom)
    {
        return false;
    }

    dynamic_cast<const BSQRationalType*>(BSQType::g_typeRational)->storeValueDirect(sl, rr);
    return true;
}

std::string entityStringReprDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQStringIterator iter;
    BSQStringType::initializeIteratorBegin(&iter, SLPTR_LOAD_CONTENTS_AS(BSQString, data));

    std::string res = "\"";
    while(iteratorIsValid(&iter))
    {
        res += (char)iteratorGetCodePoint(&iter);
        incrementStringIterator_codePoint(&iter);
    }
    res += "\"";

    return res;
}

void BSQStringKReprTypeAbstract::initializeIterPositionWSlice(BSQStringIterator* iter, void* data, int64_t minpos, int64_t maxpos, int64_t pos)
{
    iter->cbuff = data;

    iter->minpos = (int16_t)minpos;
    iter->maxpos = (int16_t)maxpos;
    iter->cpos = (int16_t)pos;
}

void BSQStringKReprTypeAbstract::initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const
{
    iter->cbuff = data;

    iter->minpos = 0;
    iter->maxpos = (int16_t)BSQStringKReprTypeAbstract::getUTF8ByteCount(data);
    iter->cpos = (int16_t)pos;
}

void* BSQStringKReprTypeAbstract::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->utf8ByteCount(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);

    auto res = Allocator::GlobalAllocator.allocateDynamic(BSQType::g_typeStringSliceRepr);

    ((BSQStringSliceRepr*)res)->srepr = data;
    ((BSQStringSliceRepr*)res)->start = nstart;
    ((BSQStringSliceRepr*)res)->end = nend;

    Allocator::GlobalAllocator.popRoot();
    return data;
}

void BSQStringSliceReprType::initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const
{
    auto slicerepr = (BSQStringSliceRepr*)data;
    BSQStringKReprTypeAbstract::initializeIterPositionWSlice(iter, slicerepr->srepr, (int64_t)slicerepr->start, (int64_t)slicerepr->end, pos + (int64_t)slicerepr->start);
}

void* BSQStringSliceReprType::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->utf8ByteCount(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);

    auto res = Allocator::GlobalAllocator.allocateDynamic(BSQType::g_typeStringSliceRepr);

    ((BSQStringSliceRepr*)res)->srepr = ((BSQStringSliceRepr*)data)->srepr;
    ((BSQStringSliceRepr*)res)->start = ((BSQStringSliceRepr*)data)->start + nstart;
    ((BSQStringSliceRepr*)res)->end = ((BSQStringSliceRepr*)data)->end - nend;

    Allocator::GlobalAllocator.popRoot();
    return res;
}


void BSQStringConcatReprType::initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const
{
    auto concatrepr = (BSQStringConcatRepr*)data;
    auto s1size = (int64_t)concatrepr->size;
    if(pos < s1size)
    {
        auto s1type = GET_TYPE_META_DATA_AS(BSQStringReprType, concatrepr->srepr1);
        s1type->initializeIterPosition(iter, concatrepr->srepr1, pos);
    }
    else
    {
        auto s2type = GET_TYPE_META_DATA_AS(BSQStringReprType, concatrepr->srepr2);
        s2type->initializeIterPosition(iter, concatrepr->srepr2, pos - s1size);
    }
}

void* BSQStringConcatReprType::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->utf8ByteCount(data)))
    {
        return data;
    }

    auto s1type = GET_TYPE_META_DATA_AS(BSQStringReprType, ((BSQStringConcatRepr*)data)->srepr1);
    auto s2type = GET_TYPE_META_DATA_AS(BSQStringReprType, ((BSQStringConcatRepr*)data)->srepr2);

    Allocator::GlobalAllocator.pushRoot(&data);
        
    void* res = nullptr;
    auto s1size = s1type->utf8ByteCount(((BSQStringConcatRepr*)data)->srepr1);
    if(nend <= s1size)
    {
        res = s1type->slice(((BSQStringConcatRepr*)data)->srepr1, nstart, nend);
    }
    else if(s1size <= nstart)
    {
        res = s2type->slice(((BSQStringConcatRepr*)data)->srepr2, nstart - s1size, nend - s1size);
    }
    else
    {
        res = Allocator::GlobalAllocator.allocateDynamic(BSQType::g_typeStringConcatRepr);
        Allocator::GlobalAllocator.pushRoot(&res);

        ((BSQStringConcatRepr*)res)->srepr1 = s1type->slice(((BSQStringConcatRepr*)data)->srepr1, nstart, s1type->utf8ByteCount(((BSQStringConcatRepr*)data)->srepr1));
        ((BSQStringConcatRepr*)res)->srepr2 = s2type->slice(((BSQStringConcatRepr*)data)->srepr2, 0, nend - s1type->utf8ByteCount(((BSQStringConcatRepr*)data)->srepr1));
        ((BSQStringConcatRepr*)res)->size = nend - nstart;

        Allocator::GlobalAllocator.popRoot(); 
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}

std::string entityStringBSQStringIteratorDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[String Iterator]";
}

bool iteratorIsValid(const BSQStringIterator* iter)
{
    return iter->statusflag != g_invalidIterFlag;
}

bool iteratorLess(const BSQStringIterator* iter1, const BSQStringIterator* iter2)
{
    return iter1->strpos < iter2->strpos;
}

bool iteratorEqual(const BSQStringIterator* iter1, const BSQStringIterator* iter2)
{
    return iter1->strpos == iter2->strpos;
}

uint8_t iteratorGetUTF8Byte(const BSQStringIterator* iter)
{
    assert(iteratorIsValid(iter));

    if(IS_INLINE_STRING(&iter->str))
    {
        return *(BSQInlineString::utf8Bytes(iter->str.u_inlineString) + iter->cpos);
    }
    else
    {
        return *(BSQStringKReprTypeAbstract::getUTF8Bytes(iter->cbuff) + iter->cpos);
    }
}

void initializeStringIterPosition(BSQStringIterator* iter, int64_t pos)
{
    auto ssize = (int64_t)BSQStringType::utf8ByteCount(iter->str);
    if((pos == -1) | (pos == ssize) | (ssize == 0))
    {
        iter->cbuff = nullptr;
        iter->statusflag = g_invalidIterFlag;
    }
    else
    {
        if (IS_INLINE_STRING(&iter->str))
        {
            iter->cbuff = nullptr;
            iter->minpos = 0;
            iter->maxpos = (int16_t)BSQInlineString::utf8ByteCount(iter->str.u_inlineString);
            iter->cpos = (int16_t)pos;
        }
        else
        {
            GET_TYPE_META_DATA_AS(BSQStringReprType, iter->str.u_data)->initializeIterPosition(iter, iter->str.u_data, pos);
        }
        iter->statusflag = g_validIterFlag;
    }
}

void incrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos++;
    iter->cpos++;
    
    if(iter->strpos == 0 || iter->cpos == iter->maxpos)
    {
        initializeStringIterPosition(iter, iter->strpos);
    }
}

void decrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos--;
    iter->cpos--;
    
    if(iter->strpos == BSQStringType::utf8ByteCount(iter->str) - 1 || iter->cpos < iter->minpos)
    {
        initializeStringIterPosition(iter, iter->strpos);
    }
}

uint32_t iteratorGetCodePoint(BSQStringIterator* iter)
{
    assert(iteratorIsValid(iter));

    auto utfbyte = iteratorGetUTF8Byte(iter);
    if((utfbyte & 0x8) == 0)
    {
        return utfbyte;
    }
    else
    {
        //not implemented
        assert(false);
        return 0;
    }
}

void incrementStringIterator_codePoint(BSQStringIterator* iter)
{
    assert(iteratorIsValid(iter));

    auto utfbyte = iteratorGetUTF8Byte(iter);
    if((utfbyte & 0x8) == 0)
    {
        incrementStringIterator_utf8byte(iter);
    }
    else
    {
        //not implemented
        assert(false);
    }
}

void decrementStringIterator_codePoint(BSQStringIterator* iter)
{
    assert(iteratorIsValid(iter));

    decrementStringIterator_utf8byte(iter);
    if(iter->strpos != -1)
    {
        assert(iteratorIsValid(iter));

        auto utfbyte = iteratorGetUTF8Byte(iter);
        if((utfbyte & 0x8) != 0)
        {
            //not implemented
            assert(false);
        }
    }
}

void BSQStringIteratorType::registerIteratorGCRoots(BSQStringIterator* iter)
{
    if(!IS_INLINE_STRING(&iter->str))
    {
        Allocator::GlobalAllocator.pushRoot(&(iter->str.u_data));
        Allocator::GlobalAllocator.pushRoot(&(iter->cbuff));
    }
}
    
void BSQStringIteratorType::releaseIteratorGCRoots(BSQStringIterator* iter)
{
    if(!IS_INLINE_STRING(&iter->str))
    {
        Allocator::GlobalAllocator.popRoots<2>();
    }
}

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQString str = SLPTR_LOAD_CONTENTS_AS(BSQString, data);

    std::string res;
    res.reserve((size_t)BSQStringType::utf8ByteCount(str));

    BSQStringIterator iter;
    BSQStringType::initializeIteratorBegin(&iter, str);
    
    while(iteratorIsValid(&iter))
    {
        res.push_back((char)iteratorGetUTF8Byte(&iter));
        incrementStringIterator_utf8byte(&iter);
    }

    return "\"" + res + "\"";
}

int entityStringKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringType::keycmp(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
}

bool entityStringJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = j.get<std::string>();
        BSQString s = g_emptyString;
        if(sstr.size() == 0)
        {
            //already empty
        }
        else if(sstr.size() < 16) 
        {
            s.u_inlineString = BSQInlineString::create((const uint8_t*)sstr.c_str(), sstr.size());
        }
        else if(sstr.size() <= 256)
        {
            auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&sstr](const std::pair<size_t, const BSQType*>& cc) {
                return cc.first > sstr.size();
            });
            s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp->second);
            BSQ_MEM_COPY(s.u_data, sstr.c_str(), sstr.size());
        }
        else
        {
            //
            //TODO: split the string into multiple parts
            //
            assert(false);
        }
        
        dynamic_cast<const BSQStringType*>(BSQType::g_typeString)->storeValueDirect(sl, s);
        return true;
    }
}

uint8_t* BSQStringType::boxInlineString(BSQInlineString istr)
{
    auto res = (uint8_t*)Allocator::GlobalAllocator.allocateSafe(BSQType::g_typeStringKRepr16);
    *res = (uint8_t)BSQInlineString::utf8ByteCount(istr);
    BSQ_MEM_COPY(res + 1, BSQInlineString::utf8Bytes(istr), *res);

    return res;
}

void initializeIteratorMin(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = -1;
    iter->cbuff = nullptr;
}

void initializeIteratorMax(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = BSQStringType::utf8ByteCount(str);
    iter->cbuff = nullptr;
}

void BSQStringType::initializeIteratorBegin(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = 0;
    iter->cbuff = nullptr;

    initializeStringIterPosition(iter, iter->strpos);
}

void BSQStringType::initializeIteratorEnd(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = BSQStringType::utf8ByteCount(str) - 1;
    iter->cbuff = nullptr;

    initializeStringIterPosition(iter, iter->strpos);
}

int BSQStringType::keycmp(BSQString v1, BSQString v2)
{
    if(BSQStringType::empty(v1) & BSQStringType::empty(v2))
    {
        return 0;
    }
    else if(IS_INLINE_STRING(&v1) && IS_INLINE_STRING(&v2))
    {
        return memcmp(BSQInlineString::utf8Bytes(v1.u_inlineString), BSQInlineString::utf8Bytes(v2.u_inlineString), 16);
    }
    else
    {
        auto bdiff = BSQStringType::utf8ByteCount(v1) - BSQStringType::utf8ByteCount(v2);
        if(bdiff != 0)
        {
            return bdiff < 0 ? -1 : 1;
        }   
        else
        {
            //
            //TODO: we want to add some order magic where we intern longer concat strings in sorted tree and can then just compare pointer equality or parent order instead of looking at full data 
            //

            BSQStringIterator iter1;
            BSQStringType::initializeIteratorBegin(&iter1, v1);

            BSQStringIterator iter2;
            BSQStringType::initializeIteratorBegin(&iter2, v2);

            while(iteratorIsValid(&iter1) && iteratorIsValid(&iter2))
            {
                auto diff = iteratorGetUTF8Byte(&iter1) - iteratorGetUTF8Byte(&iter2);
                if(diff != 0)
                {
                    return diff;
                }
            }

            return 0;
        }
    }
}

BSQString BSQStringType::concat2(StorageLocationPtr s1, StorageLocationPtr s2)
{
    //
    //TODO: want to rebalance here later
    //

    Allocator::GlobalAllocator.ensureSpace(std::max(sizeof(BSQStringConcatRepr), (sizeof(BSQStringKReprType<32>))));

    BSQString str1 = SLPTR_LOAD_CONTENTS_AS(BSQString, s1);
    BSQString str2 = SLPTR_LOAD_CONTENTS_AS(BSQString, s2);

    if(BSQStringType::empty(str1) & BSQStringType::empty(str2))
    {
        return g_emptyString;
    }
    else if(BSQStringType::empty(str1))
    {
        return str2;
    }
    else if(BSQStringType::empty(str2))
    {
        return str1;
    }
    else
    {
        auto len1 = BSQStringType::utf8ByteCount(str1);
        auto len2 = BSQStringType::utf8ByteCount(str2);

        BSQString res;
        if(IS_INLINE_STRING(&str1) & IS_INLINE_STRING(&str2))
        {
            if(len1 + len2 < 16)
            {
                BSQInlineString::utf8ByteCount_Initialize(res.u_inlineString, (uint64_t)(len1 + len2));
                GC_MEM_COPY(BSQInlineString::utf8Bytes(res.u_inlineString), BSQInlineString::utf8Bytes(str1.u_inlineString), (size_t)len1);
                GC_MEM_COPY(BSQInlineString::utf8Bytes(res.u_inlineString) + len1, BSQInlineString::utf8Bytes(str2.u_inlineString), (size_t)len2);
            }
            else
            {
                assert(len1 + len2 <= 30);

                auto crepr = (uint8_t*)Allocator::GlobalAllocator.allocateSafe(BSQType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                *crepr = (uint8_t)(len1 + len2);
                BSQ_MEM_COPY(curr, BSQInlineString::utf8Bytes(str1.u_inlineString), len1);
                BSQ_MEM_COPY(curr + len1, BSQInlineString::utf8Bytes(str1.u_inlineString), len2);

                res.u_data = crepr;
            }
        }
        else
        {
            if(len1 + len2 < 32)
            {
                auto crepr = (uint8_t*)Allocator::GlobalAllocator.allocateSafe(BSQType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                *crepr = (uint8_t)(len1 + len2);

                BSQStringIterator iter1;
                BSQStringType::initializeIteratorBegin(&iter1, str1);
                while(iteratorIsValid(&iter1))
                {
                    *curr = iteratorGetUTF8Byte(&iter1);
                    curr++;
                    incrementStringIterator_utf8byte(&iter1);
                }

                BSQStringIterator iter2;
                BSQStringType::initializeIteratorBegin(&iter2, str2);
                while(iteratorIsValid(&iter2))
                {
                    *curr = iteratorGetUTF8Byte(&iter2);
                    curr++;
                    incrementStringIterator_utf8byte(&iter2);
                }

                res.u_data = crepr;
            }
            else
            {
                auto crepr = (BSQStringConcatRepr*)Allocator::GlobalAllocator.allocateSafe(BSQType::g_typeStringConcatRepr);
                crepr->size = (uint64_t)(len1 + len2);
                crepr->srepr1 = IS_INLINE_STRING(s1) ? BSQStringType::boxInlineString(str1.u_inlineString) : str1.u_data;
                crepr->srepr2 = IS_INLINE_STRING(s2) ? BSQStringType::boxInlineString(str2.u_inlineString) : str2.u_data;
                
                res.u_data = crepr;
            }
        }

        return res;
    }
}

BSQString BSQStringType::slice(StorageLocationPtr str, StorageLocationPtr startpos, StorageLocationPtr endpos)
{
    //
    //TODO: want to rebalance here later
    //

    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQStringKReprType<32>));

    auto istart = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, startpos);
    auto iend = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, endpos);
    auto rstr = SLPTR_LOAD_CONTENTS_AS(BSQString, str);

    if(istart.strpos >= iend.strpos)
    {
        return g_emptyString;
    }
    else
    {
        int64_t dist = iend.strpos - istart.strpos;

        BSQString res = {0};
        if(IS_INLINE_STRING(&rstr))
        {
            res.u_inlineString = BSQInlineString::create(BSQInlineString::utf8Bytes(rstr.u_inlineString) + istart.strpos, (uint64_t)dist);
        }
        else
        {
            if(dist < 16)
            {
                BSQInlineString::utf8ByteCount_Initialize(res.u_inlineString, (uint64_t)dist);
                uint8_t* curr = BSQInlineString::utf8Bytes(res.u_inlineString);
                while(iteratorLess(&istart, &iend))
                {
                    *curr = iteratorGetUTF8Byte(&istart);
                }
            }
            else if(dist < 32)
            {
                res.u_data = Allocator::GlobalAllocator.allocateSafe(BSQType::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(res.u_data);
                while(iteratorLess(&istart, &iend))
                {
                    *curr = iteratorGetUTF8Byte(&istart);
                }
            }
            else
            {
                auto reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, rstr.u_data);
                res.u_data = reprtype->slice(rstr.u_data, (uint64_t)istart.strpos, (uint64_t)iend.strpos);
            }
        }

        return res;
    }
}

std::string entityByteBufferDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[Byte Buffer]";
}


std::string entityBufferDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[Buffer]";
}


std::string entityDataBufferDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[Data Buffer]";
}

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    assert(false);
    return "[ISO TIME]";
}

bool entityISOTimeJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    assert(false);
    return false;
}

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data)) + ":LogicalTime";
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

bool entityLogicalTimeJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    std::optional<std::string> nval = parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }

    dynamic_cast<const BSQLogicalTimeType*>(BSQType::g_typeLogicalTime)->storeValueDirect(sl, std::stoull(nval.value()));
    return true;
}

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    assert(false);
    return "[UUID]";
}

int entityUUIDKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1);
    auto v2 = (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2);

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

bool entityUUIDJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    assert(false);
    return false;
}

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    assert(false);
    return "[ContentHash]";
}

int entityContentHashKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = (BSQContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1);
    auto v2 = (BSQContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2);

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

bool entityContentHashJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    assert(false);
    return false;
}

BSQRegexOpt* BSQRegexOpt::parse(json j)
{
    if(j.is_string())
    {
        return BSQLiteralRe::parse(j);
    }
    else
    {
        auto tag = j["tag"].get<std::string>();
        if(tag == "CharClass")
        {
            return BSQCharClassRe::parse(j);
        }
        else if(tag == "CharRange")
        {
            return BSQCharRangeRe::parse(j);
        }
        else if(tag == "StarRepeat")
        {
            return BSQStarRepeatRe::parse(j);
        }
        else if(tag == "PlusRepeat")
        {
            return BSQPlusRepeatRe::parse(j);
        }
        else if(tag == "RangeRepeat")
        {
            return BSQRangeRepeatRe::parse(j);
        }
        else if(tag == "Optional")
        {
            return BSQOptionalRe::parse(j);
        }
        else if(tag == "Alternation")
        {
            return BSQAlternationRe::parse(j);
        }
        else
        {
            return BSQSequenceRe::parse(j);
        }
    }
}

std::optional<int64_t> BSQLiteralRe::match(BSQStringIterator iter) const
{
    //
    //TODO: unicode support and escape support
    //

    auto curr = this->litval.cbegin();
    while(iteratorIsValid(&iter) && curr != this->litval.cend())
    {
        if(iteratorGetCodePoint(&iter) != (uint32_t)*curr)
        {
            return std::nullopt;
        }

        incrementStringIterator_codePoint(&iter);
        curr++;
    }

    if(curr == this->litval.cend())
    {
        return std::make_optional(iter.strpos);
    }
    else
    {
        return std::nullopt;
    }
}

BSQLiteralRe* BSQLiteralRe::parse(json j)
{
    return new BSQLiteralRe(j.get<std::string>());
}

std::optional<int64_t> BSQCharRangeRe::match(BSQStringIterator iter) const
{
    if(!iteratorIsValid(&iter))
    {
        return std::nullopt;
    }
    
    auto cp = iteratorGetCodePoint(&iter);
    if(this->low <= (uint32_t)cp && (uint32_t)cp <= this->high)
    {
        return std::make_optional(iter.strpos + 1);
    }
    else
    {
        return std::nullopt;
    }
}

BSQCharRangeRe* BSQCharRangeRe::parse(json j)
{
    auto lb = j["lb"].get<uint64_t>();
    auto ub = j["ub"].get<uint64_t>();

    return new BSQCharRangeRe(lb, ub);
}

std::optional<int64_t> BSQCharClassRe::match(BSQStringIterator iter) const
{
    if(this->kind == SpecialCharKind::Wildcard)
    {
        return std::make_optional(iter.strpos + 1);
    }
    else
    {
        auto cp = iteratorGetCodePoint(&iter);
        char ws_char[] = {' ', '\n', '\r', '\t' };
        if((cp == ' ') | (cp == '\n') | (cp == '\r') | (cp == '\t'))
        {
            return std::make_optional(iter.strpos + 1);
        }
        else
        {
            return std::nullopt;
        }
    }
}

BSQCharClassRe* BSQCharClassRe::parse(json j)
{
    auto kind = j["kind"].get<SpecialCharKind>();

    return new BSQCharClassRe(kind);
}

std::string BSQStarRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(0, finfo.limits.re_repeat_max);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQStarRepeatRe* BSQStarRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQStarRepeatRe(repeat);
}

std::string BSQPlusRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(1, finfo.limits.re_repeat_max);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQPlusRepeatRe* BSQPlusRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQPlusRepeatRe(repeat);
}

std::string BSQRangeRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(this->low, this->high);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQRangeRepeatRe* BSQRangeRepeatRe::parse(json j)
{
    auto min = j["min"].get<uint64_t>();
    auto max = j["max"].get<uint64_t>();
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQRangeRepeatRe(min, max, repeat);
}

std::string BSQOptionalRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<uint32_t> ctdist(0, 1);

    auto ct = ctdist(rnd);
    if(ct == 1)
    {
        return this->opt->generate(rnd, finfo);
    }
    else
    {
        return "";
    }
}

BSQOptionalRe* BSQOptionalRe::parse(json j)
{
    auto opt = BSQRegexOpt::parse(j["opt"]);

    return new BSQOptionalRe(opt);
}

std::string BSQAlternationRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> idxdist(0, this->opts.size() - 1);
    auto opt = this->opts[idxdist(rnd)];

    return opt->generate(rnd, finfo);   
}

BSQAlternationRe* BSQAlternationRe::parse(json j)
{
    std::vector<const BSQRegexOpt*> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](json arg) {
        return BSQRegexOpt::parse(arg);
    });

    return new BSQAlternationRe(opts);
}

std::string BSQSequenceRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::string res;
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        res.append(this->opts[i]->generate(rnd, finfo));
    }

    return res;
}

BSQRegex bsqRegexJSONParse_impl(json j)
{
    auto restr = j["restr"].get<std::string>();
    auto isAnchorStart = j["isAnchorStart"].get<bool>();
    auto isAnchorEnd = j["isAnchorEnd"].get<bool>();

    return BSQRegex{restr, std::regex{restr}, isAnchorStart, isAnchorEnd};
}

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::string("/") + ((BSQRegex*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->restr + std::string("/");
}

std::string entityValidatorDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return btype->name + std::string("/") + ((BSQRegex*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->restr + std::string("/");
}

std::string entityStringOfDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return btype->name + entityStringDisplay_impl(BSQType::g_typetable[BSQ_TYPE_ID_STRING], data);
}

bool entityStringOfJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_string())
    {
        return false;
    }
    else
    {
        std::string sstr = j.get<std::string>();
        const BSQRegex& vre = dynamic_cast<const BSQValidatorType*>(BSQType::g_typetable[dynamic_cast<const BSQStringOfType*>(btype)->validator])->re;

        if(!std::regex_match(sstr, vre.cppre))
        {
            return false;
        }

        return BSQType::g_typeString->consops.fpJSONParse(BSQType::g_typeString, j, sl);
    }
}

std::string entityDataStringDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return btype->name + entityStringDisplay_impl(BSQType::g_typetable[BSQ_TYPE_ID_STRING], data);
}

bool entityDataStringJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    assert(false);
    return false;
}

std::string entityTypedNumberDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto utype = BSQType::g_typetable[dynamic_cast<const BSQTypedNumberTypeAbstract*>(btype)->underlying];
    return btype->name + utype->fpDisplay(utype, data);
}

bool entityTypedNumberJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    //
    //TODO: need to propagate the invariant call info and then check here -- for now pretend there are no additional checks
    //
    
    auto utype = BSQType::g_typetable[dynamic_cast<const BSQTypedNumberTypeAbstract*>(btype)->underlying];
    return utype->consops.fpJSONParse(utype, j, sl);
}

std::string enumDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto underlying = dynamic_cast<const BSQEnumType*>(btype)->underlying;
    return "(" + btype->name + ")" + underlying->fpDisplay(underlying, data);
}

bool enumJSONParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_string())
    {
        return false;
    }
    else
    {
        auto ename = j.get<std::string>();

        auto etype = dynamic_cast<const BSQEnumType*>(btype);
        auto cpos = std::find_if(etype->enuminvs.cbegin(), etype->enuminvs.cend(), [&ename](const std::pair<std::string, uint32_t>& entry) {
            return entry.first == ename;
        })->second;
    
        etype->underlying->storeValue(sl, Environment::g_constantbuffer + cpos);
        return true;
    }
}
