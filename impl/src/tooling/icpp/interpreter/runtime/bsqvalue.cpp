//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "environment.h"

#include "boost/uuid/uuid_io.hpp"

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

std::string generateRandomChar(RandGenerator& rnd)
{
    char small_char[] = {' ', '!', '0', '1', '4', 'a', 'i', 'Q', 'Z', ':', '_', '(', ')',  };
    uint8_t small_unic[] = {/*£*/ 194, 163, /*µ*/ 194, 181};
    uint8_t emoji[] = {/*🌵*/ 240, 159, 140, 181};
    auto ulimc = Environment::g_small_model_gen ? (sizeof(small_char) + (sizeof(small_unic) / 2) + 1) : 94;
    std::uniform_int_distribution<uint32_t> chardist(0, ulimc);

    std::string data;
    if(!Environment::g_small_model_gen)
    {
        data.append({ (char)(32 + chardist(rnd)) });
    }
    else
    {
        auto choice = chardist(rnd);
        if(choice < sizeof(small_char))
        {
            data.append({ (char)small_char[choice] });
        }
        else
        {
            if(choice < ulimc - (sizeof(emoji) / 4))
            {
                choice = choice - sizeof(small_char);
                data.append({ (char)small_unic[choice], (char)small_unic[choice + 1] });
            }
            else
            {
                choice = choice - (sizeof(small_char) + (sizeof(small_unic) / 2)); 
                data.append({ (char)emoji[choice], (char)emoji[choice + 1],  (char)emoji[choice + 2],  (char)emoji[choice + 3] });
            }
        }
    }

    return data;
}

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "none";
}

int entityNoneKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return 0;
}

bool entityNoneJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_null())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNoneType*>(BSQType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
        return true;
    }
}

void entityNoneGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    dynamic_cast<const BSQNoneType*>(BSQType::g_typeNone)->storeValueDirect(sl, BSQNoneValue);
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

bool entityBoolJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_null())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQBoolType*>(BSQType::g_typeBool)->storeValueDirect(sl, jv.as_bool() ? BSQTRUE : BSQFALSE);
        return true;
    }
}

void entityBoolGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    std::uniform_int_distribution<int> distribution(0, 1);
    dynamic_cast<const BSQBoolType*>(BSQType::g_typeBool)->storeValueDirect(sl, distribution(rnd) == 1 ? BSQTRUE : BSQFALSE);
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

bool entityNatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_int64())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQNatType*>(BSQType::g_typeNat)->storeValueDirect(sl, jv.as_int64());
        return true;
    }
}

void entityNatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto lim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQNat>::max();
    
    std::uniform_int_distribution<BSQNat> distribution(0, lim);
    dynamic_cast<const BSQNatType*>(BSQType::g_typeNat)->storeValueDirect(sl, distribution(rnd));
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

bool entityIntJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_int64())
    {
        return false;
    }
    else
    {
        dynamic_cast<const BSQIntType*>(BSQType::g_typeInt)->storeValueDirect(sl, jv.as_int64());
        return true;
    }
}

void entityIntGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto llim = Environment::g_small_model_gen ? -10 : std::numeric_limits<BSQInt>::min();
    auto ulim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQInt>::max();
    
    std::uniform_int_distribution<BSQInt> distribution(llim, ulim);
    dynamic_cast<const BSQIntType*>(BSQType::g_typeInt)->storeValueDirect(sl, distribution(rnd));
}

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data).str() + "N";
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

bool entityBigNatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQBigNat bn(sstr.subview(1, sstr.size() - 2));
        dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, bn);
        return true;
    }
}

void entityBigNatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto lim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQNat>::max();
    
    std::uniform_int_distribution<BSQNat> distribution(0, lim);
    dynamic_cast<const BSQBigNatType*>(BSQType::g_typeBigNat)->storeValueDirect(sl, distribution(rnd));
}

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data).str() + "I";
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

bool entityBigIntJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQBigInt bn(sstr.subview(1, sstr.size() - 2));
        dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, bn);
        return true;
    }
}

void entityBigIntGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto llim = Environment::g_small_model_gen ? -10 : std::numeric_limits<BSQInt>::min();
    auto ulim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQInt>::max();
    
    std::uniform_int_distribution<BSQInt> distribution(llim, ulim);
    dynamic_cast<const BSQBigIntType*>(BSQType::g_typeBigInt)->storeValueDirect(sl, distribution(rnd));
}

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQFloat, data)) + "f";
}

bool entityFloatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQFloat bfloat = std::stod(std::string(sstr.subview(1, sstr.size() - 2)));
        dynamic_cast<const BSQFloatType*>(BSQType::g_typeFloat)->storeValueDirect(sl, bfloat);
        return true;
    }
}

void entityFloatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    std::uniform_real_distribution<BSQFloat> distribution;
    dynamic_cast<const BSQFloatType*>(BSQType::g_typeFloat)->storeValueDirect(sl, distribution(rnd));
}

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQDecimal, data)) + "d";
}

bool entityDecimalJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQDecimal bdecimal = std::stod(std::string(sstr.subview(1, sstr.size() - 2)));
        dynamic_cast<const BSQDecimalType*>(BSQType::g_typeDecimal)->storeValueDirect(sl, bdecimal);
        return true;
    }
}

void entityDecimalGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    std::uniform_real_distribution<BSQDecimal> distribution;
    dynamic_cast<const BSQDecimalType*>(BSQType::g_typeDecimal)->storeValueDirect(sl, distribution(rnd));
}

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rval = SLPTR_LOAD_CONTENTS_AS(BSQRational, data);
    return rval.numerator.str() + "/" + std::to_string(rval.denominator) + "R";
}

bool entityRationalJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    assert(false);
    return false;
}

void entityRationalGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    assert(false);
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
    return iter->cbuff != nullptr;
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

    return res;
}

int entityStringKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringType::keycmp(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
}

bool entityStringJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
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
        
        return true;
    }
}

void entityStringGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto lim = Environment::g_small_model_gen ? 10 : 256;
    std::uniform_int_distribution<size_t> distribution(0, lim);

    auto size = distribution(rnd);
    std::string data;
    for(size_t i = 0; i < size; ++i)
    {
        data.append(generateRandomChar(rnd));
    }

    BSQString s = g_emptyString;
    if(size == 0)
    {
        //already empty
    }
    else if(size < 16) 
    {
        s.u_inlineString = BSQInlineString::create((const uint8_t*)data.c_str(), size);
    }
    else
    {
        auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&data](const std::pair<size_t, const BSQType*>& cc) {
            return cc.first > data.size();
        });
        s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp->second);
        BSQ_MEM_COPY(s.u_data, data.c_str(), size);
    }

    dynamic_cast<const BSQStringType*>(BSQType::g_typeString)->storeValue(sl, &s);
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

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQISOTime, data)) + ":IsoTime";
}

bool entityISOTimeJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQISOTime iso = std::stoul(sstr.subview(1, sstr.size() - 2).to_string());
        dynamic_cast<const BSQISOTimeType*>(BSQType::g_typeISOTime)->storeValueDirect(sl, iso);
        return true;
    }
}

void entityISOTimeGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto lim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQISOTime>::max();
    
    std::uniform_int_distribution<BSQISOTime> distribution(0, lim);
    dynamic_cast<const BSQISOTimeType*>(BSQType::g_typeISOTime)->storeValueDirect(sl, distribution(rnd));
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

bool entityLogicalTimeJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto sstr = jv.as_string();
        BSQLogicalTime lgt = std::stoul(sstr.subview(1, sstr.size() - 2).to_string());
        dynamic_cast<const BSQLogicalTimeType*>(BSQType::g_typeLogicalTime)->storeValueDirect(sl, lgt);
        return true;
    }
}

void entityLogicalTimeGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    auto lim = Environment::g_small_model_gen ? 10 : std::numeric_limits<BSQISOTime>::max();
    
    std::uniform_int_distribution<BSQLogicalTime> distribution(0, lim);
    dynamic_cast<const BSQLogicalTimeType*>(BSQType::g_typeLogicalTime)->storeValueDirect(sl, distribution(rnd));
}

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return to_string(*(BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data));
}

int entityUUIDKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1);
    auto v2 = (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2);
    if(*v1 == *v2)
    {
        return 0;
    }
    else
    {
        return (*v1 < *v2) ? -1 : 1;
    }
}

bool entityUUIDJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    assert(false);
    return true;
}

void entityUUIDGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    assert(false);
}

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQContentHash, data).str() + ":Hash";
}

int entityContentHashKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2)
{
    auto v1 = (BSQContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1);
    auto v2 = (BSQContentHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2);
    if(*v1 == *v2)
    {
        return 0;
    }
    else
    {
        return (*v1 < *v2) ? -1 : 1;
    }
}

bool entityContentHashJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    assert(false);
    return true;
}

void entityContentHashGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    assert(false);
}

BSQRegexOpt* BSQRegexOpt::reoptJSONParse_impl(const boost::json::value& jv)
{
    if(jv.is_string())
    {
        return BSQLiteralRe::litoptJSONParse_impl(jv);
    }
    else
    {
        auto tag = jsonGetAsString(jv, "tag");
        if(tag == "CharClass")
        {
            return BSQCharClassRe::classoptJSONParse_impl(jv);
        }
        else if(tag == "CharRange")
        {
            return BSQCharRangeRe::crangeoptJSONParse_impl(jv);
        }
        else if(tag == "StarRepeat")
        {
            return BSQStarRepeatRe::staroptJSONParse_impl(jv);
        }
        else if(tag == "PlusRepeat")
        {
            return BSQPlusRepeatRe::plusoptJSONParse_impl(jv);
        }
        else if(tag == "RangeRepeat")
        {
            return BSQRangeRepeatRe::rangeoptJSONParse_impl(jv);
        }
        else if(tag == "Optional")
        {
            return BSQOptionalRe::optoptJSONParse_impl(jv);
        }
        else if(tag == "Alternation")
        {
            return BSQAlternationRe::altoptJSONParse_impl(jv);
        }
        else
        {
            return BSQSequenceRe::seqoptJSONParse_impl(jv);
        }
    }
}

std::string BSQLiteralRe::generate(RandGenerator& rnd) const
{
    return this->litval;
}

BSQLiteralRe* BSQLiteralRe::litoptJSONParse_impl(const boost::json::value& jv)
{
    auto lstr = std::string(jv.as_string().c_str());
    return new BSQLiteralRe(lstr);
}

std::string BSQCharRangeRe::generate(RandGenerator& rnd) const
{
    //
    //TODO: unicode support and escape support
    //
    assert(32 <= low && high < 126);

    std::uniform_int_distribution<uint32_t> distribution(low, high);
    return std::string{(char)distribution(rnd)};
}

BSQCharRangeRe* BSQCharRangeRe::crangeoptJSONParse_impl(const boost::json::value& jv)
{
    auto lb = (uint64_t)jv.as_object().at("lb").as_int64();
    auto ub = (uint64_t)jv.as_object().at("ub").as_int64();

    return new BSQCharRangeRe(lb, ub);
}

std::string BSQCharClassRe::generate(RandGenerator& rnd) const
{
    //
    //TODO: unicode support and escape support
    //
    if(this->kind == SpecialCharKind::Wildcard)
    {
        return generateRandomChar(rnd);
    }
    else
    {
        char ws_char[] = {' ', '\n', '\r', '\t' };
        std::uniform_int_distribution<uint32_t> chardist(0, sizeof(ws_char));

        return std::string{ws_char[chardist(rnd)]};
    }
}

BSQCharClassRe* BSQCharClassRe::classoptJSONParse_impl(const boost::json::value& jv)
{
    auto kind = (SpecialCharKind)jv.as_object().at("kind").as_int64();

    return new BSQCharClassRe(kind);
}

std::string BSQStarRepeatRe::generate(RandGenerator& rnd) const
{
    auto ulimc = Environment::g_small_model_gen ? 3 : 10;
    std::uniform_int_distribution<size_t> ctdist(0, ulimc);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd));
    }

    return res;
}

BSQStarRepeatRe* BSQStarRepeatRe::staroptJSONParse_impl(const boost::json::value& jv)
{
    auto repeat = BSQRegexOpt::reoptJSONParse_impl(jv.as_object().at("repeat"));

    return new BSQStarRepeatRe(repeat);
}

std::string BSQPlusRepeatRe::generate(RandGenerator& rnd) const
{
    auto ulimc = Environment::g_small_model_gen ? 3 : 10;
    std::uniform_int_distribution<uint32_t> ctdist(1, ulimc);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd));
    }

    return res;
}

BSQPlusRepeatRe* BSQPlusRepeatRe::plusoptJSONParse_impl(const boost::json::value& jv)
{
    auto repeat = BSQRegexOpt::reoptJSONParse_impl(jv.as_object().at("repeat"));

    return new BSQPlusRepeatRe(repeat);
}

std::string BSQRangeRepeatRe::generate(RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint32_t> ctdist(this->low, this->high);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd));
    }

    return res;
}

 BSQRangeRepeatRe* BSQRangeRepeatRe::rangeoptJSONParse_impl(const boost::json::value& jv)
 {
    auto repeat = BSQRegexOpt::reoptJSONParse_impl(jv.as_object().at("repeat"));
    auto min = (uint32_t)jv.as_object().at("min").as_int64();
    auto max = (uint32_t)jv.as_object().at("max").as_int64();

    return new BSQRangeRepeatRe(min, max, repeat);
 }

std::string BSQOptionalRe::generate(RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint32_t> ctdist(0, 1);

    auto ct = ctdist(rnd);
    if(ct == 1)
    {
        return this->opt->generate(rnd);
    }
    else
    {
        return "";
    }
}

BSQOptionalRe* BSQOptionalRe::optoptJSONParse_impl(const boost::json::value& jv)
{
    auto opt = BSQRegexOpt::reoptJSONParse_impl(jv.as_object().at("opt"));

    return new BSQOptionalRe(opt);
}

std::string BSQAlternationRe::generate(RandGenerator& rnd) const
{
    std::uniform_int_distribution<size_t> idxdist(0, this->opts.size());
    auto opt = this->opts[idxdist(rnd)];

    return opt->generate(rnd);
}

BSQAlternationRe* BSQAlternationRe::altoptJSONParse_impl(const boost::json::value& jv)
{
    std::vector<const BSQRegexOpt*> opts;
    std::transform(jv.as_object().at("opts").as_array().cbegin(), jv.as_object().at("opts").as_array().cend(), std::back_inserter(opts), [](boost::json::value arg) {
        return BSQRegexOpt::reoptJSONParse_impl(arg);
    });

    return new BSQAlternationRe(opts);
}

std::string BSQSequenceRe::generate(RandGenerator& rnd) const
{
    std::string res;
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        res.append(this->opts[i]->generate(rnd));
    }

    return res;
}

BSQSequenceRe* BSQSequenceRe::seqoptJSONParse_impl(const boost::json::value& jv)
{
    std::vector<const BSQRegexOpt*> elems;
    std::transform(jv.as_object().at("elems").as_array().cbegin(), jv.as_object().at("elems").as_array().cend(), std::back_inserter(elems), [](boost::json::value arg) {
        return BSQRegexOpt::reoptJSONParse_impl(arg);
    });

    return new BSQSequenceRe(elems);
}

BSQRegex bsqRegexJSONParse_impl(const boost::json::value& jv)
{
    auto restr = jsonGetAsString(jv, "restr");
    auto isAnchorStart = jsonGetAsBool(jv, "isAnchorStart");
    auto isAnchorEnd = jsonGetAsBool(jv, "isAnchorEnd");
    auto re = BSQRegexOpt::reoptJSONParse_impl(jv.as_object().at("re"));

    return BSQRegex{restr, std::regex{restr}, isAnchorStart, isAnchorEnd, re};
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

bool entityStringOfJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        std::string sstr(jv.as_string().c_str(), jv.as_string().c_str() + jv.as_string().size());
        const BSQRegex& vre = dynamic_cast<const BSQValidatorType*>(BSQType::g_typetable[dynamic_cast<const BSQStringOfType*>(btype)->validator])->re;

        if(!std::regex_match(sstr, vre.cppre))
        {
            return false;
        }

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
        
        return true;
    }
}

void entityStringOfGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    std::string sstr = dynamic_cast<const BSQValidatorType*>(btype)->re.re->generate(rnd);

    //
    //TODO: we need to handle this case later
    //
    assert(sstr.size() < 256);

    BSQString s = g_emptyString;
    if(sstr.size() == 0)
    {
        //already empty
    }
    else if(sstr.size() < 16) 
    {
        s.u_inlineString = BSQInlineString::create((const uint8_t*)sstr.c_str(), sstr.size());
    }
    else
    {
        auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&sstr](const std::pair<size_t, const BSQType*>& cc) {
            return cc.first > sstr.size();
        });

        s.u_data = Allocator::GlobalAllocator.allocateDynamic(stp->second);
        BSQ_MEM_COPY(s.u_data, sstr.c_str(), sstr.size());
    }

    dynamic_cast<const BSQStringType*>(BSQType::g_typeString)->storeValue(sl, &s);
}

std::string entityDataStringDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return btype->name + entityStringDisplay_impl(BSQType::g_typetable[BSQ_TYPE_ID_STRING], data);
}

bool entityDataStringJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    assert(false);
    return true;
}

void entityDataStringGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    assert(false);
}

std::string entityTypedNumberDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto utype = BSQType::g_typetable[dynamic_cast<const BSQTypedNumberTypeAbstract*>(btype)->underlying];
    return btype->name + utype->fpDisplay(utype, data);
}

bool entityTypedNumberJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    //
    //TODO: need to propagate the invariant call info and then check here -- for now pretend there are no additional checks
    //
    
    auto utype = BSQType::g_typetable[dynamic_cast<const BSQTypedNumberTypeAbstract*>(btype)->underlying];
    return utype->consops.fpJSONParse(utype, jv, sl);
}

void entityTypedNumberGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    //
    //TODO: need to propagate the invariant call info and then check here -- for now pretend there are no additional checks
    //

    auto utype = BSQType::g_typetable[dynamic_cast<const BSQTypedNumberTypeAbstract*>(btype)->underlying];
    return utype->consops.fpGenerateRandom(utype, rnd, sl);
}


std::string enumDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto underlying = dynamic_cast<const BSQEnumType*>(btype)->underlying;
    return "(" + btype->name + ")" + underlying->fpDisplay(underlying, data);
}

bool enumJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl)
{
    if(!jv.is_string())
    {
        return false;
    }
    else
    {
        auto ename = jv.as_string();

        auto etype = dynamic_cast<const BSQEnumType*>(btype);
        auto cpos = std::find_if(etype->enuminvs.cbegin(), etype->enuminvs.cend(), [&ename](const std::pair<std::string, uint32_t>& entry) {
            return entry.first == ename;
        })->second;
    
        etype->underlying->storeValue(sl, Environment::g_constantbuffer + cpos);
        return true;
    }
}

void enumGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl)
{
    //This is going away soon!!!
    assert(false);
}

