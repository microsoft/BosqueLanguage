//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "environment.h"


std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "none";
}

bool entityNoneEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return true;
}

bool enityNoneLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return false;
}

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBool, data) ? "true" : "false";
}

bool entityBoolEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBoolType::equal(SLPTR_LOAD_CONTENTS_AS(BSQBool, data1), SLPTR_LOAD_CONTENTS_AS(BSQBool, data2));
}

bool enityBoolLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBoolType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQBool, data1), SLPTR_LOAD_CONTENTS_AS(BSQBool, data2));
}

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQNat, data)) + "n";
}

bool entityNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQNatType::equal(SLPTR_LOAD_CONTENTS_AS(BSQNat, data1), SLPTR_LOAD_CONTENTS_AS(BSQNat, data2));
}

bool enityNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQNatType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQNat, data1), SLPTR_LOAD_CONTENTS_AS(BSQNat, data2));
}

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQInt, data)) + "i";
}

bool entityIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQIntType::equal(SLPTR_LOAD_CONTENTS_AS(BSQInt, data1), SLPTR_LOAD_CONTENTS_AS(BSQInt, data2));
}

bool enityIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQIntType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQInt, data1), SLPTR_LOAD_CONTENTS_AS(BSQInt, data2));
}

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data).str() + "N";
}

bool entityBigNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBigNatType::equal(SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data1), SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data2));
}

bool enityBigNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBigNatType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data1), SLPTR_LOAD_CONTENTS_AS(BSQBigNat, data2));
}

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data).str() + "I";
}

bool entityBigIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBigIntType::equal(SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data1), SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data2));
}

bool enityBigIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQBigIntType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data1), SLPTR_LOAD_CONTENTS_AS(BSQBigInt, data2));
}

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQFloat, data).str() + "f";
}

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQDecimal, data).str() + "d";
}

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto rval = SLPTR_LOAD_CONTENTS_AS(BSQRational, data);
    return rval.numerator.str() + "/" + rval.denominator.str() + "R";
}

template <uint64_t k>
std::string entityStringKReprDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQStringKRepr<k>* kstr = (BSQStringKRepr<k>*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);
    return std::string(kstr->elems, kstr->elems + kstr->len);
}

std::string entityStringSliceReprDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQStringSliceRepr* slice = (BSQStringSliceRepr*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);
    const BSQType* kreprtype = GET_TYPE_META_DATA(slice->srepr);
    auto sstr = kreprtype->fpDisplay(kreprtype, slice->srepr);

    return sstr.substr(slice->start, slice->end - slice->start);
}

std::string entityStringConcatReprDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    const BSQStringConcatRepr* cstr = (BSQStringConcatRepr*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);
    const BSQType* s1type = GET_TYPE_META_DATA(cstr->srepr1);
    const BSQType* s2type = GET_TYPE_META_DATA(cstr->srepr2);

    return s1type->fpDisplay(s1type, cstr->srepr1) + s2type->fpDisplay(s2type, cstr->srepr2);
}

std::string entityStringBSQStringIteratorDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[StringIterator]";
}

bool iteratorIsValid(const BSQStringIterator* iter)
{
    return iter->cbuff != nullptr;
}

uint8_t iteratorGetUTF8Byte(const BSQStringIterator* iter)
{
    return iter->cbuff[iter->cpos];
}

void initializeStringIterStart(BSQStringIterator* iter, void* activeparent, const BSQStringReprType* reprtype, void* srepr)
{
    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        iter->activeparent = activeparent;
        iter->activerepr = srepr;
        iter->cbuff = BSQStringKReprTypeAbstract::getUTF8Bytes(srepr);

        const BSQStringReprType* parenttype = (activeparent != nullptr) ? GET_TYPE_META_DATA_AS(BSQStringReprType, activeparent) : nullptr;
        if(parenttype != nullptr && parenttype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
        {
            auto slicerepr = (BSQStringSliceRepr*)activeparent;
            iter->minpos = slicerepr->start;
            iter->maxpos = slicerepr->end;
            iter->cpos = slicerepr->start;
        }
        else
        {
            iter->minpos = 0;
            iter->maxpos = BSQStringKReprTypeAbstract::getUTF8ByteCount(srepr);
            iter->cpos = 0;
        }
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        auto slicerepr = (BSQStringSliceRepr*)srepr;
        initializeStringIterStart(iter, slicerepr, GET_TYPE_META_DATA_AS(BSQStringReprType, slicerepr->srepr), slicerepr->srepr);
    }
    else
    {
        auto concatrepr = (BSQStringConcatRepr*)srepr;
        initializeStringIterStart(iter, concatrepr, GET_TYPE_META_DATA_AS(BSQStringReprType, concatrepr->srepr1), concatrepr->srepr1);
    }
}

void incrementStringIterator_utf8byteSlow(BSQStringIterator* iter)
{
    if(iter->strpos == (int64_t)BSQStringType::utf8ByteCount(iter->str))
    {
        assert(iter->activeparent == nullptr);
        iter->cbuff = nullptr;
    }
    else if(iter->strpos == 0)
    {
        if (IS_INLINE_STRING(&iter->str))
        {
            iter->activeparent = nullptr;
            iter->activerepr = nullptr;
            iter->cbuff = BSQInlineString::utf8Bytes(iter->str.u_inlineString);
            iter->minpos = 0;
            iter->maxpos = BSQInlineString::utf8ByteCount(iter->str.u_inlineString);
            iter->cpos = 0;
        }
        else
        {
            initializeStringIterStart(iter, nullptr, GET_TYPE_META_DATA_AS(BSQStringReprType, iter->str.u_data), iter->str.u_data);
        }
    }
    else
    {
        if(GET_TYPE_META_DATA_AS(BSQStringReprType, iter->activeparent)->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
        {
            iter->activerepr = iter->activeparent;
            iter->activeparent = ((BSQStringSliceRepr*)iter->activeparent)->parent;
        }

        while(iter->activeparent != nullptr)
        {
            //it is always a concat
            auto crepr = ((BSQStringConcatRepr*)iter->activeparent);

            //if we are the left child then we switch to the right child and are done otherwise keep going up the tree
            if(crepr->srepr1 == iter->activerepr)
            {
                initializeStringIterStart(iter, iter->activeparent, GET_TYPE_META_DATA_AS(BSQStringReprType, crepr->srepr2), crepr->srepr2);
                break;
            }
            else
            {
                iter->activerepr = crepr;
                iter->activeparent = crepr->parent;
            }
        }
    }
}

void incrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos++;
    iter->cpos++;
    
    if((iter->cpos == iter->maxpos) || (iter->strpos == 0))
    {
        incrementStringIterator_utf8byteSlow(iter);
    }
}

void initializeStringIterEnd(BSQStringIterator* iter, void* activeparent, const BSQStringReprType* reprtype, void* srepr)
{
    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        iter->activeparent = activeparent;
        iter->activerepr = srepr;
        iter->cbuff = BSQStringKReprTypeAbstract::getUTF8Bytes(srepr);

        const BSQStringReprType* parenttype = (activeparent != nullptr) ? GET_TYPE_META_DATA_AS(BSQStringReprType, activeparent) : nullptr;
        if(parenttype != nullptr && parenttype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
        {
            auto slicerepr = (BSQStringSliceRepr*)activeparent;
            iter->minpos = slicerepr->start;
            iter->maxpos = slicerepr->end;
            iter->cpos = iter->maxpos - 1;
        }
        else
        {
            iter->minpos = 0;
            iter->maxpos = BSQStringKReprTypeAbstract::getUTF8ByteCount(srepr);
            iter->cpos = iter->maxpos - 1;
        }
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        auto slicerepr = (BSQStringSliceRepr*)srepr;
        initializeStringIterEnd(iter, slicerepr, GET_TYPE_META_DATA_AS(BSQStringReprType, slicerepr->srepr), slicerepr->srepr);
    }
    else
    {
        auto concatrepr = (BSQStringConcatRepr*)srepr;
        initializeStringIterEnd(iter, concatrepr, GET_TYPE_META_DATA_AS(BSQStringReprType, concatrepr->srepr2), concatrepr->srepr2);
    }
}

void decrementStringIterator_utf8byteSlow(BSQStringIterator* iter)
{
    if(iter->strpos == -1)
    {
        assert(iter->activeparent == nullptr);
        iter->cbuff = nullptr;
    }
    else if(iter->strpos == (int64_t)BSQStringType::utf8ByteCount(iter->str) - 1)
    {
        if(IS_INLINE_STRING(&iter->str))
        {
            iter->activeparent = nullptr;
            iter->activerepr = nullptr;
            iter->cbuff = BSQInlineString::utf8Bytes(iter->str.u_inlineString);
            iter->minpos = 0;
            iter->maxpos = BSQInlineString::utf8ByteCount(iter->str.u_inlineString);
            iter->cpos = iter->maxpos - 1;
        }
        else
        {
            initializeStringIterEnd(iter, nullptr, GET_TYPE_META_DATA_AS(BSQStringReprType, iter->str.u_data), iter->str.u_data);
        }
    }
    else
    {
        if(GET_TYPE_META_DATA_AS(BSQStringReprType, iter->activeparent)->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
        {
            iter->activerepr = iter->activeparent;
            iter->activeparent = ((BSQStringSliceRepr*)iter->activeparent)->parent;
        }

        while(iter->activeparent != nullptr)
        {
            //it is always a concat
            auto crepr = ((BSQStringConcatRepr*)iter->activeparent);

            //if we are the right child then we switch to the left child and are done otherwise keep going up the tree
            if(crepr->srepr2 == iter->activerepr)
            {
                initializeStringIterEnd(iter, iter->activeparent, GET_TYPE_META_DATA_AS(BSQStringReprType, crepr->srepr1), crepr->srepr1);
                break;
            }
            else
            {
                iter->activerepr = crepr;
                iter->activeparent = crepr->parent;
            }
        }
    }
}

void decrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos--;
    iter->cpos--;
    
    if((iter->cpos < iter->minpos) || (iter->strpos == (int64_t)BSQStringType::utf8ByteCount(iter->str) - 1))
    {
        incrementStringIterator_utf8byteSlow(iter);
    }
}

uint32_t iteratorGetCodePoint(BSQStringIterator* iter)
{
    assert(iteratorIsValid(iter));

    auto utfbyte = iteratorGetUTF8Byte(iter);
    if((utfbyte & 0x8) == 0)
    {
        utfbyte;
    }
    else
    {
        //not implemented
        assert(false);
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

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQString str = SLPTR_LOAD_CONTENTS_AS(BSQString, data);

    std::string res;
    res.reserve(BSQStringType::utf8ByteCount(str));

    BSQStringIterator iter;
    BSQStringIterator iend;
    BSQStringType::initializeIteratorBegin(&iter, str);
    BSQStringType::initializeIteratorEnd(&iend, str);
    
    while(iteratorIsLess(&iter, &iend))
    {
        res.push_back(iteratorGetUTF8Byte(&iter));
        incrementStringIterator_utf8byte(&iter);
    }

    return res;
}

bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringType::equal(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
}

bool enityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
}

uint64_t BSQStringReprType::getKReprSizeFor(uint64_t v)
{
    uint64_t i = g_kreprcount - 1;
    while(i > 0)
    {
        if(g_kreprsizes[i - 1] < v)
        {
            break;
        }
        i--;
    }
    return g_kreprsizes[i];
}

void* BSQStringType::allocateStringKForSize(uint64_t k, uint8_t** dataptr)
{
    uint64_t osize = BSQStringReprType::getKReprSizeFor(k);
    void* res = nullptr;

    switch(osize)
    {
    case 8:
        res = (BSQStringKRepr<8>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr8);
        break;
    case 16:
        res = (BSQStringKRepr<16>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr16);
        break;
    case 32: 
        res = (BSQStringKRepr<32>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr32);
        break;
    case 64:
        res = (BSQStringKRepr<64>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr64);
        break;
    case 128:
        res = (BSQStringKRepr<128>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr128);
        break;
    default:
        res = (BSQStringKRepr<256>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr256);
        break;
    }

    *((BSQNat*)res) = k;
    *dataptr = (uint8_t*)((uint8_t*)res) + sizeof(BSQNat);
    return res;
}

BSQStringKRepr<8>* BSQStringType::boxInlineString(BSQInlineString istr)
{
    auto res = (BSQStringKRepr<8>*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringKRepr<8>), Environment::g_typeStringKRepr8);
    res->size = BSQInlineString::utf8ByteCount(istr);
    std::copy(BSQInlineString::utf8Bytes(istr), BSQInlineString::utf8BytesEnd(istr), res->utf8bytes);

    return res;
}

void initializeIteratorMin(BSQStringIterator* iter, BSQString str)
{
    xxxx;
}

void initializeIteratorMax(BSQStringIterator* iter, BSQString str)
{
    xxxx;
}

void BSQStringType::initializeIteratorBegin(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = 0;
    iter->activeparent = nullptr;
    iter->activerepr = nullptr;
    iter->cbuff = nullptr;

    initializeStringIterStart(iter, nullptr, GET_TYPE_META_DATA_AS(BSQStringReprType, str.u_data), str.u_data);
}

void BSQStringType::initializeIteratorEnd(BSQStringIterator* iter, BSQString str)
{
    iter->str = str;
    iter->strpos = BSQStringType::utf8ByteCount(str);
    iter->activeparent = nullptr;
    iter->activerepr = nullptr;
    iter->cbuff = nullptr;

    initializeStringIterEnd(iter, nullptr, GET_TYPE_META_DATA_AS(BSQStringReprType, str.u_data), str.u_data);
}

bool BSQStringType::equal(BSQString v1, BSQString v2)
{
    if(BSQStringType::empty(v1) & BSQStringType::empty(v2))
    {
        return true;
    }
    else if(IS_INLINE_STRING(&v1) && IS_INLINE_STRING(&v2))
    {
        return memcmp(BSQInlineString::utf8Bytes(v1.u_inlineString), BSQInlineString::utf8Bytes(v2.u_inlineString), 8) == 0;
    }
    else
    {
        if(BSQStringType::utf8ByteCount(v1) != BSQStringType::utf8ByteCount(v2))
        {
            return false;
        }   
        else
        {
            BSQStringIterator iter1;
            BSQStringIterator iend1;
            BSQStringType::initializeIteratorBegin(&iter1, v1);
            BSQStringType::initializeIteratorEnd(&iend1, v1);

            BSQStringIterator iter2;
            BSQStringIterator iend2;
            BSQStringType::initializeIteratorBegin(&iter2, v2);
            BSQStringType::initializeIteratorEnd(&iend2, v1);

            while(iteratorIsLess(&iter1, &iend1) && iteratorIsLess(&iter2, &iend2))
            {
                if(iteratorGetUTF8Byte(&iter1) != iteratorGetUTF8Byte(&iter2))
                {
                    return false;
                }
            }

            return true;
        }
    }
}

bool BSQStringType::lessThan(BSQString v1, BSQString v2)
{
    if(BSQStringType::empty(v1) & BSQStringType::empty(v2))
    {
        return false;
    }
    else if(IS_INLINE_STRING(&v1) && IS_INLINE_STRING(&v2))
    {
        return memcmp(BSQInlineString::utf8Bytes(v1.u_inlineString), BSQInlineString::utf8Bytes(v2.u_inlineString), 8) < 0;
    }
    else
    {
        auto bdiff = BSQStringType::utf8ByteCount(v1) - BSQStringType::utf8ByteCount(v2);
        if(bdiff != 0)
        {
            return bdiff < 0;
        }   
        else
        {
            BSQStringIterator iter1;
            BSQStringType::initializeIteratorBegin(&iter1, v1);

            BSQStringIterator iter2;
            BSQStringType::initializeIteratorBegin(&iter2, v2);

            while(iteratorIsValid(&iter1) && iteratorIsValid(&iter2))
            {
                if(iteratorGetUTF8Byte(&iter1) < iteratorGetUTF8Byte(&iter2))
                {
                    return true;
                }
            }

            return false;
        }
    }
}

BSQString BSQStringType::concat2(StorageLocationPtr s1, StorageLocationPtr s2)
{
    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQStringConcatRepr) + sizeof(BSQStringKRepr<16>));

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
                BSQInlineString irepr = BSQInlineString::create2(BSQInlineString::utf8Bytes(str1.u_inlineString), len1, BSQInlineString::utf8Bytes(str2.u_inlineString), len2);

                res.u_inlineString = irepr;
            }
            else
            {
                auto crepr = (BSQStringKRepr<16>*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringKRepr<16>), Environment::g_typeStringKRepr16);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                crepr->size = len1 + len2;
                std::copy(BSQInlineString::utf8Bytes(str1.u_inlineString), BSQInlineString::utf8BytesEnd(str1.u_inlineString), curr);
                std::copy(BSQInlineString::utf8Bytes(str1.u_inlineString), BSQInlineString::utf8BytesEnd(str1.u_inlineString), curr + len1);

                res.u_data = crepr;
            }
        }
        else
        {
            if(len1 + len2 < 16)
            {
                auto crepr = (BSQStringKRepr<16>*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringKRepr<16>), Environment::g_typeStringKRepr16);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);

                crepr->size = len1 + len2;

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
                auto crepr = (BSQStringConcatRepr*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringConcatRepr), Environment::g_typeStringConcatRepr);
                crepr->parent = nullptr;
                crepr->size = len1 + len2;
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
    xxxx;
}

BSQString BSQStringType::sliceRepr(void* repr, BSQNat start, BSQNat end)
{
    const BSQStringReprType* tt = GET_TYPE_META_DATA_AS(BSQStringReprType, repr);

    if(tt->tag == BSQStringReprTypeTag::ReprK)
    {
        return xxxx;
    }
    else if(tt->tag == BSQStringReprTypeTag::Slice)
    {

    }
    else
    {

    }

    if(repr.is<StringSlice>()) {
            return String::s_sliceRepr[recursive](repr.s, repr.start + start, repr.start + end);
        }
        elif(repr.is<StringConcat>()) {
            let s1size = repr.s1.length();

            if(start >= s1size) {
                return String::s_sliceRepr[recursive](repr.s2, start - s1size, end - s1size);
            }
            else if(end <= s1size) {
                return String::s_sliceRepr[recursive](repr.s1, start, end);
            }
            else {
                let lhs = String::s_sliceRepr[recursive](repr.s1, start, s1size);
                let rhs = String::s_sliceRepr[recursive](repr.s2, 0, end - s1size);

                return String::s_concat2(lhs, rhs);
            }
            }
        else {
            let cstr = StringSlice@{repr, start, end}
            return String#{cstr, InlineString::g_emptystr};
        }

}



