//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "environment.h"

#include "boost/uuid/uuid_io.hpp"

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "none";
}

bool entityNoneEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return true;
}

bool entityNoneLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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

bool entityBoolLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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

bool entityNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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

bool entityIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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

bool entityBigNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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

bool entityBigIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
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
    return rval.numerator.str() + "/" + std::to_string(rval.denominator) + "R";
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
        return *(((uint8_t*)iter->cbuff) + iter->cpos);
    }
    else
    {
        return *(BSQStringKReprTypeAbstract::getUTF8Bytes(iter->cbuff) + iter->cpos);
    }
}

void initializeStringIterPosition_Helper(BSQStringIterator* iter, int64_t pos, void* optsliceparent, void* srepr)
{
    const BSQStringReprType* reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, srepr);

    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        iter->cbuff = srepr;

        if(optsliceparent != nullptr)
        {
            auto slicerepr = (BSQStringSliceRepr*)optsliceparent;
            iter->minpos = slicerepr->start;
            iter->maxpos = slicerepr->end;
            iter->cpos = iter->minpos + pos;
        }
        else
        {
            iter->minpos = 0;
            iter->maxpos = BSQStringKReprTypeAbstract::getUTF8ByteCount(srepr);
            iter->cpos = pos;
        }
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        auto slicerepr = (BSQStringSliceRepr*)srepr;
        initializeStringIterPosition_Helper(iter, pos, slicerepr, slicerepr->srepr);
    }
    else
    {
        auto concatrepr = (BSQStringConcatRepr*)srepr;
        auto s1size = (int64_t)BSQStringKReprTypeAbstract::getUTF8ByteCount(concatrepr->srepr1);
        if(pos < s1size)
        {
            initializeStringIterPosition_Helper(iter, pos, nullptr, concatrepr->srepr1);
        }
        else
        {
            initializeStringIterPosition_Helper(iter, pos - s1size, nullptr, concatrepr->srepr2);
        }
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
            iter->cbuff = BSQInlineString::utf8Bytes(iter->str.u_inlineString);
            iter->minpos = 0;
            iter->maxpos = BSQInlineString::utf8ByteCount(iter->str.u_inlineString);
            iter->cpos = pos;
        }
        else
        {
            initializeStringIterPosition_Helper(iter, pos, nullptr, iter->str.u_data);
        }
    }
}

void incrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos++;
    iter->cpos++;
    
    if(iter->cbuff == nullptr || iter->cpos == iter->maxpos)
    {
        initializeStringIterPosition(iter, iter->strpos);
    }
}

void decrementStringIterator_utf8byte(BSQStringIterator* iter)
{
    iter->strpos--;
    iter->cpos--;
    
    if(iter->cbuff == nullptr || iter->cpos < iter->minpos)
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
    res.reserve(BSQStringType::utf8ByteCount(str));

    BSQStringIterator iter;
    BSQStringType::initializeIteratorBegin(&iter, str);
    
    while(iteratorIsValid(&iter))
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

bool entityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQStringType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQString, data1), SLPTR_LOAD_CONTENTS_AS(BSQString, data2));
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
            BSQStringType::initializeIteratorBegin(&iter1, v1);

            BSQStringIterator iter2;
            BSQStringType::initializeIteratorBegin(&iter2, v2);

            while(iteratorIsValid(&iter1) && iteratorIsValid(&iter2))
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
    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQStringConcatRepr) + sizeof(BSQStringKRepr<32>));

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
                auto crepr = (BSQStringKRepr<32>*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringKRepr<32>), Environment::g_typeStringKRepr32);
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
                crepr->size = len1 + len2;
                crepr->srepr1 = IS_INLINE_STRING(s1) ? BSQStringType::boxInlineString(str1.u_inlineString) : str1.u_data;
                crepr->srepr2 = IS_INLINE_STRING(s2) ? BSQStringType::boxInlineString(str2.u_inlineString) : str2.u_data;
                
                res.u_data = crepr;
            }
        }

        return res;
    }
}

void* traverseReprTreeSliceFront(void* repr, int64_t count)
{
    if(count == 0)
    {
        return repr;
    }

    const BSQStringReprType* reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, repr);
    Allocator::GlobalAllocator.pushRoot(&repr);
    
    void* res = nullptr;
    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringSliceRepr);
        ((BSQStringSliceRepr*)res)->srepr = repr;
        ((BSQStringSliceRepr*)res)->start = count;
        xxxx;
        ((BSQStringSliceRepr*)res)->end = BSQStringKReprTypeAbstract::getUTF8ByteCount(repr);
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringSliceRepr);
        ((BSQStringSliceRepr*)res)->srepr = ((BSQStringSliceRepr*)repr)->srepr;
        ((BSQStringSliceRepr*)res)->start = ((BSQStringSliceRepr*)repr)->start + count;
        ((BSQStringSliceRepr*)res)->end = ((BSQStringSliceRepr*)repr)->end;
    }
    else
    {
        auto s1size = (int64_t)BSQStringReprType::getKReprSizeFor(((BSQStringConcatRepr*)repr)->srepr1);
        if(count < s1size)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringConcatRepr);
            Allocator::GlobalAllocator.pushRoot(&res);

            ((BSQStringConcatRepr*)res)->srepr1 = traverseReprTreeSliceFront(((BSQStringConcatRepr*)repr)->srepr1, count);
            ((BSQStringConcatRepr*)res)->srepr2 = ((BSQStringConcatRepr*)repr)->srepr2;
            ((BSQStringConcatRepr*)res)->size = ((BSQStringConcatRepr*)repr)->size - count;

            Allocator::GlobalAllocator.popRoot();        
        }
        else
        {
            res = traverseReprTreeSliceFront(((BSQStringConcatRepr*)repr)->srepr2, count - s1size);
        }
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}

void* traverseReprTreeSliceBack(void* repr, int64_t count)
{
    if(count == 0)
    {
        return repr;
    }

    const BSQStringReprType* reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, repr);
    Allocator::GlobalAllocator.pushRoot(&repr);
    
    void* res = nullptr;
    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringSliceRepr);
        ((BSQStringSliceRepr*)res)->srepr = repr;
        ((BSQStringSliceRepr*)res)->start = 0;
        ((BSQStringSliceRepr*)res)->end = BSQStringKReprTypeAbstract::getUTF8ByteCount(repr) - count;
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        res = (BSQStringSliceRepr*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringSliceRepr);
        ((BSQStringSliceRepr*)res)->srepr = ((BSQStringSliceRepr*)repr)->srepr;
        ((BSQStringSliceRepr*)res)->start = ((BSQStringSliceRepr*)repr)->start;
        ((BSQStringSliceRepr*)res)->end = ((BSQStringSliceRepr*)repr)->end - count;
    }
    else
    {
        auto s2size = (int64_t)BSQStringKReprTypeAbstract::getUTF8ByteCount(((BSQStringConcatRepr*)repr)->srepr2);
        if(count < s2size)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringConcatRepr);
            Allocator::GlobalAllocator.pushRoot(&res);

            ((BSQStringConcatRepr*)res)->srepr1 = ((BSQStringConcatRepr*)repr)->srepr1;
            ((BSQStringConcatRepr*)res)->srepr2 = traverseReprTreeSliceBack(((BSQStringConcatRepr*)repr)->srepr2, count);;
            ((BSQStringConcatRepr*)res)->size = ((BSQStringConcatRepr*)repr)->size - count;

            Allocator::GlobalAllocator.popRoot();
        }
        else
        {
            res = traverseReprTreeSliceFront(((BSQStringConcatRepr*)repr)->srepr1, count - s2size);
        }
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}

BSQString BSQStringType::slice(StorageLocationPtr str, StorageLocationPtr startpos, StorageLocationPtr endpos)
{
    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQStringKRepr<32>));

    auto istart = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, startpos);
    auto iend = SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, endpos);
    auto rstr = SLPTR_LOAD_CONTENTS_AS(BSQString, str);

    if(istart.strpos >= iend.strpos)
    {
        return g_emptyString;
    }
    else
    {
        auto dist = iend.strpos - istart.strpos;

        BSQString res;
        if(IS_INLINE_STRING(&rstr))
        {
            res.u_inlineString = BSQInlineString::create(BSQInlineString::utf8Bytes(rstr.u_inlineString) + istart.strpos, dist);
        }
        else
        {
            if(dist < 16)
            {
                BSQInlineString::utf8ByteCount_Initialize(res.u_inlineString, (uint64_t)dist);
                uint8_t* curr = BSQInlineString::utf8Bytes(rstr.u_inlineString);
                while(iteratorLess(&istart, &iend))
                {
                    *curr = iteratorGetUTF8Byte(&istart);
                }
            }
            else if(dist <= 32)
            {
                auto crepr = (BSQStringKRepr<32>*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQStringKRepr<32>), Environment::g_typeStringKRepr32);
                uint8_t* curr = BSQStringKReprTypeAbstract::getUTF8Bytes(crepr);
                while(iteratorLess(&istart, &iend))
                {
                    *curr = iteratorGetUTF8Byte(&istart);
                }
            }
            else
            {
                auto repr = rstr.u_data;
                auto reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, repr);

                auto frontcount = istart.strpos;
                auto backcount = (int64_t)BSQStringType::utf8ByteCount(rstr) - iend.strpos;

                auto fronttrim = traverseReprTreeSliceFront(repr, frontcount);
                Allocator::GlobalAllocator.pushRoot(&fronttrim);
    
                res.u_data = traverseReprTreeSliceBack(fronttrim, backcount);
                Allocator::GlobalAllocator.popRoot();
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

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::to_string(SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data)) + ":LogicalTime";
}

bool entityLogicalTimeEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQLogicalTimeType::equal(SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data1), SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data2));
}

bool entityLogicalTimeLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQLogicalTimeType::lessThan(SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data1), SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, data2));
}

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return to_string(*(BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data));
}

bool entityUUIDEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQUUIDType::equal((BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1), (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2));
}

bool entityUUIDLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQUUIDType::lessThan((BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1), (BSQUUID*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2));
}

std::string entityCryptoHashDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return SLPTR_LOAD_CONTENTS_AS(BSQCryptoHash, data).str() + ":Hash";
}

bool entityCryptoHashEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQCryptoHashType::equal((BSQCryptoHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1), (BSQCryptoHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2));
}

bool entityCryptoHashLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    return BSQCryptoHashType::lessThan((BSQCryptoHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data1), (BSQCryptoHash*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data2));
}

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return std::string("/") + *((BSQRegex*)SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data))->strversion + std::string("/");
}