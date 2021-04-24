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

template <size_t k>
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

bool iteratorIsValid(BSQStringIterator* iter)
{
    iter->cbuff != nullptr;
}

uint8_t iteratorGet(BSQStringIterator* iter)
{
    return iter->cbuff[iter->cpos];
}

void initializeStringIterStart(BSQStringIterator* iter, void* activeparent, const BSQStringReprType* reprtype, void* srepr)
{
    if(reprtype->tid == BSQ_TYPE_ID_STRINGKREPR)
    {
        iter->activeparent = activeparent;
        iter->cbuff = BSQStringKReprTypeAbstract::getCodePointData(srepr);

        const BSQStringReprType* parenttype = (activeparent != nullptr) ? GET_TYPE_META_DATA_AS(BSQStringReprType, activeparent) : nullptr;
        if(parenttype != nullptr && parenttype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
        {
            auto slicerepr = (BSQStringSliceRepr*)activeparent;
            iter->minpos = slicerepr->start;
            iter->cpos = slicerepr->start;
            iter->maxpos = slicerepr->end;
        }
        else
        {
            iter->minpos = 0;
            iter->cpos = 0;
            iter->maxpos = BSQStringKReprTypeAbstract::getCodePointCount(srepr);
        }
    }
    else if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
    {
        auto slicerepr = (BSQStringSliceRepr*)srepr;
        initializeStringIterStart(iter, srepr, GET_TYPE_META_DATA_AS(BSQStringReprType, slicerepr->srepr), slicerepr->srepr);
    }
    else
    {
        auto concatrepr = (BSQStringConcatRepr*)srepr;
        initializeStringIterStart(iter, srepr, GET_TYPE_META_DATA_AS(BSQStringReprType, concatrepr->srepr1), concatrepr->srepr1);
    }
}

void incrementStringIterator_ucharSlow(BSQStringIterator* iter)
{
    if(iter->activeparent == nullptr)
    {
        iter->cbuff = nullptr;
    }
    else
    {
        const BSQStringReprType* reprtype = GET_TYPE_META_DATA_AS(BSQStringReprType, iter->activeparent);
        void* srepr = nullptr;
        while(iter->activeparent != nullptr)
        {
            if(reprtype->tid == BSQ_TYPE_ID_STRINGSLICEREPR)
            {
                iter->activeparent = ((BSQStringSliceRepr*)iter->activeparent)->parent;
            }
            else
            {
                xxxx;
                
                srepr = ;
            }
        }

        if(iter->activeparent != nullptr)
        {
            initializeStringIterStart(iter, iter->activeparent, GET_TYPE_META_DATA_AS(BSQStringReprType, srepr), srepr);
        }
    }
}

void incrementStringIterator_uchar(BSQStringIterator* iter)
{
    if(iter->cpos < iter->maxpos)
    {
        iter->cpos++;
    }
    else
    {
        incrementStringIterator_ucharSlow(iter);
    }
}

void decrementStringIterator_ucharSlow(BSQStringIterator* iter)
{
    xxxx;
}

void decrementStringIterator_uchar(BSQStringIterator* iter)
{
    if(iter->minpos < iter->cpos)
    {
        iter->cpos--;
    }
    else
    {
        incrementStringIterator_ucharSlow(iter);
    }
}

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    xxxx;
}

bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    xxxx;
}

bool enityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2)
{
    xxxx;
}

////
//Define some safe constants for memory allocation during various builtin operations
#define SAFE_STRING_CONCAT_SIZE 128

size_t BSQStringReprType::getKReprSizeFor(size_t v)
{
    size_t i = g_kreprcount - 1;
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

void BSQStringReprIterator::incrementTree()
{
    xxxx;
}

void BSQStringReprIterator::initialize(BSQStringReprIterator& iv, void* repr)
{
    xxxx;
}

void BSQStringReprIterator::initializePosition(BSQStringReprIterator& iv, void* repr, uint64_t pos)
{
    xxxx;
}

void* BSQStringType::allocateStringKForSize(size_t k, uint8_t** dataptr)
{
    size_t osize = BSQStringReprType::getKReprSizeFor(k);
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
    auto res = (BSQStringKRepr<4>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr4);
    res->size = BSQInlineString::length(istr);
    std::copy(BSQInlineString::vals(istr), BSQInlineString::valsend(istr), res->elems);

    return res;
}

BSQBool BSQStringType::equalOperator(const BSQString& s1, const BSQString& s2)
{
    xxxx;
}

BSQBool BSQStringType::lessOperator(const BSQString& s1, const BSQString& s2)
{
    xxxx;
}

BSQString BSQStringType::concat2(BSQString s1, BSQString s2) const
{
    auto s1size = this->length(s1);
    auto s2size = this->length(s2);

    if(s1size == 0 & s2size == 0) 
    {
        g_emptyString;
    }
    else if(s1size == 0) 
    {
        s2;
    }
    else if(s2size == 0) 
    {
        s1;
    }
    else 
    {
        Allocator::GlobalAllocator.ensureSpace(SAFE_STRING_CONCAT_SIZE);

        void* lhs = IS_INLINE_STRING(s1) ? BSQStringType::boxInlineString(s1.u_inlineString) : s1.data;
        void* rhs = IS_INLINE_STRING(s2) ? BSQStringType::boxInlineString(s2.u_inlineString) : s2.data;
        BSQStringConcatRepr* cct = (BSQStringConcatRepr*)Allocator::GlobalAllocator.allocateSafe(Environment::g_typeStringConcatRepr->allocsize, Environment::g_typeStringConcatRepr);
        cct->size = s1size + s2size;
        cct->srepr1 = lhs;
        cct->srepr2 = rhs;

        return {cct, s1size + s2size};
    }
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

BSQString BSQStringType::slice(BSQString s, BSQNat start, BSQNat end)
{
            if(start == end) {
            String::g_emptystr;
        }
        else {
            let repr = s.data;
            if(repr === none) {
                return String#{none, InlineString::slice(s.istr, start, end)};
            }
            else {
                return String::s_sliceRepr[recursive](s.data, start, end);
            }
        }
}

BSQNat BSQStringType::indexOf(BSQString s, BSQString oftr)
{
    xxxx;
}



