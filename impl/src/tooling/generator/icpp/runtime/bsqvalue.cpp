//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "environment.h"

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

    static BSQBool equalOperator(const BSQString& s1, const BSQString& s2);
    static BSQBool lessOperator(const BSQString& s1, const BSQString& s2);


void* BSQStringType::allocateStringKForSize(size_t k, wchar_t** dataptr)
{
    size_t osize = BSQStringReprType::getKReprSizeFor(k);
    void* res = nullptr;

    switch(osize)
    {
    case 4:
        res = (BSQStringKRepr<4>*)Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeStringKRepr4);
        break;
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
    *dataptr = (wchar_t*)((uint8_t*)res) + sizeof(BSQNat);
    return res;
}

BSQStringKRepr<4>* BSQStringType::boxInlineString(BSQInlineString istr)
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



