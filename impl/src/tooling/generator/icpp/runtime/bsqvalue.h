//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>

////
//Primitive value representations

class BSQNoneType : public BSQEntityType
{
    xxxx;
};

struct BSQNone
{
    uint64_t emptydata;
};

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

typedef uint64_t BSQNat;
typedef int64_t BSQInt;

typedef boost::multiprecision::checked_uint256_t BSQBigNat;
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

typedef boost::multiprecision::cpp_bin_float_double BSQFloat;
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

struct BSQRational
{
    BSQBigInt numerator;
    BSQBigInt denominator;
};

#define IS_INLINE_STRING(S) (((uintptr_t)(S->data) & BSQ_MEM_ALIGNMENT_MASK) == 0)

class BSQStringType : public BSQEntityType
{
public:
    //TODO: should be a union of the data repers we care about -- 
    virtual BSQNat getLength(void* data) const = 0;
};

struct BSQString
{
    void* data;

    inline static void initializeInline(size_t count, const wchar_t* chars, BSQString* into)
    {
        
        BSQStringInlineContents::fromchars(chars, chars + count, (BSQStringInlineContents*)into->data);
    }

    template <uint16_t k>
    static void initializeFlatKnown(const wchar_t* chars, BSQString* into)
    {
        static_assert(k <= 256, "Cant overflow max mem and must match type options in bsqtype");

        BSQStringFlatContents<k>* s = (BSQStringFlatContents<k>*)Allocator::GlobalAllocator.allocateDynamic(BSQStringEntityTypeFlatContents<k>);
        s->length = k;
        GC_MEM_COPY(s->data, chars, count);

        into->data = s;
    }

    static void initializeFlat(size_t count, const wchar_t* chars, BSQString* into)
    {
        if(count < 8)
        {
            initializeFlatKnown<8>(chars, into);
        }
        else if(count < 16)
        {
            initializeFlatKnown<16>(chars, into);
        }
        else if(count < 32)
        {
            initializeFlatKnown<32>(chars, into);
        }
        else if(count < 64)
        {
            initializeFlatKnown<64>(chars, into);
        }
        else if(count < 128)
        {
            initializeFlatKnown<128>(chars, into);
        }
        else
        {
            initializeFlatKnown<256>(chars, into);
        }
    }

    inline BSQNat count() const
    {
        if(this->data == nullptr)
        {
            return 0;
        }
        else if(IS_INLINE_STRING(this))
        {
            return ((BSQStringInlineContents*)this->data)->data[3];
        }
        else
        {
            void* sobj = *((void**)this->data);
            return ((BSQStringEntityType*)GET_TYPE_META_DATA(sobj))->getLength(sobj);
        }
    }
};

constexpr BSQString EmptyString = {nullptr};

struct BSQRegex
{
    std::wregex* regex;
};
