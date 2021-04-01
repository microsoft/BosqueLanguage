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

////
//None
class BSQNoneType : public BSQEntityType
{
    xxxx;
};

typedef uint64_t BSQNone;
#define BSQNoneValue 0

typedef void* BSQNoneHeap;
#define BSQNoneHeapValue nullptr

////
//Bool
class BSQBoolType : public BSQEntityType
{
    xxxx;
};

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

////
//Nat
class BSQNatType : public BSQEntityType
{
    xxxx;
};
typedef uint64_t BSQNat;

////
//Int
class BSQIntType : public BSQEntityType
{
    xxxx;
};
typedef int64_t BSQInt;

////
//BigNat
class BSQBigNatType : public BSQEntityType
{
    xxxx;
};
typedef boost::multiprecision::checked_uint256_t BSQBigNat;

////
//BigInt
class BSQBigIntType : public BSQEntityType
{
    xxxx;
};
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

////
//Float
class BSQFloatType : public BSQEntityType
{
    xxxx;
};
typedef boost::multiprecision::cpp_bin_float_double BSQFloat;

////
//Decimal
class BSQDecimalType : public BSQEntityType
{
    xxxx;
};
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

////
//Rational
class BSQRationalType : public BSQEntityType
{
    xxxx;
};
struct BSQRational
{
    BSQBigInt numerator;
    BSQBigInt denominator;
};

////
//String
class BSQStringType : public BSQEntityType
{
    xxxx;
};

#define IS_INLINE_STRING(S) ((S)->sdata == BSQNoneHeapValue)

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
