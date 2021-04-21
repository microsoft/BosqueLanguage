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
#include <boost/math/special_functions/fpclassify.hpp>

////
//Primitive value representations

////
//None
typedef uint64_t BSQNone;
#define BSQNoneValue 0

typedef void* BSQNoneHeap;
#define BSQNoneHeapValue nullptr

class BSQNoneType : public BSQEntityType
{
    xxxx;
};

////
//Bool
typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

class BSQBoolType : public BSQEntityType
{
    xxxx;
};

////
//Nat
typedef uint64_t BSQNat;

class BSQNatType : public BSQEntityType
{
    xxxx;
};

////
//Int
typedef int64_t BSQInt;

class BSQIntType : public BSQEntityType
{
    xxxx;
};

////
//BigNat
typedef boost::multiprecision::checked_uint256_t BSQBigNat;

class BSQBigNatType : public BSQEntityType
{
    xxxx;
};

////
//BigInt
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

class BSQBigIntType : public BSQEntityType
{
    xxxx;
};

////
//Float
typedef boost::multiprecision::cpp_bin_float_double BSQFloat;

class BSQFloatType : public BSQEntityType
{
    xxxx;
};

////
//Decimal
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

class BSQDecimalType : public BSQEntityType
{
    xxxx;
};

////
//Rational
struct BSQRational
{
    BSQBigInt numerator;
    BSQBigInt denominator;
};

class BSQRationalType : public BSQEntityType
{
    xxxx;
};

////
//String
struct BSQInlineString
{
    uint8_t vals[8];

    inline static BSQInlineString create(const uint8_t* chars, size_t len)
    {
        BSQInlineString istr = {len, 0, 0, 0, 0, 0, 0, 0};
        std::copy(chars, chars + len, istr.vals + 1);
    }

    inline static BSQNat length(BSQInlineString istr)
    {
        return (BSQNat)istr.vals[0];
    }

    inline static uint8_t* vals(BSQInlineString istr)
    {
        return istr.vals + 1;
    }

    inline static uint8_t* valsend(BSQInlineString istr)
    {
        return istr.vals + 1 + istr.vals[0];
    }
};
constexpr BSQInlineString g_emptyInlineString = {0};

enum class BSQStringReprTypeTag
{
    ReprK,
    Concat,
    Slice
};

class BSQStringReprType : public BSQEntityType
{
public:
    BSQStringReprTypeTag tag;

    virtual BSQNat length(void* repr) const = 0;

    static size_t getKReprSizeFor(size_t v);
};

template <size_t k>
struct BSQStringKRepr
{
    BSQNat size;
    uint8_t elems[k];
};

template <size_t k>
class BSQStringKReprType : public BSQStringReprType
{
public:
    virtual BSQNat length(void* repr) const override
    {
        return ((BSQStringKRepr<k>*)repr)->size;
    }
};
constexpr size_t g_kreprsizes[] = { 8, 16, 32, 64, 128, 256 };
constexpr size_t g_kreprcount = 6;

struct BSQStringSliceRepr
{
    void* srepr;
    BSQNat start;
    BSQNat end;
};

class BSQStringSliceReprType : public BSQStringReprType
{
public:
    virtual BSQNat length(void* repr) const override
    {
        auto srepr = (BSQStringSliceRepr*)repr;
        return (srepr->end - srepr->start);
    }
};

struct BSQStringConcatRepr
{
    void* srepr1;
    void* srepr2;
    BSQNat size;
};

class BSQStringConcatReprType : public BSQStringReprType
{
public:
    virtual BSQNat length(void* repr) const override
    {
        return ((BSQStringConcatRepr*)repr)->size;
    }
};

class BSQStringReprIterator
{
public:
    std::stack<void*> parents;
    wchar_t* current;
    wchar_t* currentLimit;

    uint64_t pos;

    inline bool done() const
    {
        return this->current == nullptr;
    }

    void incrementTree();
    inline void increment()
    {
        this->current++;
        this->pos++;
        if(this->current == this->currentLimit)
        {
            this->incrementTree();
        }
    }
    
    static void initialize(BSQStringReprIterator& iv, void* repr);
    static void initializePosition(BSQStringReprIterator& iv, void* repr, uint64_t pos);
};

#define IS_INLINE_STRING(S) ((S).data == BSQNoneHeapValue)

struct BSQString
{
    void* data;
    union { BSQNat u_size; BSQInlineString u_inlineString; };
};
constexpr BSQString g_emptyString = {0};

class BSQStringType : public BSQEntityType
{
private:
    static void* allocateStringKForSize(size_t k, uint8_t** dataptr);
    static BSQStringKRepr<8>* boxInlineString(BSQInlineString istr);

public:
    static BSQBool equalOperator(const BSQString& s1, const BSQString& s2);
    static BSQBool lessOperator(const BSQString& s1, const BSQString& s2);

    inline static BSQBool equalOperator(StorageLocationPtr s1, StorageLocationPtr s2)
    {
        return equalOperator(SLPTR_LOAD_CONTENTS_AS(BSQString, s1), SLPTR_LOAD_CONTENTS_AS(BSQString, s2));
    }

    inline static BSQBool lessOperator(StorageLocationPtr s1, StorageLocationPtr s2)
    {
        return lessOperator(SLPTR_LOAD_CONTENTS_AS(BSQString, s1), SLPTR_LOAD_CONTENTS_AS(BSQString, s2));
    }

    inline BSQNat length(BSQString s) const
    {
        if(IS_INLINE_STRING(s))
        {
            return BSQInlineString::length(s.u_inlineString);
        }
        else
        {
            return s.u_size;
        }
    }

    BSQString concat2(BSQString s1, BSQString s2) const;

    BSQString sliceRepr(void* repr, BSQNat start, BSQNat end);
    BSQString slice(BSQString s, BSQNat start, BSQNat end);
    BSQNat indexOf(BSQString s, BSQString oftr);
};

////
//Regex

struct BSQRegex
{
    std::wregex* regex;
};

class BSQRegexType : public BSQEntityType
{
    xxxx;
};
