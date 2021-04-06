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
    wchar_t vals[4];

    static BSQNat length(const BSQInlineString& istr)
    {
        return (BSQNat)istr.vals[0];
    }

    static wchar_t* vals(BSQInlineString& istr)
    {
        return istr.vals + 1;
    }
};
constexpr BSQInlineString g_emptyInlineString = {0};

class BSQStringReprType : public BSQEntityType
{
public:
    virtual BSQNat length(void* repr) const = 0;

    virtual wchar_t getAt(void* repr, BSQNat i) = 0;
    virtual uint64_t indexof();
};

template <size_t k>
struct BSQStringKRepr
{
    BSQNat size;
    wchar_t elems[k];

    static void flattenInlineString(xxxx)
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

#define IS_INLINE_STRING(S) ((S)->sdata == BSQNoneHeapValue)

struct BSQString
{
    void* data;
    BSQNat size;

    static BSQBool equalOperator(const BSQString& s1, const BSQString& s2);
    static BSQBool lessOperator(const BSQString& s1, const BSQString& s2);

    static BSQNat count(const BSQString& s);

    inline static BSQBool equalOperator(StorageLocationPtr s1, StorageLocationPtr s2)
    {
        return equalOperator(SLPTR_LOAD_CONTENTS_AS(BSQString, s1), SLPTR_LOAD_CONTENTS_AS(BSQString, s2));
    }

    inline static BSQBool lessOperator(StorageLocationPtr s1, StorageLocationPtr s2)
    {
        return lessOperator(SLPTR_LOAD_CONTENTS_AS(BSQString, s1), SLPTR_LOAD_CONTENTS_AS(BSQString, s2));
    }

    inline static BSQNat count(StorageLocationPtr s)
    {
        return count(SLPTR_LOAD_CONTENTS_AS(BSQString, s));
    }
};

class BSQStringType : public BSQEntityType
{
    xxxx;
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
