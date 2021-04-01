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

struct BSQRegex
{
    std::wregex* regex;
};
