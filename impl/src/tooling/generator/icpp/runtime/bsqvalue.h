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

std::string entityNoneDisplay_impl(const BSQType* btype, void** data);

class BSQNoneType : public BSQEntityType
{
public:
    BSQNoneType() : BSQEntityType(BSQ_TYPE_ID_NONE, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNone)), {}, {}, entityNoneDisplay_impl, "NSCore::None", {}, {}, {}) {;}
    virtual ~BSQNoneType() {;}
};

////
//Bool
typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

std::string entityBoolDisplay_impl(const BSQType* btype, void** data);

class BSQBoolType : public BSQEntityType
{
public:
    BSQBoolType() : BSQEntityType(BSQ_TYPE_ID_BOOL, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBool)), {}, {}, entityBoolDisplay_impl, "NSCore::Bool", {}, {}, {}) {;}
    virtual ~BSQBoolType() {;}
};

////
//Nat
typedef uint64_t BSQNat;

std::string entityNatDisplay_impl(const BSQType* btype, void** data);

class BSQNatType : public BSQEntityType
{
public:
    BSQNatType() : BSQEntityType(BSQ_TYPE_ID_NAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNat)), {}, {}, entityNatDisplay_impl, "NSCore::Nat", {}, {}, {}) {;}
    virtual ~BSQNatType() {;}
};

////
//Int
typedef int64_t BSQInt;

std::string entityIntDisplay_impl(const BSQType* btype, void** data);

class BSQIntType : public BSQEntityType
{
public:
    BSQIntType() : BSQEntityType(BSQ_TYPE_ID_INT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQInt)), {}, {}, entityIntDisplay_impl, "NSCore::Int", {}, {}, {}) {;}
    virtual ~BSQIntType() {;}
};

////
//BigNat
typedef boost::multiprecision::checked_uint256_t BSQBigNat;

std::string entityBigNatDisplay_impl(const BSQType* btype, void** data);

class BSQBigNatType : public BSQEntityType
{
public:
    BSQBigNatType() : BSQEntityType(BSQ_TYPE_ID_BIGNAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), {}, {}, entityBigNatDisplay_impl, "NSCore::BigNat", {}, {}, {}) {;}
    virtual ~BSQBigNatType() {;}
};

////
//BigInt
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

std::string entityBigIntDisplay_impl(const BSQType* btype, void** data);

class BSQBigIntType : public BSQEntityType
{
public:
    BSQBigIntType() : BSQEntityType(BSQ_TYPE_ID_BIGINT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), {}, {}, entityBigIntDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
    virtual ~BSQBigIntType() {;}
};

////
//Float
typedef boost::multiprecision::cpp_bin_float_double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, void** data);

class BSQFloatType : public BSQEntityType
{
public:
    BSQFloatType() : BSQEntityType(BSQ_TYPE_ID_FLOAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQFloat)), {}, {}, entityFloatDisplay_impl, "NSCore::Float", {}, {}, {}) {;}
    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

std::string entityDecimalDisplay_impl(const BSQType* btype, void** data);

class BSQDecimalType : public BSQEntityType
{
public:
    BSQDecimalType() : BSQEntityType(BSQ_TYPE_ID_DECIMAL, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQDecimal)), {}, {}, entityDecimalDisplay_impl, "NSCore::Decimal", {}, {}, {}) {;}
    virtual ~BSQDecimalType() {;}
};

////
//Rational
struct BSQRational
{
    BSQBigInt numerator;
    BSQBigInt denominator;
};

std::string entityRationalDisplay_impl(const BSQType* btype, void** data);

class BSQRationalType : public BSQEntityType
{
public:
    BSQRationalType() : BSQEntityType(BSQ_TYPE_ID_RATIONAL, BSQTypeKind::Struct, BSQ_ALIGN_SIZE(sizeof(BSQRational)), {}, {}, entityRationalDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
    virtual ~BSQRationalType() {;}
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
