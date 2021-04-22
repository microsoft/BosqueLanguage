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

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityNoneEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityNoneLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNoneType : public BSQEntityType
{
public:
    BSQNoneType() : BSQEntityType(BSQ_TYPE_ID_NONE, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNone)), {}, {}, entityNoneEqual_impl, enityNoneLessThan_impl, entityNoneDisplay_impl, "NSCore::None", {}, {}, {}) {;}
    virtual ~BSQNoneType() {;}
};

////
//Bool
typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBoolEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityBoolLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBoolType : public BSQEntityType
{
public:
    BSQBoolType() : BSQEntityType(BSQ_TYPE_ID_BOOL, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBool)), {}, {}, entityBoolEqual_impl, enityBoolLessThan_impl, entityBoolDisplay_impl, "NSCore::Bool", {}, {}, {}) {;}
    virtual ~BSQBoolType() {;}

    inline static bool equal(BSQBool v1, BSQBool v2) { return v1 == v2; }
    inline static bool lessThan(BSQBool v1, BSQBool v2) { return !v1 & v2; }
};

////
//Nat
typedef uint64_t BSQNat;

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNatType : public BSQEntityType
{
public:
    BSQNatType() : BSQEntityType(BSQ_TYPE_ID_NAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNat)), {}, {}, entityNatEqual_impl, enityNatLessThan_impl, entityNatDisplay_impl, "NSCore::Nat", {}, {}, {}) {;}
    virtual ~BSQNatType() {;}

    inline static bool equal(BSQNat v1, BSQNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQNat v1, BSQNat v2) { return v1 < v2; }
};

////
//Int
typedef int64_t BSQInt;

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQIntType : public BSQEntityType
{
public:
    BSQIntType() : BSQEntityType(BSQ_TYPE_ID_INT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQInt)), {}, {}, entityIntEqual_impl, enityIntLessThan_impl, entityIntDisplay_impl, "NSCore::Int", {}, {}, {}) {;}
    virtual ~BSQIntType() {;}

    inline static bool equal(BSQInt v1, BSQInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQInt v1, BSQInt v2) { return v1 < v2; }
};

////
//BigNat
typedef boost::multiprecision::checked_uint256_t BSQBigNat;

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityBigNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigNatType : public BSQEntityType
{
public:
    BSQBigNatType() : BSQEntityType(BSQ_TYPE_ID_BIGNAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), {}, {}, entityBigNatEqual_impl, enityBigNatLessThan_impl, entityBigNatDisplay_impl, "NSCore::BigNat", {}, {}, {}) {;}
    virtual ~BSQBigNatType() {;}

    inline static bool equal(BSQBigNat v1, BSQBigNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigNat v1, BSQBigNat v2) { return v1 < v2; }
};

////
//BigInt
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityBigIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigIntType : public BSQEntityType
{
public:
    BSQBigIntType() : BSQEntityType(BSQ_TYPE_ID_BIGINT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), {}, {}, entityBigIntEqual_impl, enityBigIntLessThan_impl, entityBigIntDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
    virtual ~BSQBigIntType() {;}

    inline static bool equal(BSQBigInt v1, BSQBigInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigInt v1, BSQBigInt v2) { return v1 < v2; }
};

////
//Float
typedef boost::multiprecision::cpp_bin_float_double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQFloatType : public BSQEntityType
{
public:
    BSQFloatType() : BSQEntityType(BSQ_TYPE_ID_FLOAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQFloat)), {}, {}, entityFloatDisplay_impl, "NSCore::Float", {}, {}, {}) {;}
    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

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

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

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
        BSQInlineString istr = {len << 1, 0, 0, 0, 0, 0, 0, 0};
        assert(IS_INLINE_STRING(&istr.vals));

        std::copy(chars, chars + len, istr.vals + 1);
    }

    inline static size_t codePointCount(BSQInlineString istr)
    {
        return istr.vals[0] >> 1;
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

class BSQStringReprType : public BSQEntityType
{
public:
    static size_t getKReprSizeFor(size_t v);

    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, uint64_t gcptrcount, DisplayFP fpDisplay, std::string name) 
    : BSQEntityType(tid, BSQTypeKind::Ref, allocsize, gcptrcount, {}, {}, fpDisplay, name, {}, {}, {}) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual size_t codePointCount(void* repr) const = 0;
};

template <size_t k>
struct BSQStringKRepr
{
    BSQNat size;
    uint8_t elems[k];
};

template <size_t k>
std::string entityStringKReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

template <size_t k>
class BSQStringKReprType : public BSQStringReprType
{
public:
    BSQStringKReprType(DisplayFP fpDisplay) 
    : BSQStringReprType(BSQ_TYPE_ID_STRINGKREPR, BSQ_ALIGN_SIZE(sizeof(BSQStringKRepr<k>)), fpDisplay, "[Internal::StringKRepr]") 
    {;}

    virtual ~BSQStringKReprType() {;}

    virtual size_t codePointCount(void* repr) const override
    {
        return ((BSQStringKRepr<k>*)repr)->size;
    }
};
constexpr size_t g_kreprsizes[] = { 8, 16, 32, 64, 128, 256 };
constexpr size_t g_kreprcount = 6;

struct BSQStringSliceRepr
{
    void* srepr; //a krepr string
    size_t start;
    size_t end;
    void* parent; //dont gc ptr this so it is like a weak ref
};

std::string entityStringSliceReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQStringSliceReprType : public BSQStringReprType
{
public:
    BSQStringSliceReprType() 
    : BSQStringReprType(BSQ_TYPE_ID_STRINGSLICEREPR, BSQ_ALIGN_SIZE(sizeof(BSQStringSliceRepr)), 1, entityStringSliceReprDisplay_impl, "[Internal::StringSliceRepr]") 
    {;}

    virtual ~BSQStringSliceReprType() {;}

    virtual size_t codePointCount(void* repr) const override
    {
        auto srepr = (BSQStringSliceRepr*)repr;
        return (srepr->end - srepr->start);
    }
};

struct BSQStringConcatRepr
{
    void* srepr1;
    void* srepr2;
    size_t size;
    void* parent; //dont gc ptr this so it is like a weak ref
};

std::string entityStringConcatReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQStringConcatReprType : public BSQStringReprType
{
public:
    BSQStringConcatReprType() 
    : BSQStringReprType(BSQ_TYPE_ID_STRINGAPPENDREPR, BSQ_ALIGN_SIZE(sizeof(BSQStringConcatRepr)), 2, entityStringConcatReprDisplay_impl, "[Internal::StringConcatRepr]") 
    {;}

    virtual ~BSQStringConcatReprType() {;}

    virtual size_t codePointCount(void* repr) const override
    {
        return ((BSQStringConcatRepr*)repr)->size;
    }
};

class BSQStringReprIterator
{
public:
    void* activeparent;
    uint8_t* current;

    void increment();
    void decrement();
};

struct BSQString
{
    union { void* u_data; BSQInlineString u_inlineString; };
};
constexpr BSQString g_emptyString = {0};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQEntityType
{
private:
    static void* allocateStringKForSize(size_t k, uint8_t** dataptr);
    static BSQStringKRepr<8>* boxInlineString(BSQInlineString istr);

public:
    BSQStringReprIterator begin(BSQString s) const
    {

    }

    BSQStringReprIterator end(BSQString s) const
    {

    }

    inline static bool equalOperator(BSQString v1, BSQString v2)
    {

    }

    inline static bool lessOperator(BSQString v1, BSQString v2)
    {

    }

    size_t codePointCount(BSQString s) const
    {
        if(IS_INLINE_STRING(&s))
        {
            return BSQInlineString::codePointCount(s.u_inlineString);
        }
        else
        {
            return GET_TYPE_META_DATA_AS(BSQStringReprType, s.u_data)->codePointCount(s.u_data);
        }
    }

    inline BSQBool empty(BSQString s) const
    {
        s.u_data == nullptr;
    }

    BSQString concat2(BSQString s1, BSQString s2) const;
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
