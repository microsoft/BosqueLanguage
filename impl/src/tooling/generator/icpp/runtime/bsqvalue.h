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
    BSQNoneType() : BSQEntityType(BSQ_TYPE_ID_NONE, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNone)), {}, entityNoneEqual_impl, enityNoneLessThan_impl, entityNoneDisplay_impl, "NSCore::None", {}, {}, {}) {;}
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
    BSQBoolType() : BSQEntityType(BSQ_TYPE_ID_BOOL, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBool)), {}, entityBoolEqual_impl, enityBoolLessThan_impl, entityBoolDisplay_impl, "NSCore::Bool", {}, {}, {}) {;}
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
    BSQNatType() : BSQEntityType(BSQ_TYPE_ID_NAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQNat)), {}, entityNatEqual_impl, enityNatLessThan_impl, entityNatDisplay_impl, "NSCore::Nat", {}, {}, {}) {;}
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
    BSQIntType() : BSQEntityType(BSQ_TYPE_ID_INT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQInt)), {}, entityIntEqual_impl, enityIntLessThan_impl, entityIntDisplay_impl, "NSCore::Int", {}, {}, {}) {;}
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
    BSQBigNatType() : BSQEntityType(BSQ_TYPE_ID_BIGNAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), {}, entityBigNatEqual_impl, enityBigNatLessThan_impl, entityBigNatDisplay_impl, "NSCore::BigNat", {}, {}, {}) {;}
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
    BSQBigIntType() : BSQEntityType(BSQ_TYPE_ID_BIGINT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), {}, entityBigIntEqual_impl, enityBigIntLessThan_impl, entityBigIntDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
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
    BSQFloatType() : BSQEntityType(BSQ_TYPE_ID_FLOAT, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQFloat)), {}, entityFloatDisplay_impl, "NSCore::Float", {}, {}, {}) {;}
    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQDecimalType : public BSQEntityType
{
public:
    BSQDecimalType() : BSQEntityType(BSQ_TYPE_ID_DECIMAL, BSQTypeKind::Register, BSQ_ALIGN_SIZE(sizeof(BSQDecimal)), {}, entityDecimalDisplay_impl, "NSCore::Decimal", {}, {}, {}) {;}
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
    BSQRationalType() : BSQEntityType(BSQ_TYPE_ID_RATIONAL, BSQTypeKind::Struct, BSQ_ALIGN_SIZE(sizeof(BSQRational)), {}, entityRationalDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
    virtual ~BSQRationalType() {;}
};

////
//String
struct BSQInlineString
{
    uint8_t utf8bytes[8];

    inline static BSQInlineString create(const uint8_t* chars, size_t len)
    {
        BSQInlineString istr = {len << 1, 0, 0, 0, 0, 0, 0, 0};
        assert(IS_INLINE_STRING(&istr));

        std::copy(chars, chars + len, istr.utf8bytes + 1);
    }

    inline static BSQInlineString create2(const uint8_t* chars1, size_t len1, const uint8_t* chars2, size_t len2)
    {
        BSQInlineString istr = {(len1 + len2) << 1, 0, 0, 0, 0, 0, 0, 0};
        assert(IS_INLINE_STRING(&istr));

        std::copy(chars1, chars1 + len1, istr.utf8bytes + 1);
        std::copy(chars2, chars2 + len2, istr.utf8bytes + 1 + len1);
    }

    inline static size_t utf8ByteCount(BSQInlineString istr)
    {
        return istr.utf8bytes[0] >> 1;
    }

    inline static uint8_t* utf8Bytes(BSQInlineString istr)
    {
        return istr.utf8bytes + 1;
    }

    inline static uint8_t* utf8BytesEnd(BSQInlineString istr)
    {
        return istr.utf8bytes + 1 + istr.utf8bytes[0];
    }
};
constexpr BSQInlineString g_emptyInlineString = {0};

class BSQStringReprType : public BSQEntityType
{
public:
    static size_t getKReprSizeFor(size_t v);

    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, uint64_t gcptrcount, DisplayFP fpDisplay, std::string name) 
    : BSQEntityType(tid, BSQTypeKind::Ref, allocsize, gcptrcount, {}, fpDisplay, name, {}, {}, {}) 
    {;}

    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, DisplayFP fpDisplay, std::string name) 
    : BSQEntityType(tid, BSQTypeKind::Ref, allocsize, {}, fpDisplay, name, {}, {}, {}) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual size_t utf8ByteCount(void* repr) const = 0;
};

template <size_t k>
struct BSQStringKRepr
{
    size_t size;
    uint8_t utf8bytes[k];
};

template <size_t k>
std::string entityStringKReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQStringKReprTypeAbstract : public BSQStringReprType
{
public:
    BSQStringKReprTypeAbstract(uint64_t allocsize, DisplayFP fpDisplay, std::string name) 
    : BSQStringReprType(BSQ_TYPE_ID_STRINGKREPR, allocsize, fpDisplay, name) 
    {;}

    virtual ~BSQStringKReprTypeAbstract() {;}

    static size_t getUTF8ByteCount(void* repr)
    {
        return *((size_t*)repr);
    }

    static uint8_t* getUTF8Bytes(void* repr)
    {
        return ((uint8_t*)repr) + sizeof(size_t);
    }

    virtual size_t utf8ByteCount(void* repr) const override
    {
        return BSQStringKReprTypeAbstract::getUTF8ByteCount(repr);
    }
};

template <size_t k>
class BSQStringKReprType : public BSQStringKReprTypeAbstract
{
public:
    BSQStringKReprType(DisplayFP fpDisplay) 
    : BSQStringKReprTypeAbstract(BSQ_TYPE_ID_STRINGKREPR, BSQ_ALIGN_SIZE(sizeof(BSQStringKRepr<k>)), fpDisplay, "[Internal::StringKRepr]") 
    {;}

    virtual ~BSQStringKReprType() {;}
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

    virtual size_t utf8ByteCount(void* repr) const override
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

    virtual size_t utf8ByteCount(void* repr) const override
    {
        return ((BSQStringConcatRepr*)repr)->size;
    }
};

struct BSQString
{
    union { void* u_data; BSQInlineString u_inlineString; };
};
constexpr BSQString g_emptyString = {0};

struct BSQStringIterator
{
    BSQString str;
    xxxx; //put in actual index in string
    void* activeparent;
    void* activerepr;
    uint8_t* cbuff;
    uint16_t cpos;
    uint16_t minpos;
    uint16_t maxpos;
};

std::string entityStringBSQStringIteratorDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool iteratorIsValid(const BSQStringIterator* iter);
uint8_t iteratorGetUTF8Byte(const BSQStringIterator* iter);
void incrementStringIterator_utf8byte(BSQStringIterator* iter);
void decrementStringIterator_utf8byte(BSQStringIterator* iter);

uint32_t iteratorGetCodePoint(BSQStringIterator* iter);
void incrementStringIterator_codePoint(BSQStringIterator* iter);
void decrementStringIterator_codePoint(BSQStringIterator* iter);

bool iteratorIsLess(const BSQStringIterator* iter1, const BSQStringIterator* iter2);

class BSQStringIteratorType : public BSQEntityType
{
public:
    BSQStringIteratorType() 
    : BSQEntityType(BSQ_TYPE_ID_STRINGITERATOR, BSQTypeKind::Struct, BSQ_ALIGN_SIZE(sizeof(BSQStringIterator)), "3", {}, entityStringBSQStringIteratorDisplay_impl, "NSCore::StringPos", {}, {}, {})
    {;}

    virtual ~BSQStringIteratorType() {;}
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool enityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQEntityType
{
private:
    static void* allocateStringKForSize(size_t k, uint8_t** dataptr);
    static BSQStringKRepr<8>* boxInlineString(BSQInlineString istr);

public:
    static void initializeIteratorBegin(BSQStringIterator* iter, BSQString str);
    static void initializeIteratorEnd(BSQStringIterator* iter, BSQString str);

    static bool equal(BSQString v1, BSQString v2);
    static bool lessThan(BSQString v1, BSQString v2);

    static size_t utf8ByteCount(BSQString s)
    {
        if(IS_INLINE_STRING(&s))
        {
            return BSQInlineString::utf8ByteCount(s.u_inlineString);
        }
        else
        {
            return GET_TYPE_META_DATA_AS(BSQStringReprType, s.u_data)->utf8ByteCount(s.u_data);
        }
    }

    static inline BSQBool empty(BSQString s)
    {
        s.u_data == nullptr;
    }

    static BSQString concat2(StorageLocationPtr s1, StorageLocationPtr s2);
    static BSQString slice(StorageLocationPtr str, StorageLocationPtr startpos, StorageLocationPtr endpos);
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
