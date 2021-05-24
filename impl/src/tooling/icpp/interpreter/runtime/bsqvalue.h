//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "../core/bsqmemory.h"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/math/special_functions/fpclassify.hpp>

#include <boost/uuid/uuid.hpp>

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
bool entityNoneLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNoneType : public BSQEntityAbstractType
{
public:
    BSQNoneType() : BSQEntityAbstractType(BSQ_TYPE_ID_NONE, BSQTypeKind::Register, { sizeof(BSQNone), sizeof(BSQNone), sizeof(BSQNone), "1" }, {}, entityNoneEqual_impl, entityNoneLessThan_impl, entityNoneDisplay_impl, "NSCore::None", {}, {}, {}) {;}
    virtual ~BSQNoneType() {;}
};

////
//Bool

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBoolEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBoolLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBoolType : public BSQEntityAbstractType
{
public:
    BSQBoolType() : BSQEntityAbstractType(BSQ_TYPE_ID_BOOL, BSQTypeKind::Register, { sizeof(BSQNone), sizeof(BSQNone), sizeof(BSQBool), "1" }, {}, entityBoolEqual_impl, entityBoolLessThan_impl, entityBoolDisplay_impl, "NSCore::Bool", {}, {}, {}) {;}
    virtual ~BSQBoolType() {;}

    inline static bool equal(BSQBool v1, BSQBool v2) { return v1 == v2; }
    inline static bool lessThan(BSQBool v1, BSQBool v2) { return (!v1) & v2; }
};

////
//Nat
typedef uint64_t BSQNat;

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNatType : public BSQEntityAbstractType
{
public:
    BSQNatType() : BSQEntityAbstractType(BSQ_TYPE_ID_NAT, BSQTypeKind::Register, { sizeof(BSQNat), sizeof(BSQNat), sizeof(BSQNat), "1" }, {}, entityNatEqual_impl, entityNatLessThan_impl, entityNatDisplay_impl, "NSCore::Nat", {}, {}, {}) {;}
    virtual ~BSQNatType() {;}

    inline static bool equal(BSQNat v1, BSQNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQNat v1, BSQNat v2) { return v1 < v2; }
};

////
//Int
typedef int64_t BSQInt;

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQIntType : public BSQEntityAbstractType
{
public:
    BSQIntType() : BSQEntityAbstractType(BSQ_TYPE_ID_INT, BSQTypeKind::Register, { sizeof(BSQInt), sizeof(BSQInt), sizeof(BSQInt), "1" }, {}, entityIntEqual_impl, entityIntLessThan_impl, entityIntDisplay_impl, "NSCore::Int", {}, {}, {}) {;}
    virtual ~BSQIntType() {;}

    inline static bool equal(BSQInt v1, BSQInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQInt v1, BSQInt v2) { return v1 < v2; }
};

////
//BigNat
typedef boost::multiprecision::cpp_int BSQBigNat;

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBigNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigNatType : public BSQEntityAbstractType
{
public:
    BSQBigNatType() : BSQEntityType(BSQ_TYPE_ID_BIGNAT, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), BSQ_ALIGN_SIZE(sizeof(BSQBigNat)), "1" }, {}, entityBigNatEqual_impl, entityBigNatLessThan_impl, entityBigNatDisplay_impl, "NSCore::BigNat", {}, {}, {}) {;}
    virtual ~BSQBigNatType() {;}

    inline static bool equal(BSQBigNat v1, BSQBigNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigNat v1, BSQBigNat v2) { return v1 < v2; }
};

////
//BigInt
typedef boost::multiprecision::cpp_int BSQBigInt;

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBigIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigIntType : public BSQEntityType
{
public:
    BSQBigIntType() : BSQEntityType(BSQ_TYPE_ID_BIGINT, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), BSQ_ALIGN_SIZE(sizeof(BSQBigInt)), "1" }, {}, entityBigIntEqual_impl, entityBigIntLessThan_impl, entityBigIntDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
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
    BSQFloatType() : BSQEntityType(BSQ_TYPE_ID_FLOAT, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQFloat)), BSQ_ALIGN_SIZE(sizeof(BSQFloat)), BSQ_ALIGN_SIZE(sizeof(BSQFloat)), "1" }, {}, entityFloatDisplay_impl, "NSCore::Float", {}, {}, {}) {;}
    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQDecimalType : public BSQEntityType
{
public:
    BSQDecimalType() : BSQEntityType(BSQ_TYPE_ID_DECIMAL, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQDecimal)), BSQ_ALIGN_SIZE(sizeof(BSQDecimal)), BSQ_ALIGN_SIZE(sizeof(BSQDecimal)), "11" }, {}, entityDecimalDisplay_impl, "NSCore::Decimal", {}, {}, {}) {;}
    virtual ~BSQDecimalType() {;}
};

////
//Rational
struct BSQRational
{
    boost::multiprecision::int128_t numerator;
    uint64_t denominator;
};

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRationalType : public BSQEntityType
{
public:
    BSQRationalType() : BSQEntityType(BSQ_TYPE_ID_RATIONAL, BSQTypeKind::Struct, {BSQ_ALIGN_SIZE(sizeof(BSQRational)), BSQ_ALIGN_SIZE(sizeof(BSQRational)), BSQ_ALIGN_SIZE(sizeof(BSQRational)), "111" }, {}, entityRationalDisplay_impl, "NSCore::BigInt", {}, {}, {}) {;}
    virtual ~BSQRationalType() {;}
};

////
//String
struct BSQStringIterator; //forward decl

struct BSQInlineString
{
    uint8_t utf8bytes[16];

    inline static BSQInlineString create(const uint8_t* chars, uint64_t len)
    {
        BSQInlineString istr = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (uint8_t)len};
        assert(IS_INLINE_STRING(&istr));

        std::copy(chars, chars + len, istr.utf8bytes);
        return istr;
    }

    inline static uint64_t utf8ByteCount(const BSQInlineString& istr)
    {
        return istr.utf8bytes[15];
    }

    static void utf8ByteCount_Initialize(BSQInlineString& istr, uint64_t len)
    {
        istr.utf8bytes[15] = (uint8_t)len;
    }

    inline static uint8_t* utf8Bytes(BSQInlineString& istr)
    {
        return istr.utf8bytes;
    }

    inline static const uint8_t* utf8Bytes(const BSQInlineString& istr)
    {
        return istr.utf8bytes;
    }

    inline static uint8_t* utf8BytesEnd(BSQInlineString& istr)
    {
        return istr.utf8bytes + istr.utf8bytes[15];
    }

    inline static const uint8_t* utf8BytesEnd(const BSQInlineString& istr)
    {
        return istr.utf8bytes + istr.utf8bytes[15];
    }
};
constexpr BSQInlineString g_emptyInlineString = {0};

std::string entityStringReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQStringReprType : public BSQEntityType
{
public:
    static uint64_t getKReprSizeFor(uint64_t v);

    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, uint64_t gcptrcount, std::string name) 
    : BSQEntityType(tid, BSQTypeKind::Ref, { allocsize, allocsize, allocsize, "2" }, gcptrcount, {}, entityStringReprDisplay_impl, name, {}, {}, {}) 
    {;}

    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, std::string name) 
    : BSQEntityType(tid, BSQTypeKind::Ref, { allocsize, allocsize, allocsize, "2" }, {}, entityStringReprDisplay_impl, name, {}, {}, {}) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const = 0;
    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const = 0;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const = 0;
};

template <uint64_t k>
struct BSQStringKRepr
{
    uint16_t size;
    uint8_t utf8bytes[k];
};

class BSQStringKReprTypeAbstract : public BSQStringReprType
{
public:
    BSQStringKReprTypeAbstract(uint64_t allocsize, std::string name) 
    : BSQStringReprType(BSQ_TYPE_ID_STRINGREPR, allocsize, name) 
    {;}

    virtual ~BSQStringKReprTypeAbstract() {;}

    static uint64_t getUTF8ByteCount(void* repr)
    {
        return *((uint16_t*)repr);
    }

    static uint8_t* getUTF8Bytes(void* repr)
    {
        return ((uint8_t*)repr) + sizeof(uint16_t);
    }

    virtual uint64_t utf8ByteCount(void* repr) const override
    {
        return BSQStringKReprTypeAbstract::getUTF8ByteCount(repr);
    }

    static void initializeIterPositionWSlice(BSQStringIterator* iter, void* data, int64_t minpos, int64_t maxpos, int64_t pos);

    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};

template <uint64_t k>
class BSQStringKReprType : public BSQStringKReprTypeAbstract
{
public:
    BSQStringKReprType() 
    : BSQStringKReprTypeAbstract(BSQ_ALIGN_SIZE(sizeof(BSQStringKRepr<k>)), "[Internal::StringKRepr]") 
    {;}

    virtual ~BSQStringKReprType() {;}
};

struct BSQStringSliceRepr
{
    void* srepr; //a krepr string
    uint64_t start;
    uint64_t end;
};

class BSQStringSliceReprType : public BSQStringReprType
{
public:
    BSQStringSliceReprType() 
    : BSQStringReprType(BSQ_ALIGN_SIZE(sizeof(BSQStringSliceRepr)), 1, "[Internal::StringSliceRepr]") 
    {;}

    virtual ~BSQStringSliceReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const override
    {
        auto srepr = (BSQStringSliceRepr*)repr;
        return (srepr->end - srepr->start);
    }

    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};

struct BSQStringConcatRepr
{
    void* srepr1;
    void* srepr2;
    uint64_t size;
};

class BSQStringConcatReprType : public BSQStringReprType
{
public:
    BSQStringConcatReprType() 
    : BSQStringReprType(BSQ_ALIGN_SIZE(sizeof(BSQStringConcatRepr)), 2, "[Internal::StringConcatRepr]") 
    {;}

    virtual ~BSQStringConcatReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const override
    {
        return ((BSQStringConcatRepr*)repr)->size;
    }

    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};

struct BSQString
{
    union { void* u_data; BSQInlineString u_inlineString; };
};
constexpr BSQString g_emptyString = {0};

struct BSQStringIterator
{
    BSQString str;
    int64_t strpos;
    void* cbuff;
    int16_t cpos;
    int16_t minpos;
    int16_t maxpos;
};

std::string entityStringBSQStringIteratorDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool iteratorIsValid(const BSQStringIterator* iter);
bool iteratorLess(const BSQStringIterator* iter1, const BSQStringIterator* iter2);
bool iteratorEqual(const BSQStringIterator* iter1, const BSQStringIterator* iter2);

void initializeStringIterPosition(BSQStringIterator* iter, int64_t pos);

uint8_t iteratorGetUTF8Byte(const BSQStringIterator* iter);
void incrementStringIterator_utf8byte(BSQStringIterator* iter);
void decrementStringIterator_utf8byte(BSQStringIterator* iter);

uint32_t iteratorGetCodePoint(BSQStringIterator* iter);
void incrementStringIterator_codePoint(BSQStringIterator* iter);
void decrementStringIterator_codePoint(BSQStringIterator* iter);

class BSQStringIteratorType : public BSQEntityType
{
public:
    BSQStringIteratorType() 
    : BSQEntityType(BSQ_TYPE_ID_STRINGITERATOR, BSQTypeKind::Struct, { BSQ_ALIGN_SIZE(sizeof(BSQStringIterator)), BSQ_ALIGN_SIZE(sizeof(BSQStringIterator)), BSQ_ALIGN_SIZE(sizeof(BSQStringIterator)), "3121" }, "3", {}, entityStringBSQStringIteratorDisplay_impl, "NSCore::StringPos", {}, {}, {})
    {;}

    virtual ~BSQStringIteratorType() {;}

    void registerIteratorGCRoots(BSQStringIterator* iter);
    void releaseIteratorGCRoots(BSQStringIterator* iter);
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQEntityType
{
private:
    static BSQStringKRepr<8>* boxInlineString(BSQInlineString istr);

public:
    BSQStringType() : BSQEntityType({ BSQ_ALIGN_SIZE(sizeof(BSQString)), BSQ_ALIGN_SIZE(sizeof(BSQString)), BSQ_ALIGN_SIZE(sizeof(BSQString)), "31" }, entityStringEqual_impl, entityStringLessThan_impl, entityStringDisplay_impl, "NSCore::String") {;}
    virtual ~BSQStringType() {;}

    static void initializeIteratorMin(BSQStringIterator* iter, BSQString str);
    static void initializeIteratorMax(BSQStringIterator* iter, BSQString str);

    static void initializeIteratorBegin(BSQStringIterator* iter, BSQString str);
    static void initializeIteratorEnd(BSQStringIterator* iter, BSQString str);

    static bool equal(BSQString v1, BSQString v2);
    static bool lessThan(BSQString v1, BSQString v2);

    inline static int64_t utf8ByteCount(const BSQString& s)
    {
        if(IS_INLINE_STRING(&s))
        {
            return (int64_t)BSQInlineString::utf8ByteCount(s.u_inlineString);
        }
        else
        {
            return (int64_t)GET_TYPE_META_DATA_AS(BSQStringReprType, s.u_data)->utf8ByteCount(s.u_data);
        }
    }

    static inline BSQBool empty(const BSQString& s)
    {
        return (BSQBool)(s.u_data == nullptr);
    }

    static BSQString concat2(StorageLocationPtr s1, StorageLocationPtr s2);
    static BSQString slice(StorageLocationPtr str, StorageLocationPtr startpos, StorageLocationPtr endpos);
};

////
//ByteBuffer
struct BSQByteBuffer
{
    BSQByteBuffer* next;
    uint64_t bytecount;
    uint8_t bytes[256];
};

//
//TODO: at some point in the future we might want to split this out with the 256 buffer as a 
//      carefully memory aligned thing and a overall object that know the total lenght of the 
//      buffer
//

std::string entityByteBufferDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQByteBufferType : public BSQEntityType
{
public:
    BSQByteBufferType() : BSQEntityType(BSQ_TYPE_ID_BYTEBUFFER, BSQTypeKind::Ref, { BSQ_ALIGN_SIZE(sizeof(BSQByteBuffer)), sizeof(void*), sizeof(void*), "2" }, 1, {}, entityByteBufferDisplay_impl, "NSCore::ByteBuffer", {}, {}, {}) {;}
    virtual ~BSQByteBufferType() {;}
};

////
//ISOTime
typedef uint64_t BSQISOTime;

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQISOTimeType : public BSQEntityType
{
public:
    BSQISOTimeType() : BSQEntityType(BSQ_TYPE_ID_ISOTIME, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQISOTime)), BSQ_ALIGN_SIZE(sizeof(BSQISOTime)), BSQ_ALIGN_SIZE(sizeof(BSQISOTime)), "1" }, {}, entityISOTimeDisplay_impl, "NSCore::ISOTime", {}, {}, {}) {;}
    virtual ~BSQISOTimeType() {;}
};

////
//LogicalTime
typedef uint64_t BSQLogicalTime;

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityLogicalTimeEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityLogicalTimeLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQLogicalTimeType : public BSQEntityType
{
public:
    BSQLogicalTimeType() : BSQEntityType(BSQ_TYPE_ID_LOGICALTIME, BSQTypeKind::Register, { BSQ_ALIGN_SIZE(sizeof(BSQLogicalTime)), BSQ_ALIGN_SIZE(sizeof(BSQLogicalTime)), BSQ_ALIGN_SIZE(sizeof(BSQLogicalTime)), "1"}, {}, entityLogicalTimeEqual_impl, entityLogicalTimeLessThan_impl, entityLogicalTimeDisplay_impl, "NSCore::LogicalTime", {}, {}, {}) {;}
    virtual ~BSQLogicalTimeType() {;}

    inline static bool equal(BSQLogicalTime v1, BSQLogicalTime v2) { return v1 == v2; }
    inline static bool lessThan(BSQLogicalTime v1, BSQLogicalTime v2) { return v1 < v2; }
};

////
//UUID
typedef boost::uuids::uuid BSQUUID;

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityUUIDEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityUUIDLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQUUIDType : public BSQEntityType
{
public:
    BSQUUIDType() : BSQEntityType(BSQ_TYPE_ID_UUID, BSQTypeKind::Ref, { BSQ_ALIGN_SIZE(sizeof(BSQUUID)), sizeof(void*), sizeof(void*), "2" }, {}, entityUUIDEqual_impl, entityUUIDLessThan_impl, entityUUIDDisplay_impl, "NSCore::UUID", {}, {}, {}) {;}
    virtual ~BSQUUIDType() {;}

    inline static bool equal(BSQUUID* v1, BSQUUID* v2) { return *v1 == *v2; }
    inline static bool lessThan(BSQUUID* v1, BSQUUID* v2) { return *v1 < *v2; }
};

////
//ContentHash
typedef boost::multiprecision::checked_uint512_t BSQContentHash;

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityContentHashEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityContentHashLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQContentHashType : public BSQEntityType
{
public:
    BSQContentHashType() : BSQEntityType(BSQ_TYPE_ID_CONTENTHASH, BSQTypeKind::Ref, { BSQ_ALIGN_SIZE(sizeof(BSQContentHash)), sizeof(void*), sizeof(void*), "2" }, {}, entityContentHashEqual_impl, entityContentHashLessThan_impl, entityContentHashDisplay_impl, "NSCore::ContentHash", {}, {}, {}) {;}
    virtual ~BSQContentHashType() {;}

    inline static bool equal(BSQContentHash* v1, BSQContentHash* v2) { return *v1 == *v2; }
    inline static bool lessThan(BSQContentHash* v1, BSQContentHash* v2) { return *v1 < *v2; }
};

////
//Regex

struct BSQRegex
{
    std::string* strversion;
    std::regex* regex;
};

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRegexType : public BSQEntityType
{
public:
    BSQRegexType() : BSQEntityType(BSQ_TYPE_ID_REGEX, BSQTypeKind::Struct, { BSQ_ALIGN_SIZE(sizeof(BSQRegex)), BSQ_ALIGN_SIZE(sizeof(BSQRegex)), BSQ_ALIGN_SIZE(sizeof(BSQRegex)), "11" }, {}, entityRegexDisplay_impl, "NSCore::Regex", {}, {}, {}) {;}
    virtual ~BSQRegexType() {;}
};
