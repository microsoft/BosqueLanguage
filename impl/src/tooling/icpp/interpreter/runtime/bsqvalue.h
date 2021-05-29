//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "../core/bsqmemory.h"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/uuid/uuid.hpp>

////
//Primitive value representations

////
//None
typedef uint64_t BSQNone;
#define BSQNoneValue 0
#define BSQNoneHeapValue nullptr

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityNoneEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityNoneLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNoneType : public BSQRegisterType<BSQNone>
{
public:
    BSQNoneType(): BSQRegisterType(BSQ_TYPE_ID_NONE, sizeof(BSQNone), "1", {entityNoneEqual_impl, entityNoneLessThan_impl}, entityNoneDisplay_impl, "NSCore::None")
    {
        static_assert(sizeof(BSQNone) == 8);
    }

    virtual ~BSQNoneType() {;}
};

////
//Bool

typedef uint8_t BSQBool;
#define BSQTRUE ((BSQBool)1)
#define BSQFALSE ((BSQBool)0)

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBoolEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBoolLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBoolType : public BSQRegisterType<BSQBool>
{
public:
    BSQBoolType(): BSQRegisterType(BSQ_TYPE_ID_BOOL, sizeof(BSQBool), "1", {entityBoolEqual_impl, entityBoolLessThan_impl}, entityBoolDisplay_impl, "NSCore::Bool")
    {
        static_assert(sizeof(BSQBool) == 1);
    }

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

class BSQNatType : public BSQRegisterType<BSQNat>
{
public:
    BSQNatType(): BSQRegisterType(BSQ_TYPE_ID_NAT, sizeof(BSQNat), "1", {entityNatEqual_impl, entityNatLessThan_impl}, entityNatDisplay_impl, "NSCore::Nat")
    {
        static_assert(sizeof(BSQNat) == 8);
    }

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

class BSQIntType : public BSQRegisterType<BSQInt>
{
public:
    BSQIntType(): BSQRegisterType(BSQ_TYPE_ID_INT, sizeof(BSQInt), "1", {entityIntEqual_impl, entityIntLessThan_impl}, entityIntDisplay_impl, "NSCore::Int")
    {
        static_assert(sizeof(BSQInt) == 8);
    }

    virtual ~BSQIntType() {;}

    inline static bool equal(BSQInt v1, BSQInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQInt v1, BSQInt v2) { return v1 < v2; }
};

////
//BigNat
typedef boost::multiprecision::cpp_int BSQBigNat;

//
//TODO: maybe change impl to inline + https://github.com/chakra-core/ChakraCore/blob/1eae003b7a981b4b691928daef27b5254a49f5eb/lib/Runtime/Library/JavascriptBigInt.h
//

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigNatEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBigNatLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigNatType : public BSQBigNumType<BSQNat>
{
public:
    BSQBigNatType(): BSQBigNumType(BSQ_TYPE_ID_BIGNAT, sizeof(BSQBigNat), "411", {entityBigNatEqual_impl, entityBigNatLessThan_impl}, entityBigNatDisplay_impl, "NSCore::BigNat") 
    {
        static_assert(sizeof(BSQBigNat) == 24);
    }

    virtual ~BSQBigNatType() {;}

    inline static bool equal(BSQBigNat v1, BSQBigNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigNat v1, BSQBigNat v2) { return v1 < v2; }
};

////
//BigInt
typedef boost::multiprecision::cpp_int BSQBigInt;

//
//TODO: maybe change impl to inline + https://github.com/chakra-core/ChakraCore/blob/1eae003b7a981b4b691928daef27b5254a49f5eb/lib/Runtime/Library/JavascriptBigInt.h
//

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityBigIntEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityBigIntLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigIntType : public BSQBigNumType<BSQBigInt>
{
public:
    BSQBigIntType(): BSQBigNumType(BSQ_TYPE_ID_BIGINT, sizeof(BSQBigInt), "411", {entityBigIntEqual_impl, entityBigIntLessThan_impl}, entityBigIntDisplay_impl, "NSCore::BigInt") 
    {
        static_assert(sizeof(BSQBigNat) == 24);
    }

    virtual ~BSQBigIntType() {;}

    inline static bool equal(BSQBigInt v1, BSQBigInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigInt v1, BSQBigInt v2) { return v1 < v2; }
};

////
//Float
typedef double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQFloatType: public BSQRegisterType<BSQFloat>
{
public:
    BSQFloatType(): BSQRegisterType(BSQ_TYPE_ID_FLOAT, sizeof(BSQFloat), "1", EMPTY_KEY_FUNCTOR_SET, entityFloatDisplay_impl, "NSCore::Float") 
    {
        static_assert(sizeof(BSQFloat) == 8);
    }

    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef double BSQDecimal;

//
//TODO: this is not a nice "large number of significant integral and fractional digits and no round-off error" like I want plus it is huge -- we need to get a better library later
//https://github.com/dotnet/runtime/blob/main/src/libraries/System.Private.CoreLib/src/System/Decimal.cs
//

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQDecimalType : public BSQRegisterType<BSQDecimal>
{
public:
    BSQDecimalType() : BSQRegisterType(BSQ_TYPE_ID_DECIMAL, sizeof(BSQDecimal), "1" , EMPTY_KEY_FUNCTOR_SET, entityDecimalDisplay_impl, "NSCore::Decimal")
    {
        static_assert(sizeof(BSQDecimal) == 8);
    }

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

class BSQRationalType : public BSQRegisterType<BSQRational>
{
public:
    BSQRationalType() : BSQRegisterType(BSQ_TYPE_ID_RATIONAL, sizeof(BSQRational), "1111", EMPTY_KEY_FUNCTOR_SET, entityRationalDisplay_impl, "NSCore::Rational") 
    {
        static_assert(sizeof(BSQRational) == 32);
    }

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

class BSQStringReprType : public BSQRefType
{
public:
    static uint64_t getKReprSizeFor(uint64_t v);

    BSQStringReprType(uint64_t allocsize, RefMask heapmask, std::string name):
        BSQRefType(BSQ_TYPE_ID_STRINGREPR, allocsize, heapmask, {}, EMPTY_KEY_FUNCTOR_SET, entityStringReprDisplay_impl, name) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const = 0;
    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const = 0;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const = 0;
};

class BSQStringKReprTypeAbstract : public BSQStringReprType
{
public:
    BSQStringKReprTypeAbstract(uint64_t allocsize, std::string name) 
    : BSQStringReprType(allocsize, nullptr, name) 
    {;}

    virtual ~BSQStringKReprTypeAbstract() {;}

    static uint64_t getUTF8ByteCount(void* repr)
    {
        return *((uint8_t*)repr);
    }

    static uint8_t* getUTF8Bytes(void* repr)
    {
        return ((uint8_t*)repr) + 1;
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
    BSQStringKReprType(): BSQStringKReprTypeAbstract(k, "[Internal::StringKRepr]") 
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
    BSQStringSliceReprType(): BSQStringReprType(sizeof(BSQStringSliceRepr), "211", "[Internal::StringSliceRepr]") 
    {;}

    virtual ~BSQStringSliceReprType() {;}

    uint64_t utf8ByteCount(void* repr) const override final
    {
        auto srepr = (BSQStringSliceRepr*)repr;
        return (srepr->end - srepr->start);
    }

    void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const override final;
    void* slice(void* data, uint64_t nstart, uint64_t nend) const override final;
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
    BSQStringConcatReprType(): BSQStringReprType(sizeof(BSQStringConcatRepr), "22", "[Internal::StringConcatRepr]") 
    {;}

    virtual ~BSQStringConcatReprType() {;}

    uint64_t utf8ByteCount(void* repr) const override final
    {
        return ((BSQStringConcatRepr*)repr)->size;
    }

    void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const override final;
    void* slice(void* data, uint64_t nstart, uint64_t nend) const override final;
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

class BSQStringIteratorType : public BSQStructType
{
public:
    BSQStringIteratorType(): 
        BSQStructType(BSQ_TYPE_ID_STRINGITERATOR, sizeof(BSQStringIterator), "31121", {}, EMPTY_KEY_FUNCTOR_SET, entityStringBSQStringIteratorDisplay_impl, "NSCore::StringPos")
    {
        static_assert(sizeof(BSQStringIterator) == 40);
    }

    virtual ~BSQStringIteratorType() {;}

    void registerIteratorGCRoots(BSQStringIterator* iter);
    void releaseIteratorGCRoots(BSQStringIterator* iter);
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQType
{
private:
    static uint8_t* boxInlineString(BSQInlineString istr);

public:
    BSQStringType() 
    : BSQType(BSQ_TYPE_ID_STRING, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, {entityStringEqual_impl, entityStringLessThan_impl}, entityStringDisplay_impl, "NSCore::String")
    {
        static_assert(sizeof(BSQString) == 16);
    }

    virtual ~BSQStringType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, {0});
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, SLPTR_LOAD_CONTENTS_AS(BSQString, src));
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, SLPTR_LOAD_CONTENTS_AS(BSQString, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQString, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQString, src));
    }

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

class BSQByteBufferType : public BSQRefType
{
public:
    BSQByteBufferType(): BSQRefType(BSQ_TYPE_ID_BYTEBUFFER, sizeof(BSQByteBuffer), "2", {}, EMPTY_KEY_FUNCTOR_SET, entityByteBufferDisplay_impl, "NSCore::ByteBuffer") {;}

    virtual ~BSQByteBufferType() {;}
};

////
//ISOTime
typedef uint64_t BSQISOTime;

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQISOTimeType : public BSQRegisterType<BSQISOTime>
{
public:
    BSQISOTimeType(): BSQRegisterType(BSQ_TYPE_ID_ISOTIME, sizeof(BSQISOTime), "1", EMPTY_KEY_FUNCTOR_SET, entityISOTimeDisplay_impl, "NSCore::ISOTime") 
    {
        static_assert(sizeof(BSQISOTime) == 8);
    }
    
    virtual ~BSQISOTimeType() {;}
};

////
//LogicalTime
typedef uint64_t BSQLogicalTime;

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityLogicalTimeEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityLogicalTimeLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQLogicalTimeType : public BSQRegisterType<BSQLogicalTime>
{
public:
    BSQLogicalTimeType(): BSQRegisterType(BSQ_TYPE_ID_LOGICALTIME, sizeof(BSQLogicalTime), "1", {entityLogicalTimeEqual_impl, entityLogicalTimeLessThan_impl}, entityLogicalTimeDisplay_impl, "NSCore::LogicalTime") 
    {
        static_assert(sizeof(BSQLogicalTime) == 8);
    }

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

class BSQUUIDType : public BSQRefType
{
public:
    BSQUUIDType(): BSQRefType(BSQ_TYPE_ID_UUID, sizeof(BSQUUID), nullptr, {}, {entityUUIDEqual_impl, entityUUIDLessThan_impl}, entityUUIDDisplay_impl, "NSCore::UUID") {;}
    
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

class BSQContentHashType : public BSQRefType
{
public:
    BSQContentHashType(): BSQRefType(BSQ_TYPE_ID_CONTENTHASH, sizeof(BSQContentHash), nullptr, {}, {entityContentHashEqual_impl, entityContentHashLessThan_impl}, entityContentHashDisplay_impl, "NSCore::ContentHash") {;}

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

class BSQRegexType : public BSQRegisterType<BSQRegex>
{
public:
    BSQRegexType(): BSQRegisterType(BSQ_TYPE_ID_REGEX, sizeof(BSQRegex), "11", EMPTY_KEY_FUNCTOR_SET, entityRegexDisplay_impl, "NSCore::Regex") 
    {
        static_assert(sizeof(BSQRegex) == 16);
    }

    virtual ~BSQRegexType() {;}
};
