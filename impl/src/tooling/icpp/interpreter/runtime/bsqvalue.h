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

std::string generateRandomChar(RandGenerator& rnd);

////
//None
typedef uint64_t BSQNone;
#define BSQNoneValue 0
#define BSQNoneHeapValue nullptr

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityNoneKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityNoneJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityNoneGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQNoneType : public BSQRegisterType<BSQNone>
{
public:
    BSQNoneType(): BSQRegisterType(BSQ_TYPE_ID_NONE, sizeof(BSQNone), "1", entityNoneKeyCmp_impl, entityNoneDisplay_impl, "NSCore::None", {entityNoneJSONParse_impl, entityNoneGenerateRandom_impl})
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
int entityBoolKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityBoolJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityBoolGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQBoolType : public BSQRegisterType<BSQBool>
{
public:
    BSQBoolType(): BSQRegisterType(BSQ_TYPE_ID_BOOL, sizeof(BSQBool), "1", entityBoolKeyCmp_impl, entityBoolDisplay_impl, "NSCore::Bool", {entityBoolJSONParse_impl, entityBoolGenerateRandom_impl})
    {
        static_assert(sizeof(BSQBool) == 1);
    }

    virtual ~BSQBoolType() {;}
};

////
//Nat
typedef uint64_t BSQNat;

std::string entityNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityNatKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityNatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityNatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQNatType : public BSQRegisterType<BSQNat>
{
public:
    BSQNatType(): BSQRegisterType(BSQ_TYPE_ID_NAT, sizeof(BSQNat), "1", entityNatKeyCmp_impl, entityNatDisplay_impl, "NSCore::Nat", {entityNatJSONParse_impl, entityNatGenerateRandom_impl})
    {
        static_assert(sizeof(BSQNat) == 8);
    }

    virtual ~BSQNatType() {;}
};

////
//Int
typedef int64_t BSQInt;

std::string entityIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityIntKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityIntJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityIntGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQIntType : public BSQRegisterType<BSQInt>
{
public:
    BSQIntType(): BSQRegisterType(BSQ_TYPE_ID_INT, sizeof(BSQInt), "1", entityIntKeyCmp_impl, entityIntDisplay_impl, "NSCore::Int", {entityIntJSONParse_impl, entityIntGenerateRandom_impl})
    {
        static_assert(sizeof(BSQInt) == 8);
    }

    virtual ~BSQIntType() {;}
};


#ifdef __APPLE__
#define BIGNAT_SIZE (size_t)32
#define BIGINT_SIZE (size_t)32
#define RATIONAL_SIZE (size_t)48

#define BIGNAT_MASK "4111"
#define BIGINT_MASK "4111"
#define RATIONAL_MASK "411111"
#else
#define BIGNAT_SIZE (size_t)24
#define BIGINT_SIZE (size_t)24
#define RATIONAL_SIZE (size_t)32

#define BIGNAT_MASK "411"
#define BIGINT_MASK "411"
#define RATIONAL_MASK "4111"
#endif

////
//BigNat
typedef boost::multiprecision::cpp_int BSQBigNat;

//
//TODO: maybe change impl to inline + https://github.com/chakra-core/ChakraCore/blob/1eae003b7a981b4b691928daef27b5254a49f5eb/lib/Runtime/Library/JavascriptBigInt.h
//

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityBigNatKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityBigNatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityBigNatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQBigNatType : public BSQBigNumType<BSQBigNat>
{
public:
    BSQBigNatType(): BSQBigNumType(BSQ_TYPE_ID_BIGNAT, BIGNAT_SIZE, BIGNAT_MASK, entityBigNatKeyCmp_impl, entityBigNatDisplay_impl, "NSCore::BigNat", {entityBigNatJSONParse_impl, entityBigNatGenerateRandom_impl}) 
    {
        static_assert(sizeof(BSQBigNat) == BIGNAT_SIZE);
    }

    virtual ~BSQBigNatType() {;}
};

////
//BigInt
typedef boost::multiprecision::cpp_int BSQBigInt;

//
//TODO: maybe change impl to inline + https://github.com/chakra-core/ChakraCore/blob/1eae003b7a981b4b691928daef27b5254a49f5eb/lib/Runtime/Library/JavascriptBigInt.h
//

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityBigIntKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityBigIntJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityBigIntGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQBigIntType : public BSQBigNumType<BSQBigInt>
{
public:
    BSQBigIntType(): BSQBigNumType(BSQ_TYPE_ID_BIGINT, BIGINT_SIZE, BIGINT_MASK, entityBigIntKeyCmp_impl, entityBigIntDisplay_impl, "NSCore::BigInt", {entityBigIntJSONParse_impl, entityBigIntGenerateRandom_impl}) 
    {
        static_assert(sizeof(BSQBigInt) == BIGINT_SIZE);
    }

    virtual ~BSQBigIntType() {;}
};

////
//Float
typedef double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityFloatJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityFloatGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQFloatType: public BSQRegisterType<BSQFloat>
{
public:
    BSQFloatType(): BSQRegisterType(BSQ_TYPE_ID_FLOAT, sizeof(BSQFloat), "1", EMPTY_KEY_CMP, entityFloatDisplay_impl, "NSCore::Float", {entityFloatJSONParse_impl, entityFloatGenerateRandom_impl}) 
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

bool entityDecimalJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityDecimalGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQDecimalType : public BSQRegisterType<BSQDecimal>
{
public:
    BSQDecimalType() : BSQRegisterType(BSQ_TYPE_ID_DECIMAL, sizeof(BSQDecimal), "1" , EMPTY_KEY_CMP, entityDecimalDisplay_impl, "NSCore::Decimal", {entityDecimalJSONParse_impl, entityDecimalGenerateRandom_impl})
    {
        static_assert(sizeof(BSQDecimal) == 8);
    }

    virtual ~BSQDecimalType() {;}
};

////
//Rational
struct BSQRational
{
    BSQBigInt numerator;
    BSQNat denominator;
};

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityRationalJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityRationalGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQRationalType : public BSQRegisterType<BSQRational>
{
public:
    BSQRationalType() : BSQRegisterType(BSQ_TYPE_ID_RATIONAL, RATIONAL_SIZE, RATIONAL_MASK, EMPTY_KEY_CMP, entityRationalDisplay_impl, "NSCore::Rational", {entityRationalJSONParse_impl, entityRationalGenerateRandom_impl}) 
    {
        static_assert(sizeof(BSQRational) == RATIONAL_SIZE);
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
        BSQRefType(BSQ_TYPE_ID_STRINGREPR, allocsize, heapmask, {}, EMPTY_KEY_CMP, entityStringReprDisplay_impl, name, {nullptr, nullptr}) 
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
        BSQStructType(BSQ_TYPE_ID_STRINGITERATOR, sizeof(BSQStringIterator), "31121", {}, EMPTY_KEY_CMP, entityStringBSQStringIteratorDisplay_impl, "NSCore::StringPos", {nullptr, nullptr})
    {
        static_assert(sizeof(BSQStringIterator) == 40);
    }

    virtual ~BSQStringIteratorType() {;}

    void registerIteratorGCRoots(BSQStringIterator* iter);
    void releaseIteratorGCRoots(BSQStringIterator* iter);
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityStringKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityStringJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityStringGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQStringType : public BSQType
{
private:
    static uint8_t* boxInlineString(BSQInlineString istr);

public:
    BSQStringType() 
    : BSQType(BSQ_TYPE_ID_STRING, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityStringDisplay_impl, "NSCore::String", {entityStringJSONParse_impl, entityStringGenerateRandom_impl})
    {
        static_assert(sizeof(BSQString) == 16);
    }

    virtual ~BSQStringType() {;}

    void storeValueDirect(StorageLocationPtr trgt, BSQString s) const
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, s);
    }

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

    static int keycmp(BSQString v1, BSQString v2);

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
    BSQByteBufferType(): BSQRefType(BSQ_TYPE_ID_BYTEBUFFER, sizeof(BSQByteBuffer), "2", {}, EMPTY_KEY_CMP, entityByteBufferDisplay_impl, "NSCore::ByteBuffer", {nullptr, nullptr}) {;}

    virtual ~BSQByteBufferType() {;}
};

////
//ISOTime
typedef uint64_t BSQISOTime;

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityISOTimeJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityISOTimeGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQISOTimeType : public BSQRegisterType<BSQISOTime>
{
public:
    BSQISOTimeType(): BSQRegisterType(BSQ_TYPE_ID_ISOTIME, sizeof(BSQISOTime), "1", EMPTY_KEY_CMP, entityISOTimeDisplay_impl, "NSCore::ISOTime", {entityISOTimeJSONParse_impl, entityISOTimeGenerateRandom_impl}) 
    {
        static_assert(sizeof(BSQISOTime) == 8);
    }
    
    virtual ~BSQISOTimeType() {;}
};

////
//LogicalTime
typedef uint64_t BSQLogicalTime;

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityLogicalTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityLogicalTimeJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityLogicalTimeGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQLogicalTimeType : public BSQRegisterType<BSQLogicalTime>
{
public:
    BSQLogicalTimeType(): BSQRegisterType(BSQ_TYPE_ID_LOGICALTIME, sizeof(BSQLogicalTime), "1", entityLogicalTimeKeyCmp_impl, entityLogicalTimeDisplay_impl, "NSCore::LogicalTime", {entityLogicalTimeJSONParse_impl, entityLogicalTimeGenerateRandom_impl}) 
    {
        static_assert(sizeof(BSQLogicalTime) == 8);
    }

    virtual ~BSQLogicalTimeType() {;}
};

////
//UUID
typedef boost::uuids::uuid BSQUUID;

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityUUIDKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityUUIDJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityUUIDGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQUUIDType : public BSQRefType
{
public:
    BSQUUIDType(): BSQRefType(BSQ_TYPE_ID_UUID, sizeof(BSQUUID), nullptr, {}, entityUUIDKeyCmp_impl, entityUUIDDisplay_impl, "NSCore::UUID", {entityUUIDJSONParse_impl, entityUUIDGenerateRandom_impl}) {;}
    
    virtual ~BSQUUIDType() {;}
};

////
//ContentHash
typedef boost::multiprecision::checked_uint512_t BSQContentHash;

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityContentHashKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

bool entityContentHashJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityContentHashGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQContentHashType : public BSQRefType
{
public:
    BSQContentHashType(): BSQRefType(BSQ_TYPE_ID_CONTENTHASH, sizeof(BSQContentHash), nullptr, {}, entityContentHashKeyCmp_impl, entityContentHashDisplay_impl, "NSCore::ContentHash", {entityContentHashJSONParse_impl, entityContentHashGenerateRandom_impl}) {;}

    virtual ~BSQContentHashType() {;}
};

////
//Regex

////
//Typed string helpers

enum class SpecialCharKind 
{
    Wildcard = 0x0,
    WhiteSpace
};

class BSQRegexOpt
{
public:
    BSQRegexOpt() {;}
    virtual ~BSQRegexOpt() {;}

    virtual std::string generate(RandGenerator& rnd) const = 0;

    static BSQRegexOpt* reoptJSONParse_impl(const boost::json::value& jv);
};

class BSQLiteralRe : public BSQRegexOpt
{
public:
    const std::string litval;

    BSQLiteralRe(std::string lv) : BSQRegexOpt(), litval(lv) {;}
    virtual ~BSQLiteralRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQLiteralRe* litoptJSONParse_impl(const boost::json::value& jv);
};

class BSQCharRangeRe : public BSQRegexOpt
{
public:
    const uint64_t low;
    const uint64_t high;

    BSQCharRangeRe(uint64_t low, uint64_t high) : BSQRegexOpt(), low(low), high(high) {;}
    virtual ~BSQCharRangeRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQCharRangeRe* crangeoptJSONParse_impl(const boost::json::value& jv);
};

class BSQCharClassRe : public BSQRegexOpt
{
public:
    const SpecialCharKind kind;

    BSQCharClassRe(SpecialCharKind kind) : BSQRegexOpt(), kind(kind) {;}
    virtual ~BSQCharClassRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQCharClassRe* classoptJSONParse_impl(const boost::json::value& jv);
};

class BSQStarRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQStarRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQStarRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQStarRepeatRe* staroptJSONParse_impl(const boost::json::value& jv);
};

class BSQPlusRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQPlusRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQPlusRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQPlusRepeatRe* plusoptJSONParse_impl(const boost::json::value& jv);
};

class BSQRangeRepeatRe : public BSQRegexOpt
{
public:
    const uint32_t low;
    const uint32_t high;
    const BSQRegexOpt* opt;

    BSQRangeRepeatRe(uint32_t low, uint32_t high, const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt), low(low), high(high) {;}
    virtual ~BSQRangeRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQRangeRepeatRe* rangeoptJSONParse_impl(const boost::json::value& jv);
};

class BSQOptionalRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQOptionalRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQOptionalRe* optoptJSONParse_impl(const boost::json::value& jv);
};

class BSQAlternationRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQAlternationRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQAlternationRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQAlternationRe* altoptJSONParse_impl(const boost::json::value& jv);
};

class BSQSequenceRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQSequenceRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQSequenceRe() {;}

    virtual std::string generate(RandGenerator& rnd) const override final;

    static BSQSequenceRe* seqoptJSONParse_impl(const boost::json::value& jv);
};

struct BSQRegex
{
    std::string restr;
    std::regex cppre;
    bool isAnchorStart;
    bool isAnchorEnd;
    BSQRegexOpt* re;

    std::string generate(RandGenerator& rnd)
    {
        return this->re->generate(rnd);
    }  
};

BSQRegex bsqRegexJSONParse_impl(const boost::json::value& jv);

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRegexType : public BSQRegisterType<void*>
{
public:
    BSQRegexType(): BSQRegisterType(BSQ_TYPE_ID_REGEX, sizeof(void*), "1", EMPTY_KEY_CMP, entityRegexDisplay_impl, "NSCore::Regex", {nullptr, nullptr}) {;}
    virtual ~BSQRegexType() {;}
};

std::string entityValidatorDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQValidatorType : public BSQRegisterType<void*>
{
public:
    const BSQRegex re;

    BSQValidatorType(BSQTypeID tid, std::string name, BSQRegex re): BSQRegisterType(tid, sizeof(void*), "1", EMPTY_KEY_CMP, entityValidatorDisplay_impl, name, {nullptr, nullptr}), re(re) {;}
    virtual ~BSQValidatorType() {;}
};

std::string entityStringOfDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityStringOfJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityStringOfGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQStringOfType : public BSQType
{
public:
    const BSQTypeID validator;

    BSQStringOfType(BSQTypeID tid, std::string name, const BSQTypeID validator)
    : BSQType(tid, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityStringOfDisplay_impl, name, {entityStringOfJSONParse_impl, entityStringOfGenerateRandom_impl}), validator(validator)
    {
        static_assert(sizeof(BSQString) == 16);
    }

    virtual ~BSQStringOfType() {;}

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
};

std::string entityDataStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityDataStringJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityDataStringGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQDataStringType : public BSQType
{
public:
    const BSQInvokeID parsemethod;

    BSQDataStringType(BSQTypeID tid, std::string name, BSQInvokeID parsemethod)
    : BSQType(tid, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityDataStringDisplay_impl, name, {entityDataStringJSONParse_impl, entityDataStringGenerateRandom_impl}), parsemethod(parsemethod)
    {
        static_assert(sizeof(BSQString) == 16);
    }

    virtual ~BSQDataStringType() {;}

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
};


std::string entityTypedNumberDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool entityTypedNumberJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void entityTypedNumberGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQTypedNumberTypeAbstract
{
public:
    const BSQTypeID underlying;

    BSQTypedNumberTypeAbstract(BSQTypeID underlying): underlying(underlying) {;}
};

template <typename T>
class BSQTypedNumberType : public BSQRegisterType<T>, public BSQTypedNumberTypeAbstract
{
public:
    BSQTypedNumberType(BSQTypeID tid, std::string name, BSQTypeID underlying, const BSQType* primitive)
    : BSQRegisterType<T>(tid, primitive->allocinfo.inlinedatasize, primitive->allocinfo.inlinedmask, primitive->fpkeycmp, entityTypedNumberDisplay_impl, name, {entityTypedNumberJSONParse_impl, entityTypedNumberGenerateRandom_impl}), 
    BSQTypedNumberTypeAbstract(underlying)
    {;}

    virtual ~BSQTypedNumberType() {;}
};

template <typename T>
class BSQTypedBigNumberType : public BSQBigNumType<T>, public BSQTypedNumberTypeAbstract
{
public:
    BSQTypedBigNumberType(BSQTypeID tid, std::string name, BSQTypeID underlying, const BSQType* primitive)
    : BSQBigNumType<T>(tid, primitive->allocinfo.inlinedatasize, primitive->allocinfo.inlinedmask, primitive->fpkeycmp, entityTypedNumberDisplay_impl, name, {entityTypedNumberJSONParse_impl, entityTypedNumberGenerateRandom_impl}), 
    BSQTypedNumberTypeAbstract(underlying)
    {;}

    virtual ~BSQTypedBigNumberType() {;}
};

std::string enumDisplay_impl(const BSQType* btype, StorageLocationPtr data);

bool enumJSONParse_impl(const BSQType* btype, const boost::json::value& jv, StorageLocationPtr sl);
void enumGenerateRandom_impl(const BSQType* btype, RandGenerator& rnd, StorageLocationPtr sl);

class BSQEnumType : public BSQStructType
{
public:
    const BSQType* underlying;
    const std::vector<std::pair<std::string, uint32_t>> enuminvs; //map from full enum names to the constant storage location

    BSQEnumType(BSQTypeID tid, std::string name, const BSQType* underlying, std::vector<std::pair<std::string, BSQInvokeID>> consmap)
    : BSQStructType(tid, underlying->allocinfo.inlinedatasize, underlying->allocinfo.inlinedmask, {}, underlying->fpkeycmp, enumDisplay_impl, name, {enumJSONParse_impl, enumGenerateRandom_impl}),
    enuminvs(enuminvs)
    {;}

    virtual ~BSQEnumType() {;}
};

//
//TODO: need to support things that are any APIType not just numeric
//
