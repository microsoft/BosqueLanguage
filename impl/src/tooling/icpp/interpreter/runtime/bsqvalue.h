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
    BSQBoolType(): BSQRegisterType(BSQ_TYPE_ID_BOOL, sizeof(BSQBool),"1", {entityBoolEqual_impl, entityBoolLessThan_impl}, entityBoolDisplay_impl, "NSCore::Bool")
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

class BSQNatType : public BSQEntityAbstractType
{
public:
    BSQNatType() : BSQEntityAbstractType(BSQ_TYPE_ID_NAT, BSQTypeKind::Register, { sizeof(BSQNat), sizeof(BSQNat), sizeof(BSQNat), "1" }, {}, entityNatEqual_impl, entityNatLessThan_impl, entityNatDisplay_impl, "NSCore::Nat", {}, {}, {})
    {
        static_assert(sizeof(BSQNat) == 8);
    }

    virtual ~BSQNatType() {;}

    inline static bool equal(BSQNat v1, BSQNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQNat v1, BSQNat v2) { return v1 < v2; }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQNat, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQNat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQNat, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQNat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQNat, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQNat, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQNat, src));
    }
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
    BSQIntType() : BSQEntityAbstractType(BSQ_TYPE_ID_INT, BSQTypeKind::Register, { sizeof(BSQInt), sizeof(BSQInt), sizeof(BSQInt), "1" }, {}, entityIntEqual_impl, entityIntLessThan_impl, entityIntDisplay_impl, "NSCore::Int", {}, {}, {})
    {
        static_assert(sizeof(BSQInt) == 8);
    }

    virtual ~BSQIntType() {;}

    inline static bool equal(BSQInt v1, BSQInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQInt v1, BSQInt v2) { return v1 < v2; }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQInt, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQInt, trgt, SLPTR_LOAD_CONTENTS_AS(BSQInt, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQInt, trgt, SLPTR_LOAD_CONTENTS_AS(BSQInt, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQInt, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQInt, src));
    }
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

class BSQBigNatType : public BSQEntityAbstractType
{
public:
    BSQBigNatType() : BSQEntityAbstractType(BSQ_TYPE_ID_BIGNAT, BSQTypeKind::BigNum, { sizeof(BSQBigNat), sizeof(BSQBigNat), sizeof(BSQBigNat), "411" }, {}, entityBigNatEqual_impl, entityBigNatLessThan_impl, entityBigNatDisplay_impl, "NSCore::BigNat", {}, {}, {}) 
    {
        static_assert(sizeof(BSQBigNat) == 24);
    }

    virtual ~BSQBigNatType() {;}

    inline static bool equal(BSQBigNat v1, BSQBigNat v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigNat v1, BSQBigNat v2) { return v1 < v2; }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQInt, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQBigNat, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQBigNat, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQBigNat, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQBigNat, src));
    }
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

class BSQBigIntType : public BSQEntityAbstractType
{
public:
    BSQBigIntType() : BSQEntityAbstractType(BSQ_TYPE_ID_BIGINT, BSQTypeKind::BigNum, { sizeof(BSQBigInt), sizeof(BSQBigInt), sizeof(BSQBigInt), "411" }, {}, entityBigIntEqual_impl, entityBigIntLessThan_impl, entityBigIntDisplay_impl, "NSCore::BigInt", {}, {}, {}) 
    {
        static_assert(sizeof(BSQBigNat) == 24);
    }

    virtual ~BSQBigIntType() {;}

    inline static bool equal(BSQBigInt v1, BSQBigInt v2) { return v1 == v2; }
    inline static bool lessThan(BSQBigInt v1, BSQBigInt v2) { return v1 < v2; }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQInt, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, trgt, SLPTR_LOAD_CONTENTS_AS(BSQBigInt, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, trgt, SLPTR_LOAD_CONTENTS_AS(BSQBigInt, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQBigInt, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQBigInt, src));
    }
};

////
//Float
typedef double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQFloatType : public BSQEntityAbstractType
{
public:
    BSQFloatType() : BSQEntityAbstractType(BSQ_TYPE_ID_FLOAT, BSQTypeKind::Register, { sizeof(BSQFloat), sizeof(BSQFloat), sizeof(BSQFloat), "1" }, {}, entityFloatDisplay_impl, "NSCore::Float", {}, {}, {}) 
    {
        static_assert(sizeof(BSQFloat) == 8);
    }

    virtual ~BSQFloatType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, trgt, 0.0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQFloat, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQFloat, trgt, SLPTR_LOAD_CONTENTS_AS(BSQFloat, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQFloat, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQFloat, src));
    }
};

////
//Decimal
typedef double BSQDecimal;

//
//TODO: this is not a nice "large number of significant integral and fractional digits and no round-off error" like I want plus it is huge -- we need to get a better library later
//https://github.com/dotnet/runtime/blob/main/src/libraries/System.Private.CoreLib/src/System/Decimal.cs
//

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQDecimalType : public BSQEntityAbstractType
{
public:
    BSQDecimalType() : BSQEntityAbstractType(BSQ_TYPE_ID_DECIMAL, BSQTypeKind::Register, { sizeof(BSQDecimal), sizeof(BSQDecimal), sizeof(BSQDecimal), "1" }, {}, entityDecimalDisplay_impl, "NSCore::Decimal", {}, {}, {})
    {
        static_assert(sizeof(BSQDecimal) == 8);
    }

    virtual ~BSQDecimalType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, trgt, 0.0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, trgt, SLPTR_LOAD_CONTENTS_AS(BSQDecimal, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, trgt, SLPTR_LOAD_CONTENTS_AS(BSQDecimal, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQDecimal, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQDecimal, src));
    }
};

////
//Rational
struct BSQRational
{
    boost::multiprecision::int128_t numerator;
    uint64_t denominator;
};

std::string entityRationalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRationalType : public BSQEntityAbstractType
{
public:
    BSQRationalType() : BSQEntityAbstractType(BSQ_TYPE_ID_RATIONAL, BSQTypeKind::Register, {sizeof(BSQRational), sizeof(BSQRational), sizeof(BSQRational), "1111" }, {}, entityRationalDisplay_impl, "NSCore::BigInt", {}, {}, {}) 
    {
        static_assert(sizeof(BSQRational) == 32);
    }

    virtual ~BSQRationalType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRational, trgt, {0});
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRational, trgt, SLPTR_LOAD_CONTENTS_AS(BSQRational, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRational, trgt, SLPTR_LOAD_CONTENTS_AS(BSQRational, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQRational, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQRational, src));
    }
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

class BSQStringReprType : public BSQEntityAbstractType
{
public:
    static uint64_t getKReprSizeFor(uint64_t v);

    BSQStringReprType(uint64_t allocsize, RefMask mask, std::string name) 
    : BSQEntityAbstractType(BSQ_TYPE_ID_STRINGREPR, BSQTypeKind::Ref, { allocsize, sizeof(void*), sizeof(void*), mask }, "2", {}, entityStringReprDisplay_impl, name, {}, {}, {}) 
    {;}

    BSQStringReprType(uint64_t allocsize, std::string name) 
    : BSQEntityAbstractType(BSQ_TYPE_ID_STRINGREPR, BSQTypeKind::Ref, { allocsize, sizeof(void*), sizeof(void*), nullptr }, "2", {}, entityStringReprDisplay_impl, name, {}, {}, {}) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const = 0;
    virtual void initializeIterPosition(BSQStringIterator* iter, void* data, int64_t pos) const = 0;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const = 0;

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }
};

class BSQStringKReprTypeAbstract : public BSQStringReprType
{
public:
    BSQStringKReprTypeAbstract(uint64_t allocsize, std::string name) 
    : BSQStringReprType(allocsize, name) 
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
    BSQStringKReprType() 
    : BSQStringKReprTypeAbstract(k, "[Internal::StringKRepr]") 
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
    : BSQStringReprType(sizeof(BSQStringSliceRepr), "211", "[Internal::StringSliceRepr]") 
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
    : BSQStringReprType(sizeof(BSQStringConcatRepr), "221", "[Internal::StringConcatRepr]") 
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

class BSQStringIteratorType : public BSQEntityAbstractType
{
public:
    BSQStringIteratorType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_STRINGITERATOR, BSQTypeKind::Struct, { sizeof(BSQStringIterator), sizeof(BSQStringIterator), sizeof(BSQStringIterator), "3121" }, "3121", {}, entityStringBSQStringIteratorDisplay_impl, "NSCore::StringPos", {}, {}, {})
    {
        static_assert(sizeof(BSQStringIterator) == 40);
    }

    virtual ~BSQStringIteratorType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQStringIterator, trgt, {0});
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQStringIterator, trgt, SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQStringIterator, trgt, SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQStringIterator, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQStringIterator, src));
    }

    void registerIteratorGCRoots(BSQStringIterator* iter);
    void releaseIteratorGCRoots(BSQStringIterator* iter);
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityStringEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityStringLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQEntityAbstractType
{
private:
    static uint8_t* boxInlineString(BSQInlineString istr);

public:
    BSQStringType() 
    : BSQEntityAbstractType({ sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31" }, entityStringEqual_impl, entityStringLessThan_impl, entityStringDisplay_impl, "NSCore::String") 
    {
        static_assert(sizeof(BSQString) == 16);
    }

    virtual ~BSQStringType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, {0});
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, SLPTR_LOAD_CONTENTS_AS(BSQString, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, SLPTR_LOAD_CONTENTS_AS(BSQString, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
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

class BSQByteBufferType : public BSQEntityAbstractType
{
public:
    BSQByteBufferType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_BYTEBUFFER, BSQTypeKind::Ref, { sizeof(BSQByteBuffer), sizeof(void*), sizeof(void*), "2" }, "2", {}, entityByteBufferDisplay_impl, "NSCore::ByteBuffer", {}, {}, {}) {;}

    virtual ~BSQByteBufferType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }
};

////
//ISOTime
typedef uint64_t BSQISOTime;

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQISOTimeType : public BSQEntityAbstractType
{
public:
    BSQISOTimeType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_ISOTIME, BSQTypeKind::Register, { sizeof(BSQISOTime), sizeof(BSQISOTime), sizeof(BSQISOTime), "1" }, {}, entityISOTimeDisplay_impl, "NSCore::ISOTime", {}, {}, {}) {;}
    
    virtual ~BSQISOTimeType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQISOTime, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQISOTime, trgt, SLPTR_LOAD_CONTENTS_AS(BSQISOTime, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQISOTime, trgt, SLPTR_LOAD_CONTENTS_AS(BSQISOTime, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQISOTime, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQISOTime, src));
    }
};

////
//LogicalTime
typedef uint64_t BSQLogicalTime;

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityLogicalTimeEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityLogicalTimeLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQLogicalTimeType : public BSQEntityAbstractType
{
public:
    BSQLogicalTimeType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_LOGICALTIME, BSQTypeKind::Register, { sizeof(BSQLogicalTime), sizeof(BSQLogicalTime), sizeof(BSQLogicalTime), "1"}, {}, entityLogicalTimeEqual_impl, entityLogicalTimeLessThan_impl, entityLogicalTimeDisplay_impl, "NSCore::LogicalTime", {}, {}, {}) {;}

    virtual ~BSQLogicalTimeType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQLogicalTime, trgt, 0);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQLogicalTime, trgt, SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQLogicalTime, trgt, SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQLogicalTime, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQLogicalTime, src));
    }

    inline static bool equal(BSQLogicalTime v1, BSQLogicalTime v2) { return v1 == v2; }
    inline static bool lessThan(BSQLogicalTime v1, BSQLogicalTime v2) { return v1 < v2; }
};

////
//UUID
typedef boost::uuids::uuid BSQUUID;

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityUUIDEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityUUIDLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQUUIDType : public BSQEntityAbstractType
{
public:
    BSQUUIDType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_UUID, BSQTypeKind::Ref, { sizeof(BSQUUID), sizeof(void*), sizeof(void*), "2" }, {}, entityUUIDEqual_impl, entityUUIDLessThan_impl, entityUUIDDisplay_impl, "NSCore::UUID", {}, {}, {}) {;}
    
    virtual ~BSQUUIDType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    inline static bool equal(BSQUUID* v1, BSQUUID* v2) { return *v1 == *v2; }
    inline static bool lessThan(BSQUUID* v1, BSQUUID* v2) { return *v1 < *v2; }
};

////
//ContentHash
typedef boost::multiprecision::checked_uint512_t BSQContentHash;

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data);
bool entityContentHashEqual_impl(StorageLocationPtr data1, StorageLocationPtr data2);
bool entityContentHashLessThan_impl(StorageLocationPtr data1, StorageLocationPtr data2);

class BSQContentHashType : public BSQEntityAbstractType
{
public:
    BSQContentHashType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_CONTENTHASH, BSQTypeKind::Ref, { sizeof(BSQContentHash), sizeof(void*), sizeof(void*), "2" }, {}, entityContentHashEqual_impl, entityContentHashLessThan_impl, entityContentHashDisplay_impl, "NSCore::ContentHash", {}, {}, {}) {;}

    virtual ~BSQContentHashType() {;}

    inline static bool equal(BSQContentHash* v1, BSQContentHash* v2) { return *v1 == *v2; }
    inline static bool lessThan(BSQContentHash* v1, BSQContentHash* v2) { return *v1 < *v2; }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }
};

////
//Regex

struct BSQRegex
{
    std::string* strversion;
    std::regex* regex;
};

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRegexType : public BSQEntityAbstractType
{
public:
    BSQRegexType() 
    : BSQEntityAbstractType(BSQ_TYPE_ID_REGEX, BSQTypeKind::Struct, { sizeof(BSQRegex), sizeof(BSQRegex), sizeof(BSQRegex), "11" }, {}, entityRegexDisplay_impl, "NSCore::Regex", {}, {}, {}) 
    {
        static_assert(sizeof(BSQRegex) == 16);
    }

    virtual ~BSQRegexType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRegex, trgt, {0});
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRegex, trgt, SLPTR_LOAD_CONTENTS_AS(BSQRegex, src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS(BSQRegex, trgt, SLPTR_LOAD_CONTENTS_AS(BSQRegex, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQRegex, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQRegex, src));
    }
};
