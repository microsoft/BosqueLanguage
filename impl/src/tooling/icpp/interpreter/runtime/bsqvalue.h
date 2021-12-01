//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "../core/bsqmemory.h"

////
//Primitive value representations

////
//None
typedef uint64_t BSQNone;
#define BSQNoneValue 0
#define BSQNoneHeapValue nullptr

std::string entityNoneDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityNoneKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQNoneType : public BSQRegisterType<BSQNone>
{
public:
    BSQNoneType(): BSQRegisterType(BSQ_TYPE_ID_NONE, sizeof(BSQNone), "1", entityNoneKeyCmp_impl, entityNoneDisplay_impl, "NSCore::None")
    {
        static_assert(sizeof(BSQNone) == 8);
    }

    virtual ~BSQNoneType() {;}
};

////
//Nothing
typedef uint64_t BSQNothing;
#define BSQNothingValue 0
#define BSQNothingHeapValue nullptr

std::string entityNothingDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQNothingType : public BSQRegisterType<BSQNothing>
{
public:
    BSQNothingType(): BSQRegisterType(BSQ_TYPE_ID_NOTHING, sizeof(BSQNothing), "1", EMPTY_KEY_CMP, entityNothingDisplay_impl, "NSCore::Nothing")
    {
        static_assert(sizeof(BSQNone) == 8);
    }

    virtual ~BSQNothingType() {;}
};

////
//Bool

typedef uint8_t BSQBool;
#define BSQTRUE ((BSQBool)1)
#define BSQFALSE ((BSQBool)0)

std::string entityBoolDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityBoolKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBoolType : public BSQRegisterType<BSQBool>
{
public:
    BSQBoolType(): BSQRegisterType(BSQ_TYPE_ID_BOOL, sizeof(BSQBool), "1", entityBoolKeyCmp_impl, entityBoolDisplay_impl, "NSCore::Bool")
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

class BSQNatType : public BSQRegisterType<BSQNat>
{
public:
    BSQNatType(): BSQRegisterType(BSQ_TYPE_ID_NAT, sizeof(BSQNat), "1", entityNatKeyCmp_impl, entityNatDisplay_impl, "NSCore::Nat")
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

class BSQIntType : public BSQRegisterType<BSQInt>
{
public:
    BSQIntType(): BSQRegisterType(BSQ_TYPE_ID_INT, sizeof(BSQInt), "1", entityIntKeyCmp_impl, entityIntDisplay_impl, "NSCore::Int")
    {
        static_assert(sizeof(BSQInt) == 8);
    }

    virtual ~BSQIntType() {;}
};

////
//BigNat
typedef uint64_t BSQBigNat;

//
//TODO: change impl to something like for strings (an inline verison with maybe 128 or 196 bits + some heap allocated support)
//

std::string entityBigNatDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityBigNatKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigNatType : public BSQBigNumType<BSQBigNat>
{
public:
    BSQBigNatType(): BSQBigNumType(BSQ_TYPE_ID_BIGNAT, sizeof(BSQBigNat), "4", entityBigNatKeyCmp_impl, entityBigNatDisplay_impl, "NSCore::BigNat")
    {
        static_assert(sizeof(BSQNone) == 8);
    }

    virtual ~BSQBigNatType() {;}
};

////
//BigInt
typedef int64_t BSQBigInt;

//
//TODO: change impl to something like for strings (an inline verison with maybe 128 or 196 bits + some heap allocated support)
//

std::string entityBigIntDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityBigIntKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQBigIntType : public BSQBigNumType<BSQBigInt>
{
public:
    BSQBigIntType(): BSQBigNumType(BSQ_TYPE_ID_BIGINT, sizeof(BSQBigInt), "4", entityBigIntKeyCmp_impl, entityBigIntDisplay_impl, "NSCore::BigInt")
    {
        static_assert(sizeof(BSQNone) == 8);
    }

    virtual ~BSQBigIntType() {;}
};

////
//Float
typedef double BSQFloat;

std::string entityFloatDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQFloatType: public BSQRegisterType<BSQFloat>
{
public:
    BSQFloatType(): BSQRegisterType(BSQ_TYPE_ID_FLOAT, sizeof(BSQFloat), "1", EMPTY_KEY_CMP, entityFloatDisplay_impl, "NSCore::Float") 
    {
        static_assert(sizeof(BSQFloat) == 8);
    }

    virtual ~BSQFloatType() {;}
};

////
//Decimal
typedef double BSQDecimal;

//
//TODO: we need to get a better library later maybe use something like -- /https://github.com/dotnet/runtime/blob/main/src/libraries/System.Private.CoreLib/src/System/Decimal.cs
//

std::string entityDecimalDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQDecimalType : public BSQRegisterType<BSQDecimal>
{
public:
    BSQDecimalType() : BSQRegisterType(BSQ_TYPE_ID_DECIMAL, sizeof(BSQDecimal), "1" , EMPTY_KEY_CMP, entityDecimalDisplay_impl, "NSCore::Decimal")
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

class BSQRationalType : public BSQRegisterType<BSQRational>
{
public:
    BSQRationalType() : BSQRegisterType(BSQ_TYPE_ID_RATIONAL, sizeof(BSQRational), "41", EMPTY_KEY_CMP, entityRationalDisplay_impl, "NSCore::Rational") 
    {
        static_assert(sizeof(BSQRational) == 16);
    }

    virtual ~BSQRationalType() {;}
};

////
//String
struct BSQInlineString
{
    uint8_t utf8bytes[16];

    inline static BSQInlineString create(const uint8_t* chars, uint64_t len)
    {
        BSQInlineString istr = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (uint8_t)len};
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
    BSQStringReprType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name):
        BSQRefType(tid, allocsize, heapmask, {}, EMPTY_KEY_CMP, entityStringReprDisplay_impl, name) 
    {;}

    virtual ~BSQStringReprType() {;}

    virtual uint64_t utf8ByteCount(void* repr) const = 0;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const = 0;
};

class BSQStringKReprTypeAbstract : public BSQStringReprType
{
public:
    BSQStringKReprTypeAbstract(BSQTypeID tid, uint64_t allocsize, std::string name) 
    : BSQStringReprType(tid, allocsize, nullptr, name) 
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

    inline static const BSQStringKReprTypeAbstract* selectKReprForSize(size_t k)
    {
        auto stp = std::find_if(BSQType::g_typeStringKCons, BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons), [&k](const std::pair<size_t, const BSQType*>& cc) {
            return cc.first > k;
        });
    
        assert(stp != BSQType::g_typeStringKCons + sizeof(BSQType::g_typeStringKCons));
        return static_cast<const BSQStringKReprTypeAbstract*>(stp->second);
    }

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};

template <uint64_t k>
class BSQStringKReprType : public BSQStringKReprTypeAbstract
{
public:
    BSQStringKReprType(BSQTypeID tid): BSQStringKReprTypeAbstract(tid, k, "[Internal::StringKRepr]") 
    {;}

    virtual ~BSQStringKReprType() {;}
};

struct BSQStringTreeRepr
{
    void* srepr1;
    void* srepr2;
    uint64_t size;
};

class BSQStringTreeReprType : public BSQStringReprType
{
public:
    BSQStringTreeReprType(): BSQStringReprType(BSQ_TYPE_ID_STRINGREPR_TREE, sizeof(BSQStringTreeRepr), "22", "[Internal::StringConcatRepr]") 
    {;}

    virtual ~BSQStringTreeReprType() {;}

    uint64_t utf8ByteCount(void* repr) const override final
    {
        return ((BSQStringTreeRepr*)repr)->size;
    }

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};

struct BSQString
{
    union { void* u_data; BSQInlineString u_inlineString; };
};
constexpr BSQString g_emptyString = {0};

class BSQStringForwardIterator : public CharCodeIterator
{
private:
    void initializeIteratorPosition(int64_t curr);

    void increment_utf8byte();

public:
    BSQString* sstr;
    size_t curr;
    size_t strmax;
    uint8_t* cbuff;
    uint16_t cpos;
    uint16_t maxpos;

    BSQStringForwardIterator(BSQString* sstr, int64_t curr) : CharCodeIterator(), sstr(sstr), curr(curr), strmax(0), cbuff(nullptr), cpos(0), maxpos(0) 
    {
        if(IS_INLINE_STRING(sstr))
        {
            this->strmax = BSQInlineString::utf8ByteCount(sstr->u_inlineString);
        }
        else
        {
            this->strmax = GET_TYPE_META_DATA_AS(BSQStringReprType, sstr->u_data)->utf8ByteCount(sstr->u_data);
        }

        this->initializeIteratorPosition(curr);
    }
    
    virtual ~BSQStringForwardIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != this->strmax;
    }

    virtual void advance() override final
    {
        assert(this->valid());

        auto utfbyte = this->cbuff[this->cpos];
        if((utfbyte & 0x8) == 0) [[likely]]
        {
            this->increment_utf8byte();
        }
        else [[unlikely]]
        {
            //not implemented
            assert(false);
        }
    }

    virtual CharCode get() const override final
    {
        assert(this->valid());

        auto utfbyte = this->cbuff[this->cpos];
        if((utfbyte & 0x8) == 0) [[likely]]
        {
            return (CharCode)utfbyte;
        }
        else [[unlikely]]
        {
            //not implemented
            assert(false);
        }
    }

    virtual size_t distance() const override final
    {
        return this->curr;
    }

    virtual void resetTo(size_t distance) override final
    {
        this->initializeIteratorPosition(distance);
    }

    void advance_byte()
    {
        assert(this->valid());
        this->increment_utf8byte();
    } 

    uint8_t get_byte() const
    {
        assert(this->valid());
        return this->cbuff[this->cpos];
    }
};

class BSQStringReverseIterator : public CharCodeIterator
{
private:
    void initializeIteratorPosition(int64_t curr);
    
    void increment_utf8byte();
public:
    BSQString* sstr;
    int64_t curr;
    int64_t strmax;
    uint8_t* cbuff;
    uint16_t cpos;

    BSQStringReverseIterator(BSQString* sstr, int64_t curr) : CharCodeIterator(), sstr(sstr), curr(curr), strmax(strmax), cbuff(nullptr), cpos(0) 
    {
        if(IS_INLINE_STRING(sstr))
        {
            this->strmax = (int64_t)BSQInlineString::utf8ByteCount(sstr->u_inlineString);
        }
        else
        {
            this->strmax = (int64_t)GET_TYPE_META_DATA_AS(BSQStringReprType, sstr->u_data)->utf8ByteCount(sstr->u_data);
        }

        this->initializeIteratorPosition(curr);
        if(curr == strmax - 1)
        {
            auto utfbyte = this->cbuff[this->cpos];
            if((utfbyte & 0x8) == 1)
            {
                //not implemented
                assert(false);
            }
        }
    }

    virtual ~BSQStringReverseIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != -1;
    }

    virtual void advance() override final
    {
        assert(this->valid());
        this->increment_utf8byte();

        if(this->valid()) [[likely]]
        {
            auto utfbyte = this->cbuff[this->cpos];
            if((utfbyte & 0x8) == 1) [[unlikely]]
            {
                //not implemented
                assert(false);
            }
        }
    }

    virtual CharCode get() const override final
    {
        assert(this->valid());

        auto utfbyte = this->cbuff[this->cpos];
        if((utfbyte & 0x8) == 0) [[likely]]
        {
            return (CharCode)utfbyte;
        }
        else [[unlikely]]
        {
            //not implemented
            assert(false);
        }
    }

    virtual size_t distance() const override final
    {
        return this->strmax - (this->curr + 1);
    }

    virtual void resetTo(size_t distance) override final
    {
        this->initializeIteratorPosition(this->strmax - (distance + 1));
    }

    void advance_byte()
    {
        assert(this->valid());
        this->increment_utf8byte();
    } 

    uint8_t get_byte() const
    {
        assert(this->valid());
        return this->cbuff[this->cpos];
    } 
};

std::string entityStringDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityStringKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQStringType : public BSQType
{
private:
    static uint8_t* boxInlineString(BSQInlineString istr);

public:
    BSQStringType() 
    : BSQType(BSQ_TYPE_ID_STRING, BSQTypeLayoutKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityStringDisplay_impl, "NSCore::String")
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

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(BSQString, trgt, SLPTR_LOAD_CONTENTS_AS(BSQString, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(BSQString, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(BSQString, src));
    }

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
    static BSQString slice(StorageLocationPtr str, int64_t startpos, int64_t endpos);
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
    xxxx; //need to fix this to have encoding info too
public:
    BSQByteBufferType(): BSQRefType(BSQ_TYPE_ID_BYTEBUFFER, sizeof(BSQByteBuffer), "2", {}, EMPTY_KEY_CMP, entityByteBufferDisplay_impl, "NSCore::ByteBuffer") {;}

    virtual ~BSQByteBufferType() {;}
};

////
//ISOTime
struct BSQTimeData
{
    uint16_t millis; // 0-999
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
    uint8_t hour;    // 0-23
    uint8_t min;     // 0-59
    uint8_t sec;     // 0-60
};

std::string entityISOTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQISOTimeType : public BSQRegisterType<BSQTimeData>
{
public:
    BSQISOTimeType(): BSQRegisterType(BSQ_TYPE_ID_ISOTIME, 24, "111", EMPTY_KEY_CMP, entityISOTimeDisplay_impl, "NSCore::ISOTime") 
    {
        static_assert(sizeof(BSQTimeData) <= 24);
    }
    
    virtual ~BSQISOTimeType() {;}
};

////
//LogicalTime
typedef uint64_t BSQLogicalTime;

std::string entityLogicalTimeDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityLogicalTimeKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQLogicalTimeType : public BSQRegisterType<BSQLogicalTime>
{
public:
    BSQLogicalTimeType(): BSQRegisterType(BSQ_TYPE_ID_LOGICALTIME, sizeof(BSQLogicalTime), "1", entityLogicalTimeKeyCmp_impl, entityLogicalTimeDisplay_impl, "NSCore::LogicalTime") 
    {
        static_assert(sizeof(BSQLogicalTime) == 8);
    }

    virtual ~BSQLogicalTimeType() {;}
};

////
//UUID
typedef struct { uint8_t bytes[16]; } BSQUUID;

std::string entityUUIDDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityUUIDKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQUUIDType : public BSQRegisterType<BSQUUID>
{
public:
    BSQUUIDType(): BSQRegisterType(BSQ_TYPE_ID_UUID, sizeof(BSQUUID), "11", entityUUIDKeyCmp_impl, entityUUIDDisplay_impl, "NSCore::UUID") {;}
    
    virtual ~BSQUUIDType() {;}
};

////
//ContentHash
typedef struct { uint8_t bytes[64]; } BSQContentHash;

std::string entityContentHashDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int entityContentHashKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQContentHashType : public BSQRefType
{
public:
    BSQContentHashType(): BSQRefType(BSQ_TYPE_ID_CONTENTHASH, sizeof(BSQContentHash), nullptr, {}, entityContentHashKeyCmp_impl, entityContentHashDisplay_impl, "NSCore::ContentHash") {;}

    virtual ~BSQContentHashType() {;}
};

////
//Regex

std::string entityRegexDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRegexType : public BSQRegisterType<void*>
{
public:
    BSQRegexType(): BSQRegisterType(BSQ_TYPE_ID_REGEX, sizeof(void*), "1", EMPTY_KEY_CMP, entityRegexDisplay_impl, "NSCore::Regex") {;}
    virtual ~BSQRegexType() {;}
};

std::string entityValidatorDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQValidatorType : public BSQRegisterType<void*>
{
public:
    const BSQRegex* re;

    BSQValidatorType(BSQTypeID tid, std::string name, BSQRegex* re): BSQRegisterType(tid, sizeof(void*), "1", EMPTY_KEY_CMP, entityValidatorDisplay_impl, name), re(re) {;}
    virtual ~BSQValidatorType() {;}
};

std::string entityStringOfDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQStringOfType : public BSQType
{
public:
    const BSQTypeID validator;

    BSQStringOfType(BSQTypeID tid, std::string name, const BSQTypeID validator)
    : BSQType(tid, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityStringOfDisplay_impl, name), validator(validator)
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

class BSQDataStringType : public BSQType
{
public:
    const BSQInvokeID parsemethod;

    BSQDataStringType(BSQTypeID tid, std::string name, BSQInvokeID parsemethod)
    : BSQType(tid, BSQTypeKind::String, {sizeof(BSQString), sizeof(BSQString), sizeof(BSQString), "31", "31"}, { gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl }, {}, entityStringKeyCmp_impl, entityDataStringDisplay_impl, name), parsemethod(parsemethod)
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
    : BSQRegisterType<T>(tid, primitive->allocinfo.inlinedatasize, primitive->allocinfo.inlinedmask, primitive->fpkeycmp, entityTypedNumberDisplay_impl, name), 
    BSQTypedNumberTypeAbstract(underlying)
    {;}

    virtual ~BSQTypedNumberType() {;}
};

template <typename T>
class BSQTypedBigNumberType : public BSQBigNumType<T>, public BSQTypedNumberTypeAbstract
{
public:
    BSQTypedBigNumberType(BSQTypeID tid, std::string name, BSQTypeID underlying, const BSQType* primitive)
    : BSQBigNumType<T>(tid, primitive->allocinfo.inlinedatasize, primitive->allocinfo.inlinedmask, primitive->fpkeycmp, entityTypedNumberDisplay_impl, name), 
    BSQTypedNumberTypeAbstract(underlying)
    {;}

    virtual ~BSQTypedBigNumberType() {;}
};

std::string enumDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEnumType : public BSQStructType
{
public:
    const BSQType* underlying;
    const std::vector<std::pair<std::string, uint32_t>> enuminvs; //map from full enum names to the constant storage location

    BSQEnumType(BSQTypeID tid, std::string name, const BSQType* underlying, std::vector<std::pair<std::string, BSQInvokeID>> enuminvs)
    : BSQStructType(tid, underlying->allocinfo.inlinedatasize, underlying->allocinfo.inlinedmask, {}, underlying->fpkeycmp, enumDisplay_impl, name),
    enuminvs(enuminvs)
    {;}

    virtual ~BSQEnumType() {;}
};
