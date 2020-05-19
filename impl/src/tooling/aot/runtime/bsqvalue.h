//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

////
//Value ops

#define MIN_BSQ_INT -9007199254740991
#define MAX_BSQ_INT 9007199254740991

#define INT_OOF_BOUNDS(X) (((X) < MIN_BSQ_INT) | ((X) > MAX_BSQ_INT))

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_TAGGED_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_TAGGED_INT(V) (int64_t)(((int64_t)(V)) >> 0x3)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_TAGGED_INT(I) ((void*)((((uint64_t) I) << 0x3) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(true)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(false)

////
//Reference counting ops

#define BSQ_NEW_NO_RC(T, ...) (new T(__VA_ARGS__))
#define BSQ_NEW_ADD_SCOPE(SCOPE, T, ...) ((T*)((SCOPE).addAllocRefDirect(BSQ_NEW_NO_RC(T, __VA_ARGS__))))

#define INC_REF_DIRECT(T, V) ((T*) BSQRef::incrementDirect(V))
#define INC_REF_CHECK(T, V) ((T*) BSQRef::incrementChecked(V))

////
//Type ops

//Note POD => API
typedef uint32_t DATA_KIND_FLAG;
#define DATA_KIND_CLEAR_FLAG 0x0
#define DATA_KIND_API_FLAG 0x1
#define DATA_KIND_POD_FLAG 0x3
#define DATA_KIND_PARSABLE_FLAG 0x4
#define DATA_KIND_ALL_FLAG (DATA_KIND_API_FLAG | DATA_KIND_POD_FLAG | DATA_KIND_PARSABLE_FLAG)
#define DATA_KIND_UNKNOWN_FLAG 0xFF

#define DATA_KIND_COMPUTE(KF, COMP) (((KF) == DATA_KIND_UNKNOWN_FLAG) ? (COMP) : (KF)

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

//Category tags to embed in the type enums
#define MIRNominalTypeEnum_Category_Empty           0
#define MIRNominalTypeEnum_Category_BigInt          1
#define MIRNominalTypeEnum_Category_String          2
#define MIRNominalTypeEnum_Category_SafeString      3
#define MIRNominalTypeEnum_Category_StringOf        4
#define MIRNominalTypeEnum_Category_UUID            5
#define MIRNominalTypeEnum_Category_LogicalTime     6
#define MIRNominalTypeEnum_Category_CryptoHash      7
#define MIRNominalTypeEnum_Category_Enum            8
#define MIRNominalTypeEnum_Category_IdKeySimple     9
#define MIRNominalTypeEnum_Category_IdKeyCompound   10

#define MIRNominalTypeEnum_Category_KeyTypeLimit    MIRNominalTypeEnum_Category_IdKeyCompound

#define MIRNominalTypeEnum_Category_Float64         20
#define MIRNominalTypeEnum_Category_Buffer          21
#define MIRNominalTypeEnum_Category_BufferOf        22
#define MIRNominalTypeEnum_Category_ByteBuffer      23
#define MIRNominalTypeEnum_Category_ISOTime         24
#define MIRNominalTypeEnum_Category_Regex           25
#define MIRNominalTypeEnum_Category_Tuple           26
#define MIRNominalTypeEnum_Category_Record          27
#define MIRNominalTypeEnum_Category_Object          28

#define MIRNominalTypeEnum_Category_NormalTypeLimit MIRNominalTypeEnum_Category_Object

#define MIRNominalTypeEnum_Category_List            40
#define MIRNominalTypeEnum_Category_Stack           41
#define MIRNominalTypeEnum_Category_Queue           42
#define MIRNominalTypeEnum_Category_Set             43
#define MIRNominalTypeEnum_Category_DynamicSet      44
#define MIRNominalTypeEnum_Category_Map             45
#define MIRNominalTypeEnum_Category_DynamicMap      46

#define BUILD_MIR_NOMINAL_TYPE(C, T) ((T << 8) | C)
#define GET_MIR_TYPE_CATEGORY(T) (((int32_t)(T)) & 0xFF)
#define GET_MIR_TYPE_POSITION(T) (((int32_t)(T)) >> 8)

enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE%%
};

constexpr const char* propertyNames[] = {
    "Invalid",
//%%PROPERTY_NAMES%%
};

constexpr const char* nominaltypenames[] = {
    "[INVALID]",
//%%NOMINAL_TYPE_DISPLAY_NAMES%%
};

//%%CONCEPT_SUBTYPE_RELATION_DECLARE%%

constexpr DATA_KIND_FLAG nominalDataKinds[] = {
  DATA_KIND_CLEAR_FLAG,
//%%NOMINAL_TYPE_TO_DATA_KIND%%
};

//%%SPECIAL_NAME_BLOCK_BEGIN%%
#define MIRNominalTypeEnum_None MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Bool MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Int MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_BigInt MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Float64 MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_String MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_UUID MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ByteBuffer MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Regex MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Tuple MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Record MIRNominalTypeEnum::Invalid
//%%SPECIAL_NAME_BLOCK_END%%

typedef void* NoneValue;
typedef void* KeyValue;
typedef void* Value;

class BSQRef
{
private:
    uint64_t count;

public:
    MIRNominalTypeEnum nominalType;

    BSQRef() : count(0), nominalType(MIRNominalTypeEnum::Invalid) { ; }
    BSQRef(MIRNominalTypeEnum nominalType) : count(0), nominalType(nominalType) { ; }
    BSQRef(int64_t excount, MIRNominalTypeEnum nominalType) : count(excount), nominalType(nominalType) { ; }

    virtual ~BSQRef() { ; }
    virtual void destroy() { ; }

    inline void increment()
    {
        this->count++;
    }

    inline void decrement()
    {
        this->count--;

        if(this->count == 0)
        {
            this->destroy();
            BSQ_DELETE(this);    
        }
    }

    inline static void* incrementDirect(void* v)
    {
        ((BSQRef*)v)->increment();
        return v;
    }

    inline static Value incrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->increment();
        }
        return v;
    }

    inline static void decrementDirect(void* v)
    {
        ((BSQRef*)v)->decrement();
    }

    inline static void decrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->decrement();
        }
    }
};

class BSQRefScope
{
private:
    std::vector<BSQRef*> opts;

public:
    BSQRefScope() : opts()
    {
        ;
    }

    ~BSQRefScope()
    {
        for(uint16_t i = 0; i < this->opts.size(); ++i)
        {
           this->opts[i]->decrement();
        }
    }

    inline BSQRef* addAllocRefDirect(BSQRef* ptr)
    {
        ptr->increment();
        this->opts.push_back(ptr);

        return ptr;
    }

    inline Value addAllocRefChecked(Value v)
    {
        if (BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef* ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
            ptr->increment();
            this->opts.push_back(ptr);
        }

        return v;
    }

    inline void callReturnDirect(BSQRef* ptr)
    {
        ptr->increment();
        this->opts.push_back(ptr);
    }

    inline void processReturnChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef* ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
            ptr->increment();
            this->opts.push_back(ptr);
        }
    }
};

template <typename T, typename DestroyFunctor>
class BSQBoxed : public BSQRef
{
public:
    T bval;

    BSQBoxed(MIRNominalTypeEnum nominalType, const T& bval) : BSQRef(nominalType), bval(bval) { ; }
    virtual ~BSQBoxed() { ; }

    virtual void destroy() 
    { 
        DestroyFunctor{}(this->bval); 
    }
};

struct RCIncFunctor_NoneValue
{
    inline void* operator()(NoneValue n) const { return n; }
};
struct RCDecFunctor_NoneValue
{
    inline void operator()(NoneValue n) const { ; }
};
struct RCReturnFunctor_NoneValue
{
    inline void operator()(NoneValue& e, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return true; }
};
struct LessFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return false; }
};
struct DisplayFunctor_NoneValue
{
    std::string operator()(NoneValue n) const { return "none"; }
};

struct RCIncFunctor_bool
{
    inline bool operator()(bool b) const { return b; }
};
struct RCDecFunctor_bool
{
    inline void operator()(bool b) const { ; }
};
struct RCReturnFunctor_bool
{
    inline void operator()(bool b, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_bool
{
    inline bool operator()(bool l, bool r) const { return l == r; }
};
struct LessFunctor_bool
{
    inline bool operator()(bool l, bool r) const { return (!l) & r; }
};
struct DisplayFunctor_bool
{
    std::string operator()(bool b) const { return b ? "true" : "false"; }
};

struct RCIncFunctor_int64_t
{
    inline int64_t operator()(int64_t i) const { return i; }
};
struct RCDecFunctor_int64_t
{
    inline void operator()(int64_t i) const { ; }
};
struct RCReturnFunctor_int64_t
{
    inline void operator()(int64_t i, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l == r; }
};
struct LessFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l < r; }
};
struct DisplayFunctor_int64_t
{
    std::string operator()(int64_t i) const 
    {
        return std::to_string(i);  
    }
};

struct RCIncFunctor_double
{
    inline double operator()(double d) const { return d; }
};
struct RCDecFunctor_double
{
    inline void operator()(double d) const { ; }
};
struct RCReturnFunctor_double
{
    inline void operator()(double d, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_double
{
    std::string operator()(double d) const 
    {
        return std::to_string(d);  
    }
};
typedef BSQBoxed<double, RCDecFunctor_double> Boxed_double;

MIRNominalTypeEnum getNominalTypeOf_KeyValue(KeyValue v);
MIRNominalTypeEnum getNominalTypeOf_Value(Value v);

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);
bool bsqKeyValueLess(KeyValue v1, KeyValue v2);

DATA_KIND_FLAG getDataKindFlag(Value v);

std::string diagnostic_format(Value v);

struct RCIncFunctor_BSQRef
{
    inline BSQRef* operator()(BSQRef* r) const { return INC_REF_DIRECT(BSQRef, r); }
};
struct RCDecFunctor_BSQRef
{
    inline void operator()(BSQRef* r) const { BSQRef::decrementDirect(r); }
};
struct DisplayFunctor_BSQRef
{
    std::string operator()(BSQRef* r) const { return diagnostic_format(r); }
};

struct RCIncFunctor_KeyValue
{
    inline KeyValue operator()(KeyValue k) const { return INC_REF_CHECK(KeyValue, k); }
};
struct RCDecFunctor_KeyValue
{
    inline void operator()(KeyValue k) const { BSQRef::decrementChecked(k); }
};
struct EqualFunctor_KeyValue
{
    bool operator()(KeyValue l, KeyValue r) const { return bsqKeyValueEqual(l, r); }
};
struct LessFunctor_KeyValue
{
    bool operator()(KeyValue l, KeyValue r) const { return bsqKeyValueLess(l, r); }
};
struct DisplayFunctor_KeyValue
{
    std::string operator()(KeyValue k) const { return diagnostic_format(k); }
};

struct RCIncFunctor_Value
{
    inline Value operator()(Value v) const { return INC_REF_CHECK(Value, v); }
};
struct RCDecFunctor_Value
{
    inline void operator()(Value v) const { BSQRef::decrementChecked(v); }
};
struct DisplayFunctor_Value
{
    std::string operator()(Value v) const { return diagnostic_format(v); }
};

enum class BSQBufferFormat {
    Char,
    Bosque,
    EBosque,
    Json
};

enum class BSQBufferEncoding {
    UTF8,
    URI,
    Base64,
    Binary
};

enum class BSQBufferCompression {
    Off,
    RLE,
    Time,
    Space
};

class BSQByteBuffer : public BSQRef
{
public:
    const BSQBufferCompression compression;

    const std::vector<uint8_t> sdata;

    BSQByteBuffer(BSQBufferCompression compression, std::vector<uint8_t>&& sdata) : BSQRef(MIRNominalTypeEnum_ByteBuffer), compression(compression), sdata(move(sdata)) { ; }
    
    virtual ~BSQByteBuffer() = default;
    virtual void destroy() { ; }

    std::string display_contents() const
    {
        std::string rvals("");
        if(this->compression == BSQBufferCompression::Off)
        {
            rvals += std::string((char*)this->sdata.data(), (char*)this->sdata.data() + this->sdata.size());
        }
        else
        {
            for (size_t i = 0; i < this->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += this->sdata[i];
            }
        }
        return rvals;
    }
};
struct DisplayFunctor_BSQByteBuffer
{
    std::string operator()(const BSQByteBuffer* bb) const 
    {
        std::string rvals("ByteBuffer{");
        rvals += bb->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQBuffer : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;

    BSQByteBuffer* sdata;

    BSQBuffer(BSQBufferFormat format, BSQBufferEncoding encoding, BSQByteBuffer* sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), sdata(sdata) { ; }
    
    virtual ~BSQBuffer() = default;
    
    virtual void destroy() 
    { 
        BSQRef::decrementDirect(this->sdata);
    }
};
struct DisplayFunctor_BSQBuffer
{
    std::string operator()(const BSQBuffer* buff) const 
    {
        std::string rvals(nominaltypenames[GET_MIR_TYPE_POSITION(buff->nominalType)]);
        rvals += "{";
        rvals += buff->sdata->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQBufferOf : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;

    BSQByteBuffer* sdata;

    BSQBufferOf(BSQBufferFormat format, BSQBufferEncoding encoding, BSQByteBuffer* sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), sdata(sdata) { ; }
    
    virtual ~BSQBufferOf() = default;
    
    virtual void destroy() 
    { 
        BSQRef::decrementDirect(this->sdata);
    }
};
struct DisplayFunctor_BSQBufferOf
{
    std::string operator()(const BSQBufferOf* buff) const 
    {
        std::string rvals(nominaltypenames[GET_MIR_TYPE_POSITION(buff->nominalType)]);
        rvals += "{";
        rvals += buff->sdata->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQISOTime
{
public:
    uint64_t isotime;

    BSQISOTime() { ; }
    BSQISOTime(uint64_t isotime) : isotime(isotime) { ; }

    BSQISOTime(const BSQISOTime& src) = default;
    BSQISOTime(BSQISOTime&& src) = default;

    BSQISOTime& operator=(const BSQISOTime& src) = default;
    BSQISOTime& operator=(BSQISOTime&& src) = default;
};
struct RCIncFunctor_BSQISOTime
{
    inline BSQISOTime operator()(BSQISOTime t) const { return t; }
};
struct RCDecFunctor_BSQISOTime
{
    inline void operator()(BSQISOTime t) const { ; }
};
struct RCReturnFunctor_BSQISOTime
{
    inline void operator()(BSQISOTime& t, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_BSQISOTime
{
    std::string operator()(const BSQISOTime& t) const 
    { 
        return std::string{"ISOTime={"} + std::to_string(t.isotime) + "}";
    }
};
typedef BSQBoxed<BSQISOTime, RCDecFunctor_BSQISOTime> Boxed_BSQISOTime;

class BSQRegex
{
public:
    const std::regex* re;

    BSQRegex() { ; }
    BSQRegex(std::regex* re) : re(re) { ; }

    BSQRegex(const BSQRegex& src) = default;
    BSQRegex(BSQRegex&& src) = default;

    BSQRegex& operator=(const BSQRegex& src) = default;
    BSQRegex& operator=(BSQRegex&& src) = default;
};
struct RCIncFunctor_BSQRegex
{
    inline BSQRegex operator()(BSQRegex re) const { return re; }
};
struct RCDecFunctor_BSQRegex
{
    inline void operator()(BSQRegex re) const { ; }
};
struct RCReturnFunctor_BSQRegex
{
    inline void operator()(BSQRegex& re, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_BSQRegex
{
    std::string operator()(const BSQRegex& r) const 
    { 
        return std::string{"[REGEX]"};
    }
};
typedef BSQBoxed<BSQRegex, RCDecFunctor_BSQRegex> Boxed_BSQRegex;

class BSQTuple : public BSQRef
{
public:
    std::vector<Value> entries;
    DATA_KIND_FLAG flag;

    BSQTuple() : BSQRef(MIRNominalTypeEnum_Tuple) { ; }
    BSQTuple(std::vector<Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Tuple), entries(move(entries)), flag(flag) { ; }

    BSQTuple(const BSQTuple& src) : BSQRef(MIRNominalTypeEnum_Tuple), entries(src.entries), flag(src.flag) { ; }
    BSQTuple(BSQTuple&& src) : BSQRef(MIRNominalTypeEnum_Tuple), entries(move(src.entries)), flag(src.flag) { ; }

    virtual ~BSQTuple() = default;
    
    virtual void destroy() 
    { 
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::decrementChecked(this->entries[i]);
        }
    }

    BSQTuple& operator=(const BSQTuple& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = src.entries;
        this->flag = src.flag;
        return *this;
    }

    BSQTuple& operator=(BSQTuple&& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = std::move(src.entries);
        this->flag = src.flag;
        return *this;
    }

    template <DATA_KIND_FLAG flag>
    inline static BSQTuple createFromSingle(std::vector<Value>&& values)
    {
        auto fv = flag;
        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < values.size(); ++i)
            {
                fv &= getDataKindFlag(values[i]);
            }
        }

        return BSQTuple(move(values), fv);
    }

    static BSQTuple _empty;

    template <uint16_t idx>
    inline bool hasIndex() const
    {
        return idx < this->entries.size();
    }

    template <uint16_t idx>
    inline Value atFixed() const
    {
        if (idx < this->entries.size())
        {
            return this->entries[idx];
        }
        else
        {
            return BSQ_VALUE_NONE;
        }
    }
};
struct RCIncFunctor_BSQTuple
{
    inline BSQTuple operator()(BSQTuple tt) const 
    { 
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            BSQRef::incrementChecked(tt.entries[i]);
        }
        return tt;
    }
};
struct RCDecFunctor_BSQTuple
{
    inline void operator()(BSQTuple tt) const 
    { 
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            BSQRef::decrementChecked(tt.entries[i]);
        }
    }
};
struct RCReturnFunctor_BSQTuple
{
    inline void operator()(BSQTuple& tt, BSQRefScope& scope) const 
    {
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            scope.processReturnChecked(tt.entries[i]);
        }
    }
};
struct DisplayFunctor_BSQTuple
{
    std::string operator()(const BSQTuple& tt) const 
    { 
        std::string tvals("[");
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            if(i != 0)
            {
                tvals += ", ";
            }

            tvals += diagnostic_format(tt.entries[i]);
        }
        tvals += "]";

        return tvals;
    }
};

class BSQRecord : public BSQRef
{
public:
    std::map<MIRPropertyEnum, Value> entries;
    DATA_KIND_FLAG flag;

    BSQRecord() : BSQRef(MIRNominalTypeEnum_Record) { ; }
    BSQRecord(std::map<MIRPropertyEnum, Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Record), entries(move(entries)), flag(flag) { ; }

    BSQRecord(const BSQRecord& src) : BSQRef(MIRNominalTypeEnum_Record), entries(src.entries), flag(src.flag) { ; }
    BSQRecord(BSQRecord&& src) : BSQRef(MIRNominalTypeEnum_Record), entries(move(src.entries)), flag(src.flag) { ; }

    virtual ~BSQRecord() = default;
    
    virtual void destroy() 
    { 
        for(auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            BSQRef::decrementChecked(iter->second);
        }
    }

    BSQRecord& operator=(const BSQRecord& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = src.entries;
        this->flag = src.flag;
        return *this;
    }

    BSQRecord& operator=(BSQRecord&& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = std::move(src.entries);
        this->flag = src.flag;
        return *this;
    }

    template <DATA_KIND_FLAG flag>
    static BSQRecord createFromSingle(std::map<MIRPropertyEnum, Value>&& values)
    {
        auto fv = flag;
        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
            {
                fv &= getDataKindFlag(iter->second);
            }
        }

        return BSQRecord(move(values), fv);
    }

    template <DATA_KIND_FLAG flag>
    static BSQRecord createFromUpdate(const BSQRecord* src, std::map<MIRPropertyEnum, Value>&& values)
    {
        std::map<MIRPropertyEnum, Value> entries(move(values));
        auto fv = flag;

        for(auto iter = src->entries.begin(); iter != src->entries.end(); ++iter) {
            auto pos = values.lower_bound(iter->first);
            if(pos != src->entries.cend() && pos->first != iter->first)
            {
                values.emplace_hint(pos, *iter);
            }
        }

        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
            {
                fv &= getDataKindFlag(iter->second);
            }
        }

        return BSQRecord(move(values), fv);
    }

    static BSQRecord _empty;

    template <MIRPropertyEnum p>
    inline bool hasProperty() const
    {
        return this->entries.find(p) != this->entries.end();
    }

    template <MIRPropertyEnum p>
    inline Value atFixed() const
    {
        auto iter = this->entries.find(p);
        return iter != this->entries.end() ? iter->second : BSQ_VALUE_NONE;
    }

    bool checkPropertySet(int n, ...) const
    {
        MIRPropertyEnum val;
        std::set<MIRPropertyEnum> props;

        va_list vl;
        va_start(vl, n);
        for (int i = 0; i < n; i++)
        {
            val = va_arg(vl, MIRPropertyEnum);
            props.insert(val);
        }
        va_end(vl);

        for(auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter) {
            if(props.find(iter->first) == props.cend()) {
                return false;
            }
        }

        return true;
    }
};
struct RCIncFunctor_BSQRecord
{
    inline BSQRecord operator()(BSQRecord rr) const 
    { 
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
           BSQRef::incrementChecked(iter->second);
        }
        return rr;
    }
};
struct RCDecFunctor_BSQRecord
{
    inline void operator()(BSQRecord rr) const 
    { 
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
           BSQRef::decrementChecked(iter->second);
        }
    }
};
struct RCReturnFunctor_BSQRecord
{
    inline void operator()(BSQRecord& rr, BSQRefScope& scope) const 
    {
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
            scope.processReturnChecked(iter->second);
        } 
    }
};
struct DisplayFunctor_BSQRecord
{
    std::string operator()(const BSQRecord& rr) const 
    { 
        std::string rvals("{");
        bool first = true;
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
            if(!first)
            {
                rvals += ", ";
            }
            first = false;

            rvals += std::string{propertyNames[(int32_t)iter->first]} + "=" + diagnostic_format(iter->second);
        }
        rvals += "}";

        return rvals;
    }
};

class BSQObject : public BSQRef
{
public:
    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(ntype) { ; }
    virtual ~BSQObject() = default;

    virtual std::string display() const = 0;

    template<int32_t k>
    inline static bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
    {
        if constexpr (k < 16)
        {
            for(int32_t i = 0; i < k; ++i)
            {
                if(etypes[i] == tt)
                {
                    return true;
                }
            }
            return false;
        }
        else
        {
            return BSQObject::checkSubtypeSlow<k>(tt, etypes);
        }
    }

    template<int32_t k>
    static bool checkSubtypeSlow(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
    {
        return std::binary_search(&etypes[0], &etypes[k], tt); 
    }
};

template <typename T, typename DestroyFunctor>
class BSQBoxedObject : public BSQObject
{
public:
    T bval;

    BSQBoxedObject(MIRNominalTypeEnum nominalType, const T& bval) : BSQObject(nominalType), bval(bval) { ; }
    virtual ~BSQBoxedObject() { ; }

    virtual void destroy() 
    { 
        DestroyFunctor{}(this->bval); 
    }
};
} // namespace BSQ
