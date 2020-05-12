//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

////
//Value ops

#define MIN_BSQINT -9007199254740991
#define MAX_BSQINT 9007199254740991

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

#define HASH_COMBINE(H1, H2) (((527 + H1) * 31) + H2)

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
#define DATA_KIND_UNKNOWN_FLAG 0xF

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

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
#define MIRNominalTypeEnum_String MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_GUID MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_DataHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Tuple MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Regex MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Record MIRNominalTypeEnum::Invalid
//%%SPECIAL_NAME_BLOCK_END%%

typedef void* KeyValue;
typedef void* Value;

class BSQRef
{
private:
    int64_t count;

public:
    MIRNominalTypeEnum nominalType;

    BSQRef(MIRNominalTypeEnum nominalType) : count(0), nominalType(nominalType) { ; }
    BSQRef(int64_t excount, MIRNominalTypeEnum nominalType) : count(excount), nominalType(nominalType) { ; }
    virtual ~BSQRef() { ; }

    virtual void destroy() = 0;

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

struct HashFunctor_bool
{
    size_t operator()(bool b) const { return (size_t)b; }
};
struct EqualFunctor_bool
{
    bool operator()(bool l, bool r) const { return l == r; }
};
struct LessFunctor_bool
{
    bool operator()(bool l, bool r) const { return (!l) & r; }
};
struct DisplayFunctor_bool
{
    std::string operator()(bool b) const { return b ? "true" : "false"; }
};

//A big integer class for supporting Bosque -- right now it does not do much
class BSQBigInt : public BSQRef
{
public:
    BSQBigInt(int64_t value) : BSQRef(MIRNominalTypeEnum_Int) { ; }
    BSQBigInt(const char* bigstr) : BSQRef(MIRNominalTypeEnum_Int) { ; }

    ~BSQBigInt()
    {
        ;
    }

    virtual void destroy() 
    { 
        ; 
    }

    size_t hash() const
    {
        return 0;
    }

    std::string display() const
    {
        return "[NOT IMPLEMENTED]";
    }

    static BSQBigInt* negate(BSQRefScope& scope, const BSQBigInt* v)
    {
        return nullptr;
    }

    bool eqI64(int64_t v) const
    {
        return false;
    }

    bool ltI64(int64_t v) const
    {
        return false;
    }

    static bool eq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool lt(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static BSQBigInt* add(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* sub(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mult(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* div(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mod(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }
};
struct EqualFunctor_IntValue
{
    bool operator()(IntValue l, IntValue r) const 
    { 
        if(BSQ_IS_VALUE_TAGGED_INT(l) && BSQ_IS_VALUE_TAGGED_INT(r)) {
            return l == r; //tagging does not affect equality
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(l)) {
            return BSQ_GET_VALUE_PTR(r, BSQBigInt)->eqI64(BSQ_GET_VALUE_TAGGED_INT(l));
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(r)) {
            return BSQ_GET_VALUE_PTR(l, BSQBigInt)->eqI64(BSQ_GET_VALUE_TAGGED_INT(r));
        }
        else {
            return BSQBigInt::eq(BSQ_GET_VALUE_PTR(l, BSQBigInt), BSQ_GET_VALUE_PTR(r, BSQBigInt));
        }
    }
};
struct LessFunctor_IntValue
{
    bool operator()(IntValue l, IntValue r) const 
    { 
        if(BSQ_IS_VALUE_TAGGED_INT(l) && BSQ_IS_VALUE_TAGGED_INT(r)) {
            return BSQ_GET_VALUE_TAGGED_INT(l) < BSQ_GET_VALUE_TAGGED_INT(r);
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(l)) {
            return BSQ_GET_VALUE_PTR(r, BSQBigInt)->ltI64(BSQ_GET_VALUE_TAGGED_INT(l));
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(r)) {
            return BSQ_GET_VALUE_PTR(l, BSQBigInt)->ltI64(BSQ_GET_VALUE_TAGGED_INT(r));
        }
        else {
            return BSQBigInt::lt(BSQ_GET_VALUE_PTR(l, BSQBigInt), BSQ_GET_VALUE_PTR(r, BSQBigInt));
        }
    }
};
struct DisplayFunctor_IntValue
{
    std::u32string operator()(IntValue i) const
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return BSQ_IS_VALUE_TAGGED_INT(i) ? conv.from_bytes(std::to_string(BSQ_GET_VALUE_TAGGED_INT(i))) : BSQ_GET_VALUE_PTR(i, BSQBigInt)->display();
    }
};

IntValue op_intNegate(BSQRefScope& scope, IntValue v);

IntValue op_intAdd(BSQRefScope& scope, IntValue v1, IntValue v2);
IntValue op_intSub(BSQRefScope& scope, IntValue v1, IntValue v2);
IntValue op_intMult(BSQRefScope& scope, IntValue v1, IntValue v2);
IntValue op_intDiv(BSQRefScope& scope, IntValue v1, IntValue v2);
IntValue op_intMod(BSQRefScope& scope, IntValue v1, IntValue v2);

size_t bsqKeyValueHash(KeyValue v);
bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);
bool bsqKeyValueLess(KeyValue v1, KeyValue v2);

MIRNominalTypeEnum getNominalTypeOf_KeyValue(KeyValue v);
MIRNominalTypeEnum getNominalTypeOf_Value(Value v);

DATA_KIND_FLAG getDataKindFlag(Value v);

std::u32string diagnostic_format(Value v);

struct HashFunctor_KeyValue
{
    size_t operator()(const KeyValue& k) const { return bsqKeyValueHash(k); }
};
struct EqualFunctor_KeyValue
{
    bool operator()(const KeyValue& l, const KeyValue& r) const { return bsqKeyValueEqual(l, r); }
};
struct LessFunctor_KeyValue
{
    bool operator()(const KeyValue& l, const KeyValue& r) const { return bsqKeyValueLess(l, r); }
};
struct DisplayFunctor_KeyValue
{
    std::u32string operator()(const KeyValue& k) const { return diagnostic_format(k); }
};

enum class BSQBufferFormat {
    Bosque,
    JSON,
    Binary
};

enum class BSQBufferEncoding {
    UTF8,
    URI,
    Base64
};

enum class BSQBufferCompression {
    None,
    RLE,
    Time,
    Space
};

class BSQBuffer : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;
    const BSQBufferCompression compression;

    const std::vector<uint8_t> sdata;

    BSQBuffer(BSQBufferFormat format, BSQBufferEncoding encoding, BSQBufferCompression compression, std::vector<uint8_t>&& sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), compression(compression), sdata(move(sdata)) { ; }
    
    virtual ~BSQBuffer() = default;
    virtual void destroy() { ; }
};

class BSQISOTime : public BSQRef
{
public:
    const uint64_t isotime;

    BSQISOTime(uint64_t isotime) : BSQRef(MIRNominalTypeEnum_ISOTime), isotime(isotime) { ; }
    virtual ~BSQISOTime() = default;
    virtual void destroy() { ; }
};

class BSQRegex : public BSQRef
{
public:
    const std::u32string re;

    BSQRegex(const std::u32string& re) : BSQRef(MIRNominalTypeEnum_Regex), re(re) { ; }
    virtual ~BSQRegex() = default;
};

class BSQTuple : public BSQRef
{
public:
    const std::vector<Value> entries;
    const DATA_KIND_FLAG flag;

    BSQTuple(std::vector<Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Tuple), entries(move(entries)), flag(flag) { ; }

    template <uint16_t n>
    static BSQTuple* createFromSingle(BSQRefScope& scope, DATA_KIND_FLAG flag, const Value(&values)[n])
    {
        Value val;
        std::vector<Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val);
            entries.push_back(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < entries.size(); ++i)
            {
                flag &= getDataKindFlag(entries[i]);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQTuple, move(entries), flag);
    }

    static BSQTuple* createFromSingleDynamic(BSQRefScope& scope, DATA_KIND_FLAG flag, const std::vector<Value>& values)
    {
        Value val;
        std::vector<Value> entries;

        for (int i = 0; i < values.size(); i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val);
            entries.push_back(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < entries.size(); ++i)
            {
                flag &= getDataKindFlag(entries[i]);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQTuple, move(entries), flag);
    }

    virtual ~BSQTuple() = default;

    virtual void destroy()
    {
        for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
        {
            BSQRef::decrementChecked(*iter);
        }
    }

    static BSQTuple* _empty;

    inline bool hasIndex(uint16_t idx) const
    {
        return idx < this->entries.size();
    }

    inline Value atFixed(uint16_t idx) const
    {
        return (idx < this->entries.size()) ? this->entries[idx] : BSQ_VALUE_NONE;
    }

    static void _push(std::vector<Value>& entries, Value v)
    {
        BSQRef::incrementChecked(v);
        entries.push_back(v);
    }
};

class BSQRecord : public BSQRef
{
public:
    const std::map<MIRPropertyEnum, Value> entries;
    const DATA_KIND_FLAG flag;

    BSQRecord(std::map<MIRPropertyEnum, Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Record), entries(move(entries)), flag(flag) { ; }

    template <uint16_t n>
    static BSQRecord* createFromSingle(BSQRefScope& scope, DATA_KIND_FLAG flag, const std::pair<MIRPropertyEnum, Value>(&values)[n])
    {
        std::pair<MIRPropertyEnum, Value> val;
        std::map<MIRPropertyEnum, Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val.second);
            entries.insert(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
            {
                flag &= getDataKindFlag(iter->second);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQRecord, move(entries), flag);
    }

    template <uint16_t n>
    static BSQRecord* createFromUpdate(BSQRefScope& scope, BSQRecord* src, DATA_KIND_FLAG flag, const std::pair<MIRPropertyEnum, Value>(&values)[n])
    {
        std::pair<MIRPropertyEnum, Value> val;
        std::map<MIRPropertyEnum, Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val.second);
            entries.insert(val);
        }

        for(auto iter = src->entries.begin(); iter != src->entries.end(); ++iter) {
            auto pos = entries.lower_bound(iter->first);
            if(pos != src->entries.cend() && pos->first != iter->first)
            {
                BSQRef::incrementChecked(iter->second);
                entries.emplace_hint(pos, *iter);
            }
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
            {
                flag &= getDataKindFlag(iter->second);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQRecord, move(entries), flag);
    }

    virtual ~BSQRecord() = default;

    virtual void destroy()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::decrementChecked(iter->second);
        }
    }

    static BSQRecord* _empty;

    inline bool hasProperty(MIRPropertyEnum p) const
    {
        return this->entries.find(p) != this->entries.end();
    }

    inline Value atFixed(MIRPropertyEnum p) const
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

class BSQObject : public BSQRef
{
public:
    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(ntype) { ; }
    virtual ~BSQObject() = default;

    virtual std::u32string display() const = 0;

    template<int32_t k>
    inline static bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
    {
        if(k < 16)
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
} // namespace BSQ
