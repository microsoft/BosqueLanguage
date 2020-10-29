//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "bsqmetadata.h"
#include "bsqmemory.h"

#include <set>
#include <map>

////
//Value ops

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

#define MIN_BSQ_INT -9007199254740991
#define MAX_BSQ_INT 9007199254740991

#define INT_OOF_BOUNDS(X) (((X) < MIN_BSQ_INT) | ((X) > MAX_BSQ_INT))

#define BSQ_IS_VALUE_TAGGED(V) ((((uintptr_t)(V)) & 0x7) != 0x0)
#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_TAGGED_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)

#define BSQ_GET_VALUE_BOOL(V) ((BSQBool)(((uintptr_t)(V)) & 0x1))
#define BSQ_GET_VALUE_TAGGED_INT(V) (int64_t)(((int64_t)(V)) >> 0x3)

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_TAGGED_INT(I) ((void*)((((uint64_t) I) << 0x3) | 0x4))

#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(BSQTRUE)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(BSQFALSE)

typedef uint64_t None;
typedef void* NoneValue;

#define BSQ_NONE 0
#define BSQ_NONE_VALUE nullptr

#define META_DATA_DECLARE_SPECIAL_BUFFER(NAME, TYPE, DSTR) META_DATA_DECLARE_PTR_PACKED(NAME, TYPE, DATA_KIND_CLEAR_FLAG, sizeof(BSQBuffer), 1, coerceUnionToBox_RefValue, DisplayFunctor_BSQByteBuffer::display, DSTR)

////
//Type ops

namespace BSQ
{

enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

enum class MIRRecordPropertySetsEnum
{
    ps__ = 0,
//%%RECORD_PROPERTY_SETS_ENUM_DECLARE%%
};

constexpr const wchar_t* propertyNames[] = {
    L"Invalid",
//%%PROPERTY_NAMES%%
};

typedef void* KeyValue;
typedef void* Value;

template <uint16_t k>
struct UnionValue
{
    MetaData* umeta;
    uint8_t udata[k];

    template <uint16_t j>
    inline static void convert(const UnionValue& from, UnionValue& into)
    {
        into.umeta = from.umeta;
        GC_MEM_COPY(into.udata, from.udata, std::min(k, j));
    }

    template <uint16_t j>
    inline static UnionValue& convertDirect(const UnionValue& from)
    {
        static_assert(j < k);

        return *(reinterpret_cast<UnionValue<j>*>(&from));
    }

    inline static void convertToUnionNone(MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
    }

    template <typename T>
    inline static void convertToUnionPrimitive(T from, MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
        *((T*)into.udata) = from;
    }

    template <typename T>
    inline static void convertToUnionPointer(T* from, MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
        *((T**)into.udata) = from;
    }

    template <typename T>
    inline static void convertToUnionStruct(const T& from, MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
        GC_MEM_COPY(into.udata, (uint8_t*)(&from), mdata->datasize);
    }

    template <typename T>
    inline static void convertToUnionTuple(const T& from, MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
        GC_MEM_COPY(into.udata, (uint8_t*)(&from), mdata->computeMemorySize(mdata, &from));
    }

    template <typename T>
    inline static void convertToUnionRecord(const T& from, MetaData* mdata, UnionValue& into)
    {
        into.umeta = mdata;
        GC_MEM_COPY(into.udata, (uint8_t*)(&from), mdata->computeMemorySize(mdata, &from));
    }

    template <typename T>
    inline static T extractFromUnionPrimitive(const UnionValue& from)
    {
        return *((T*)into.udata);
    }

    template <typename T>
    inline static T* extractFromUnionPointer(const UnionValue& from)
    {
        return *((T**)into.udata);
    }

    template <typename T>
    inline static void extractFromUnionStruct(const UnionValue& from, T& into)
    {
        GC_MEM_COPY(&into, from.udata, from.mdata->datasize);
    }

    template <typename T>
    inline static void extractFromUnionTuple(const UnionValue& from, T& into)
    {
        GC_MEM_COPY(&into, from.udata, from.umeta->computeMemorySize(from.umeta, from.udata));
    }

    template <typename T>
    inline static void extractFromUnionRecord(const UnionValue& from, T& into)
    {
        GC_MEM_COPY(&into, from.udata, from.umeta->computeMemorySize(from.umeta, from.udata));
    }

    template <typename T>
    inline static T& extractFromUnionDirect(const UnionValue& from)
    {
        return *(reinterpret_cast<T*>(from.udata));
    }

    template <typename T>
    inline static T* extractPointerToContent(const UnionValue& from)
    {
        return (T*)from.udata;
    }
};

struct ConstStorage
{
    static None nhome;
    static NoneValue nvhome;
};

struct EqualFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return true; }
    static bool eq(KeyValue v1, KeyValue v2) { return true; }
};
struct LessFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return false; }
    static bool less(KeyValue v1, KeyValue v2) { return false; }
};
struct DisplayFunctor_NoneValue
{
    std::wstring operator()(NoneValue n) const { return L"none"; }
    static std::wstring display(void* v) { return L"none"; }
};
std::wstring DisplayFunction_NoneValue(void* Uv);
constexpr MetaData MetaData_None = {
    MIRNominalTypeEnum_None,
    DATA_KIND_ALL_FLAG,
    0,
    -1,
    -1,
    0,
    nullptr,
    nullptr,
    LessFunctor_NoneValue::less,
    EqualFunctor_NoneValue::eq,
    coerceUnionToBox_RefValue,
    nullptr,
    nullptr,
    nullptr,
    nullptr,
    DisplayFunctor_NoneValue::display,
    false
};

struct EqualFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return l == r; }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(l), BSQ_GET_VALUE_BOOL(r)); }
};
struct LessFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return (!l) & r; }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(l), BSQ_GET_VALUE_BOOL(r)); }
};
struct DisplayFunctor_BSQBool
{
    std::wstring operator()(BSQBool b) const { return b ? L"true" : L"false"; }
    static std::wstring display(void* v) { return DisplayFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(v)); }
};
META_DATA_DECLARE_NO_PTR_KEY(MetaData_Bool, MIRNominalTypeEnum_Bool, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQBool)), LessFunctor_BSQBool::less, EqualFunctor_BSQBool::eq, coerceUnionToBox_BSQBool, DisplayFunctor_BSQBool::display, L"Bool");

struct EqualFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l == r; }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(l), BSQ_GET_VALUE_TAGGED_INT(r)); }
};
struct LessFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l < r; }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(l), BSQ_GET_VALUE_TAGGED_INT(r)); }
};
struct DisplayFunctor_int64_t
{
    std::wstring operator()(int64_t i) const { return std::to_wstring(i); }
    static std::wstring display(void* v) { return DisplayFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v)); }
};
META_DATA_DECLARE_NO_PTR_KEY(MetaData_Int, MIRNominalTypeEnum_Int, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(int64_t)), LessFunctor_int64_t::less, EqualFunctor_int64_t::eq, coerceUnionToBox_int64_t, DisplayFunctor_int64_t::display, L"Int");

struct DisplayFunctor_double
{
    std::wstring operator()(double d) const { return std::to_wstring(d); }
    static std::wstring display(void* v) { return DisplayFunctor_double{}(*((double*)v)); }
};
META_DATA_DECLARE_NO_PTR(MetaData_Float64, MIRNominalTypeEnum_Float64, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(double)), coerceUnionToBox_double, DisplayFunctor_double::display, L"Float64");

MetaData* getMetaData(void* v);

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);
bool bsqKeyValueLess(KeyValue v1, KeyValue v2);

DATA_KIND_FLAG getDataKindFlag(Value v);

std::wstring diagnostic_format(void* v);

struct DisplayFunctor_BSQRef
{
    std::wstring operator()(void* v) const { return diagnostic_format(v); }
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
    std::wstring operator()(KeyValue k) const { return diagnostic_format(k); }
};

struct DisplayFunctor_Value
{
    std::wstring operator()(Value v) const { return diagnostic_format(v); }
};

enum class BSQBufferFormat {
    Text,
    Bosque,
    Json
};

enum class BSQBufferEncoding {
    UTF8,
    Binary
};

enum class BSQBufferCompression {
    Off,
    Time,
    Space
};

struct BSQByteBuffer
{
    size_t count;
    BSQBufferCompression compression;

    std::wstring display_contents() const
    {
        std::wstring rvals(L"");
        uint8_t* sdata = GET_COLLECTION_START_FIXED(this, sizeof(BSQByteBuffer));
        if(this->compression == BSQBufferCompression::Off)
        {
            rvals += std::wstring(sdata, sdata + this->count);
        }
        else
        {
            for (size_t i = 0; i < this->count; ++i)
            {
                if(i != 0)
                {
                    rvals += L", ";
                }

                rvals += sdata[i];
            }
        }
        return rvals;
    }
};
struct DisplayFunctor_BSQByteBuffer
{
    std::wstring operator()(const BSQByteBuffer* bb) const
    {
        std::wstring rvals(L"ByteBuffer{");
        rvals += bb->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQByteBuffer{}((BSQByteBuffer*)v);
    }
};
META_DATA_DECLARE_NO_PTR_COLLECTION(MetaData_ByteBuffer, MIRNominalTypeEnum_ByteBuffer, DATA_KIND_CLEAR_FLAG, sizeof(BSQByteBuffer), sizeof(uint8_t), coerceUnionToBox_RefValue, DisplayFunctor_BSQByteBuffer::display, L"ByteBuffer");

struct BSQBuffer
{
    BSQByteBuffer* sdata;
    
    BSQBufferFormat format;
    BSQBufferEncoding encoding;
};
struct DisplayFunctor_BSQBuffer
{
    std::wstring operator()(const BSQBuffer* buff) const 
    {
        std::wstring rvals(GET_TYPE_META_DATA(buff)->displayname);
        rvals += L"{";
        rvals += buff->sdata->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQBuffer{}((BSQBuffer*)v);
    }
};
//Declare metadata for each instantiation

struct BSQBufferOf
{
    BSQByteBuffer* sdata;

    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;
};
struct DisplayFunctor_BSQBufferOf
{
    std::wstring operator()(const BSQBufferOf* buff) const 
    {
        std::wstring rvals(GET_TYPE_META_DATA(buff)->displayname);
        rvals += L"{";
        rvals += buff->sdata->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQBufferOf{}((BSQBufferOf*)v);
    }
};
//Declare metadata for each instantiation

struct BSQISOTime
{
    uint64_t isotime;
};
struct DisplayFunctor_BSQISOTime
{
    std::wstring operator()(const BSQISOTime& t) const { return std::wstring{L"ISOTime={"} + std::to_wstring(t.isotime) + L"}";}
    static std::wstring display(void* v) { return DisplayFunctor_BSQISOTime{}(*((BSQISOTime*)v)); }
};
META_DATA_DECLARE_NO_PTR(MetaData_ISOTime, MIRNominalTypeEnum_ISOTime, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQISOTime)), coerceUnionToBox_BSQISOTime, DisplayFunctor_BSQISOTime::display, L"ISOTime");

struct BSQRegex
{
    const std::wregex* re; //these are all constant to this is a scalar as far as GC is concerned
};
struct DisplayFunctor_BSQRegex
{
    std::wstring operator()(const BSQRegex& r) const { return L"[REGEX]"; }
    static std::wstring display(void* v) { return DisplayFunctor_BSQRegex{}(*((BSQRegex*)v)); }
};
META_DATA_DECLARE_NO_PTR(MetaData_Regex, MIRNominalTypeEnum_Regex, DATA_KIND_CLEAR_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQRegex)), coerceUnionToBox_BSQRegex, DisplayFunctor_BSQRegex::display, L"Regex");

template <uint16_t k>
struct BSQTuple
{
    size_t count;
    DATA_KIND_FLAG flag;
    std::array<Value, k> entries;

    template <uint16_t j>
    inline static void convert(const BSQTuple<k>& from, BSQTuple<j>& into) {
        into.count = from.count;
        into.flag = from.flag;

        std::copy(from.entries.begin(), from.entries.begin() + std::min(j, k), into.entries.begin());
    }

    template <uint16_t j>
    inline static BSQTuple<j>& convertDirect(BSQTuple<k>& from) {
        static_assert(j < k);

        return *(reinterpret_cast<BSQTuple<j>*>(&from));
    }

    inline static void boxTuple(MetaData* mdata, BSQTuple& from, Value& into) {
       into = Allocator::GlobalAllocator.allocateSafeStruct<BSQTuple>(mdata, &from);
    }

    inline static Value boxTupleDirect(MetaData* mdata, BSQTuple& from) {
       return Allocator::GlobalAllocator.allocateSafeStruct<BSQTuple>(mdata, &from);
    }

    inline static void unboxTuple(Value from, BSQTuple& into) {
        GC_MEM_COPY(&into, from, GET_TYPE_META_DATA(from)->computeMemorySize(GET_TYPE_META_DATA(from), from));
    }

    template <DATA_KIND_FLAG flag>
    inline static void createFromSingle(BSQTuple& into, std::initializer_list<Value> values)
    {
        into->count = k;
        into->flag = flag;
        into.entries = values;
    }

    template <>
    inline static void createFromSingle<DATA_KIND_UNKNOWN_FLAG>(BSQTuple& into, std::initializer_list<Value> values)
    {
        auto fv = flag;
        for(size_t i = 0; i < k; ++i)
        {
            fv &= getDataKindFlag(values[i]);
        }

        into->count = k;
        into->flag = flag;
        into.entries = values;
    }

    template <uint16_t idx>
    inline bool hasIndex() const
    {
        return idx < this->count;
    }

    template <uint16_t idx>
    inline Value& atFixed()
    {
        if (idx < this->count)
        {
            return this->entries[idx];
        }
        else
        {
            return ConstStorage::nvhome;
        }
    }
};
struct DisplayFunctor_BSQTuple
{
    std::wstring operator()(const BSQTuple& tt) const 
    {
        Value* values = (Value*)GET_COLLECTION_START_FIXED(&tt, sizeof(BSQTuple));
        std::wstring tvals(L"[");
        for(size_t i = 0; i < tt.count; ++i)
        {
            if(i != 0)
            {
                tvals += L", ";
            }

            tvals += diagnostic_format(values[i]);
        }
        tvals += L"]";

        return tvals;
    }
    static std::wstring display(void* v) 
    { 
        return DisplayFunctor_BSQTuple{}(*((BSQTuple*)v)); 
    }
};
META_DATA_DECLARE_PTR_PACKED_COLLECTON_DIRECT(MetaData_Tuple, MIRNominalTypeEnum_Tuple, DATA_KIND_UNKNOWN_FLAG, sizeof(BSQTuple), coerceUnionToBox_BSQTuple, DisplayFunctor_BSQTuple::display, L"Tuple");

struct BSQDynamicTuple
{
    size_t count;
    DATA_KIND_FLAG flag;

    template <uint16_t idx>
    inline bool hasIndex() const
    {
        return idx < this->count;
    }

    template <uint16_t idx>
    inline Value& atFixed()
    {
        if (idx < this->count)
        {
            return *(GET_COLLECTION_START_FIXED(this, sizeof(BSQDynamicTuple)) + idx);
        }
        else
        {
            return ConstStorage::nvhome;
        }
    }
};

class BSQDynamicPropertySetEntry
{
public:
    std::vector<MIRPropertyEnum> propertySet;
    std::map<MIRPropertyEnum, BSQDynamicPropertySetEntry*> extensions;

    BSQDynamicPropertySetEntry() : propertySet(), extensions() 
    { 
        ; 
    }

    BSQDynamicPropertySetEntry(std::vector<MIRPropertyEnum>&& properties) : propertySet(move(properties)), extensions() 
    { 
        ; 
    }

    ~BSQDynamicPropertySetEntry()
    {
        for(auto iter = this->extensions.begin(); iter != this->extensions.end(); iter++)
        {
            delete iter->second;
        }
    }
};

struct BSQPropertySet
{
    static std::map<MIRRecordPropertySetsEnum, std::vector<MIRPropertyEnum>> knownRecordPropertySets;
    static BSQDynamicPropertySetEntry emptyDynamicPropertySetEntry;

    static BSQDynamicPropertySetEntry* getExtendedProperties(BSQDynamicPropertySetEntry* curr, MIRPropertyEnum ext);
};

template <uint16_t k>
struct BSQRecord
{
    size_t count;
    MIRPropertyEnum* properties;
    DATA_KIND_FLAG flag;
    std::array<Value, k> entries; 

    template <uint16_t j>
    inline static void convert(const BSQRecord<k>& from, BSQRecord<j>& into) {
        into.count = from.count;
        into.properties = from.properties;
        into.flag = from.flag;

        xxx;
        std::copy(from.entries, from.entries + std::min(j, k), into.entries);
    }

    template <uint16_t j>
    inline static BSQRecord<j>& convertDirect(BSQRecord<k>& from) {
        static_assert(j < k);

        return *(reinterpret_cast<BSQRecord<j>*>(&from));
    }

    inline static void boxRecord(MetaData* mdata, BSQRecord& from, Value& into) {
        into = Allocator::GlobalAllocator.allocateSafeStruct<BSQRecord>(mdata, &from);
    }

    inline static Value boxRecordDirect(MetaData* mdata, BSQRecord& from) {
       return Allocator::GlobalAllocator.allocateSafeStruct<BSQRecord>(mdata, &from);
    }

    inline static void unboxRecord(Value from, BSQRecord& into) {
        GC_MEM_COPY(&into, from, GET_TYPE_META_DATA(from)->computeMemorySize(GET_TYPE_META_DATA(from), from));
    }

    template <DATA_KIND_FLAG flag>
    inline static BSQRecord createFromSingle(BSQRecord& into, MIRPropertyEnum* properties, std::initializer_list<Value> values)
    {
        into->count = k;
        into->properties = properties;
        into->flag = flag;

        Value* tcurr = (Value*)GET_COLLECTION_START_FIXED(into, sizeof(BSQRecord));
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <>
    inline static void createFromSingle<DATA_KIND_UNKNOWN_FLAG>(BSQRecord& into, MIRPropertyEnum* properties, std::initializer_list<Value> values)
    {
        auto fv = flag;
        for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
        {
            fv &= getDataKindFlag(iter->second);
        }

        into->count = k;
        into->properties = properties;
        into->flag = fv;

        Value* tcurr = (Value*)GET_COLLECTION_START_FIXED(into, sizeof(BSQRecord));
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <DATA_KIND_FLAG flag, uint16_t j>
    static void createFromUpdate(BSQRecord& into, const BSQRecord<j>& src, std::initializer_list<std::pair<MIRPropertyEnum, Value>> nvals)
    {
        size_t valuespos = 0;

        BSQDynamicPropertySetEntry* pse = &BSQPropertySet::emptyDynamicPropertySetEntry
        auto fv = flag;

        auto srcpos = 0;
        auto nvalspos = nvals.begin();
        auto nvalend = nvals.end();

        while(srcpos != src.count || nvalspos != nvalend)
        {
            if(srcpos == src.count || nvalspos->first < src.properties[srcpos])
            {
                into.entries[valuespos] = nvalspos->second;
                pse = BSQPropertySet::getExtendedProperties(pse, nvalspos->first);

                nvalspos++;
            }
            else if(nvalspos == nvalend || src.properties[srcpos] < nvalspos->first)
            {
                into.entries[valuespos] = srcdata[srcpos];
                pse = BSQPropertySet::getExtendedProperties(pse, src.properties[srcpos]);

                srcpos++;
            }
            else
            {
                into.entries[valuespos] = nvalspos->second;
                pse = BSQPropertySet::getExtendedProperties(pse, nvalspos->first);

                nvalspos++;
                srcpos++;
            }

            if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
            {
                fv &= getDataKindFlag(into.entries[valuespos]);
            }
            valuespos++;
        }

        into->count = valuespos;
        into->properties = pse->propertySet.data();
        into->flag = fv;
    }

    template <DATA_KIND_FLAG flag, uint16_t i, uint16_t j>
    static void createFromMerge(BSQRecord& into, const BSQRecord<i>& arg, const BSQRecord<j>& mrg)
    {
        size_t valuespos = 0;

        BSQDynamicPropertySetEntry* pse = &BSQPropertySet::emptyDynamicPropertySetEntry
        auto fv = flag;

        auto argpos = 0;
        auto mrgpos = 0;

        while(argpos != arg.count || mrgpos != mrg.count)
        {
            if(argpos == arg.count || mrg.properties[mrgpos] < src.properties[srcpos])
            {
                into.entries[valuespos] = mrg.entries[mrgpos];
                pse = BSQPropertySet::getExtendedProperties(pse, mrg.properties[mrgpos]);

                mrgpos++;
            }
            else if(mrgpos == mrg.count || arg.properties[argpos] < mrg.properties[mrgpos])
            {
                into.entries[valuespos] = arg.entries[argpos];
                pse = BSQPropertySet::getExtendedProperties(pse, arg.properties[argpos]);

                argpos++;
            }
            else
            {
                into.entries[valuespos] = mrg.entries[mrgpos];
                pse = BSQPropertySet::getExtendedProperties(pse, mrg.properties[mrgpos]);

                mrgpos++;
                argpos++;
            }

            if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
            {
                fv &= getDataKindFlag(into.entries[valuespos]);
            }
            valuespos++;
        }

        into->count = valuespos;
        into->properties = pse->propertySet.data();
        into->flag = fv;
    }

    template <MIRPropertyEnum p>
    inline bool hasProperty() const
    {
        return std::find(this->properties, this->properties + this->count, p) != this->properties + this->count;
    }

    template <MIRPropertyEnum p>
    inline Value atFixed() const
    {
        auto iter = std::find(this->properties, this->properties + this->count, p);
        return iter != this->properties + this->count ? *(this->entries + std::distance(this->properties, iter)) : return ConstStorage::nvhome;
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

        for(size_t i = 0; i < this->count; ++i) 
        {
            if(props.find(this->properties[i]) == props.cend()) 
            {
                return false;
            }
        }

        return true;
    }
};
struct DisplayFunctor_BSQRecord
{
    std::wstring operator()(const BSQRecord& rr) const 
    { 
        Value* values = (Value*)GET_COLLECTION_START_FIXED(&rr, sizeof(BSQRecord));

        std::wstring rvals(L"{");
        for(size_t i = 0; i < rr.count; ++i)
        {
            if(i != 0)
            {
                rvals += L", ";
            }

            rvals += std::wstring{propertyNames[(size_t)rr.properties[i]]} + L"=" + diagnostic_format(values[i]);
        }
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v) 
    { 
        return DisplayFunctor_BSQRecord{}(*((BSQRecord*)v)); 
    }
};
META_DATA_DECLARE_PTR_PACKED_COLLECTON_DIRECT(MetaData_Record, MIRNominalTypeEnum_Record, DATA_KIND_UNKNOWN_FLAG, sizeof(BSQRecord), coerceUnionToBox_BSQRecord, DisplayFunctor_BSQRecord::display, L"Record");

struct BSQDynamicRecord
{
    size_t count;
    MIRPropertyEnum* properties;
    DATA_KIND_FLAG flag;
    Value* entries;

    template <MIRPropertyEnum p>
    inline bool hasProperty() const
    {
        return std::find(&(this->properties), &(this->properties) + this->count, p) != &(this->properties) + this->count;
    }

    template <MIRPropertyEnum p>
    inline Value& atFixed() const
    {
        auto iter = std::find(&(this->properties), &(this->properties) + this->count, p);
        return iter != &(this->properties) + this->count ? *(&(this->entries) + std::distance(&this->properties, iter)) : BSQ_VALUE_NONE;
    }
};

struct EqualFunctor_Union
{
    inline bool operator()(UnionValue& l, UnionValue& r) const 
    { 
        if(l.umeta->nominaltype != r.umeta->nominaltype)
        {
            return false;
        }
        else
        {
            return l.umeta->eq(l.udata, r.udata);
        }
    }
};
struct LessFunctor_Union
{
    inline bool operator()(UnionValue& l, UnionValue& r) const 
    {
        if(l.umeta->nominaltype != r.umeta->nominaltype)
        {
            return l.umeta->nominaltype < r.umeta->nominaltype;
        }
        else
        {
            return l.umeta->eq(l.udata, r.udata);
        }
    }
};
struct DisplayFunctor_Union
{
    std::wstring operator()(UnionValue& n) const 
    { 
        return n.umeta->displayFP(n.udata); 
    }
};

template<int32_t k>
inline bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
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
bool checkSubtypeSlow(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
{
    return std::binary_search(&etypes[0], &etypes[k], tt); 
}
} // namespace BSQ
