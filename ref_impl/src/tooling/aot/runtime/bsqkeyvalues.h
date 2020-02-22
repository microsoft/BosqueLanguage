//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

namespace BSQ
{
class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(MIRNominalTypeEnum_String), sdata(str) { ; }
    BSQString(const char* str, int64_t excount) : BSQRef(excount, MIRNominalTypeEnum_String), sdata(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>().from_bytes(str)) { ; }

    virtual ~BSQString() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQString* str)
    {
        return std::hash<std::u32string>{}(str->sdata);
    }
    
    inline static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        return l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQString* l, const BSQString* r)
    {
        return l->sdata < r->sdata;
    }
};
struct HashFunctor_BSQString
{
    size_t operator()(const BSQString* s) const { return BSQString::hash(s); }
};
struct EqualFunctor_BSQString
{
    bool operator()(const BSQString* l, const BSQString* r) const { return BSQString::keyEqual(l, r); }
};
struct LessFunctor_BSQString
{
    bool operator()(const BSQString* l, const BSQString* r) const { return BSQString::keyLess(l, r); }
};
struct DisplayFunctor_BSQString
{
    std::u32string operator()(const BSQString* s) const { return std::u32string(U"\"") + std::u32string(s->sdata.cbegin(), s->sdata.cend()) + std::u32string(U"\""); }
};

class BSQSafeString : public BSQRef
{
public:
    const std::u32string sdata;
  
    BSQSafeString(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

    virtual ~BSQSafeString() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQSafeString* str)
    {
        return HASH_COMBINE((size_t)str->nominalType, std::hash<std::u32string>{}(str->sdata));
    }

    inline static bool keyEqual(const BSQSafeString* l, const BSQSafeString* r)
    {
        return l->nominalType == r->nominalType && l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQSafeString* l, const BSQSafeString* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : (l->sdata < r->sdata);
    }
};
struct HashFunctor_BSQSafeString
{
    size_t operator()(const BSQSafeString* s) const { return BSQSafeString::hash(s); }
};
struct EqualFunctor_BSQSafeString
{
    bool operator()(const BSQSafeString* l, const BSQSafeString* r) const { return BSQSafeString::keyEqual(l, r); }
};
struct LessFunctor_BSQSafeString
{
    bool operator()(const BSQSafeString* l, const BSQSafeString* r) const { return BSQSafeString::keyLess(l, r); }
};
struct DisplayFunctor_BSQSafeString
{
    std::u32string operator()(const BSQSafeString* s) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)s->nominalType]) + std::u32string(U"'") + s->sdata + std::u32string(U"'"); 
    }
};

class BSQStringOf : public BSQRef
{
public:
    const std::u32string sdata;
  
    BSQStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

    virtual ~BSQStringOf() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQStringOf* str)
    {
        return HASH_COMBINE((size_t)str->nominalType, std::hash<std::u32string>{}(str->sdata));
    }

    inline static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        return l->nominalType == r->nominalType && l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQStringOf* l, const BSQStringOf* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : (l->sdata < r->sdata);
    }
};
struct HashFunctor_BSQStringOf
{
    size_t operator()(const BSQStringOf* s) const { return BSQStringOf::hash(s); }
};
struct EqualFunctor_BSQStringOf
{
    bool operator()(const BSQStringOf* l, const BSQStringOf* r) const { return BSQStringOf::keyEqual(l, r); }
};
struct LessFunctor_BSQStringOf
{
    bool operator()(const BSQStringOf* l, const BSQStringOf* r) const { return BSQStringOf::keyLess(l, r); }
};
struct DisplayFunctor_BSQStringOf
{
    std::u32string operator()(const BSQStringOf* s) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)s->nominalType]) + std::u32string(U"'") + s->sdata + std::u32string(U"'"); 
    }
};

class BSQGUID : public BSQRef
{
public:
    const uint8_t sdata[16];

    BSQGUID(const uint8_t sdata[16]) : BSQRef(MIRNominalTypeEnum_GUID), sdata() { memcpy((void*)this->sdata, sdata, 16); }

    virtual ~BSQGUID() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQGUID* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    inline static bool keyEqual(const BSQGUID* l, const BSQGUID* r)
    {
        return memcmp(l->sdata, r->sdata, 16) == 0;
    }

    inline static bool keyLess(const BSQGUID* l, const BSQGUID* r)
    {
        return memcmp(l->sdata, r->sdata, 16) < 0;
    }
};
struct HashFunctor_BSQGUID
{
    size_t operator()(const BSQGUID* g) const { return BSQGUID::hash(g); }
};
struct EqualFunctor_BSQGUID
{
    bool operator()(const BSQGUID* l, const BSQGUID* r) const { return BSQGUID::keyEqual(l, r); }
};
struct LessFunctor_BSQGUID
{
    bool operator()(const BSQGUID* l, const BSQGUID* r) const { return BSQGUID::keyLess(l, r); }
};
struct DisplayFunctor_BSQGUID
{
    std::u32string operator()(const BSQGUID* g) const { return std::u32string(U"DataHash@") + std::u32string(g->sdata, g->sdata + 16); }
};

class BSQLogicalTime : public BSQRef
{
public:
    uint64_t timestamp;

    BSQLogicalTime() : BSQRef(MIRNominalTypeEnum_LogicalTime) { ; }
    BSQLogicalTime(uint64_t timestamp) : BSQRef(MIRNominalTypeEnum_LogicalTime), timestamp(timestamp) { ; }

    BSQLogicalTime(const BSQLogicalTime& src) : BSQRef(MIRNominalTypeEnum_LogicalTime), timestamp(src.timestamp)
    { 
        ; 
    }

    BSQLogicalTime& operator=(const BSQLogicalTime& src)
    {
        this->timestamp = src.timestamp;
        return *this;
    }

    virtual ~BSQLogicalTime() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQLogicalTime& t)
    {
        return (size_t)t.timestamp;
    }

    inline static bool keyEqual(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp == r.timestamp;
    }

     inline static bool keyLess(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp < r.timestamp;
    }
};
struct HashFunctor_BSQLogicalTime
{
    size_t operator()(const BSQLogicalTime& et) const { return BSQLogicalTime::hash(et); }
};
struct EqualFunctor_BSQLogicalTime
{
    bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyEqual(l, r); }
};
struct LessFunctor_BSQLogicalTime
{
    bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyLess(l, r); }
};
struct DisplayFunctor_BSQLogicalTime
{
    std::u32string operator()(const BSQLogicalTime& et) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return std::u32string(U"LogicalTime@") + conv.from_bytes(std::to_string(et.timestamp)); 
    }
};

class BSQDataHash : public BSQRef
{
public:
    uint64_t hdata;

    BSQDataHash() : BSQRef(MIRNominalTypeEnum_DataHash) { ; }
    BSQDataHash(uint64_t hdata) : BSQRef(MIRNominalTypeEnum_DataHash), hdata(hdata) { ; }

    BSQDataHash(const BSQDataHash& src) : BSQRef(MIRNominalTypeEnum_DataHash), hdata(src.hdata)
    { 
        ; 
    }

    BSQDataHash& operator=(const BSQDataHash& src)
    {
        this->hdata = src.hdata;
        return *this;
    }

    virtual ~BSQDataHash() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQDataHash& h)
    {
        return (size_t)h.hdata;
    }

    inline static bool keyEqual(const BSQDataHash& l, const BSQDataHash& r)
    {
        return l.hdata == r.hdata;
    }

    inline static bool keyLess(const BSQDataHash& l, const BSQDataHash& r)
    {
        return l.hdata < r.hdata;
    }
};
struct HashFunctor_BSQDataHash
{
    size_t operator()(const BSQDataHash& h) const { return BSQDataHash::hash(h); }
};
struct EqualFunctor_BSQDataHash
{
    bool operator()(const BSQDataHash& l, const BSQDataHash& r) const { return BSQDataHash::keyEqual(l, r); }
};
struct LessFunctor_BSQDataHash
{
    bool operator()(const BSQDataHash& l, const BSQDataHash& r) const { return BSQDataHash::keyLess(l, r); }
};
struct DisplayFunctor_BSQDataHash
{
    std::u32string operator()(const BSQDataHash& h) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return std::u32string(U"DataHash@") + conv.from_bytes(std::to_string(h.hdata)); 
    }
};

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t sdata[64]) : BSQRef(MIRNominalTypeEnum_CryptoHash), hdata() { memcpy((void*)this->hdata, hdata, 64); }
    virtual ~BSQCryptoHash() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQCryptoHash* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    inline static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }

    inline static bool keyLess(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) < 0;
    }
};
struct HashFunctor_BSQCryptoHash
{
    size_t operator()(const BSQCryptoHash* h) const { return BSQCryptoHash::hash(h); }
};
struct EqualFunctor_BSQCryptoHash
{
    bool operator()(const BSQCryptoHash* l, const BSQCryptoHash* r) const { return BSQCryptoHash::keyEqual(l, r); }
};
struct LessFunctor_BSQCryptoHash
{
    bool operator()(const BSQCryptoHash* l, const BSQCryptoHash* r) const { return BSQCryptoHash::keyLess(l, r); }
};
struct DisplayFunctor_BSQCryptoHash
{
    std::u32string operator()(const BSQCryptoHash* h) const { return std::u32string(U"CryptoHash@") + std::u32string(h->hdata, h->hdata + 64); }
};

class BSQEnum : public BSQRef
{
public:
    uint32_t value;

    BSQEnum() : BSQRef(MIRNominalTypeEnum::Invalid) { ; }
    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : BSQRef(oftype), value(value) { ; }

    BSQEnum(const BSQEnum& src) : BSQRef(src.nominalType), value(src.value)
    { 
        ; 
    }

    BSQEnum& operator=(const BSQEnum& src)
    {
        this->value = src.value;
        this->nominalType = src.nominalType;
        return *this;
    }

    virtual ~BSQEnum() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQEnum& e)
    {
        return HASH_COMBINE((size_t)e.nominalType, (size_t)e.value);
    }

    inline static bool keyEqual(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType == r.nominalType) & (l.value == r.value);
    }

    inline static bool keyLess(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType != r.nominalType) ? (l.nominalType < r.nominalType) : (l.value < r.value);
    }
};
struct HashFunctor_BSQEnum
{
    size_t operator()(const BSQEnum& e) const { return BSQEnum::hash(e); }
};
struct EqualFunctor_BSQEnum
{
    bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyEqual(l, r); }
};
struct LessFunctor_BSQEnum
{
    bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyLess(l, r); }
};
struct DisplayFunctor_BSQEnum
{
    std::u32string operator()(const BSQEnum& e) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)e.nominalType]) + std::u32string(U"::") + conv.from_bytes(std::to_string(e.value)); 
    }
};

class BSQIdKey : public BSQRef
{
private:
    static size_t hh(MIRNominalTypeEnum oftype, const std::vector<std::pair<MIRPropertyEnum, KeyValue>>& keys)
    {
        size_t hv = (size_t)oftype;
        for(size_t i = 0; i < keys.size(); ++i)
        {
            hv = HASH_COMBINE(hv, HASH_COMBINE((size_t)keys[i].first, bsqKeyValueHash(keys[i].second)));
        }
        return hv;
    }

public:
    const size_t vhash;
    const std::vector<std::pair<MIRPropertyEnum, KeyValue>> keys;

    BSQIdKey(KeyValue key, MIRNominalTypeEnum oftype) : BSQRef(oftype), vhash(HASH_COMBINE((size_t)oftype, bsqKeyValueHash(key))), keys({std::make_pair(MIRPropertyEnum::Invalid, key)}) { ; }
    BSQIdKey(std::vector<std::pair<MIRPropertyEnum, KeyValue>>&& keys, MIRNominalTypeEnum oftype) : BSQRef(oftype), vhash(hh(oftype, keys)), keys(move(keys)) { ; }
    virtual ~BSQIdKey() = default;

    virtual void destroy() 
    {
        for(size_t i = 0; i < this->keys.size(); ++i)
        {
            BSQRef::decrementChecked(this->keys[i].second); 
        }
    }

    inline static size_t hash(const BSQIdKey* k)
    {
       return k->vhash;
    }

    inline static bool keyEqual(const BSQIdKey* l, const BSQIdKey* r)
    {
        if(l->vhash != r->vhash)
        {
            return false;
        }

        if(l->nominalType != r->nominalType || l->keys.size() != r->keys.size())
        {
            return false;
        }
        
        for(size_t i = 0; i < l->keys.size(); ++i)
        {
            if(l->keys[i].first != r->keys[i].first || !bsqKeyValueEqual(l->keys[i].second, r->keys[i].second))
            {
                return false;
            }
        }

        return true;
    }

    inline static bool keyLess(const BSQIdKey* l, const BSQIdKey* r)
    {
        if(l->nominalType != r->nominalType)
        {
            return l->nominalType < r->nominalType;
        }

        if(l->keys.size() != r->keys.size())
        {
            return l->keys.size() < r->keys.size();
        }
        
        for(size_t i = 0; i < l->keys.size(); ++i)
        {
            if(l->keys[i].first != r->keys[i].first)
            {
                return l->keys[i].first < r->keys[i].first;
            }

            if(!bsqKeyValueEqual(l->keys[i].second, r->keys[i].second))
            {
                return bsqKeyValueLess(l->keys[i].second, r->keys[i].second);
            }
        }

        return true;
    }
};
struct HashFunctor_BSQIdKey
{
    size_t operator()(const BSQIdKey* idk) const { return BSQIdKey::hash(idk); }
};
struct EqualFunctor_BSQIdKey
{
    bool operator()(const BSQIdKey* l, const BSQIdKey* r) const { return BSQIdKey::keyEqual(l, r); }
};
struct LessFunctor_BSQIdKey
{
    bool operator()(const BSQIdKey* l, const BSQIdKey* r) const { return BSQIdKey::keyLess(l, r); }
};
struct DisplayFunctor_BSQIdKey
{
    std::u32string operator()(const BSQIdKey* idk) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        std::u32string rvals = conv.from_bytes(nominaltypenames[(uint32_t)idk->nominalType]);
        if(idk->keys.size() == 1) 
        {
            return rvals + U" of " + diagnostic_format(idk->keys[0].second);
        }
        else
        {
            rvals +=  U" of { ";
            for(size_t i = 0; i < idk->keys.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += conv.from_bytes(propertyNames[(int32_t)idk->keys[i].first]) + U"=" + diagnostic_format(idk->keys[i].second);
            }
            rvals += U" }"; 

            return rvals;
        }
    }
};

class BSQGUIDIdKey : public BSQRef
{
public:
    const uint8_t sdata[16];

    BSQGUIDIdKey(const uint8_t sdata[16], MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata() { memcpy((void*)this->sdata, sdata, 16); }

    virtual ~BSQGUIDIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQGUIDIdKey* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    inline static bool keyEqual(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r)
    {
        return l->nominalType == r->nominalType && memcmp(l->sdata, r->sdata, 16) == 0;
    }

    inline static bool keyLess(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : memcmp(l->sdata, r->sdata, 16) < 0;
    }
};
struct HashFunctor_BSQGUIDIdKey
{
    size_t operator()(const BSQGUIDIdKey* idg) const { return BSQGUIDIdKey::hash(idg); }
};
struct EqualFunctor_BSQGUIDIdKey
{
    bool operator()(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r) const { return BSQGUIDIdKey::keyEqual(l, r); }
};
struct LessFunctor_BSQGUIDIdKey
{
    bool operator()(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r) const { return BSQGUIDIdKey::keyLess(l, r); }
};
struct DisplayFunctor_BSQGUIDIdKey
{
    std::u32string operator()(const BSQGUIDIdKey* idg) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)idg->nominalType]) + std::u32string(U"::") + std::u32string(idg->sdata, idg->sdata + 16); 
    }
};

class BSQLogicalTimeIdKey : public BSQRef
{
public:
    uint64_t timestamp;

    BSQLogicalTimeIdKey() : BSQRef(MIRNominalTypeEnum::Invalid) { ; }
    BSQLogicalTimeIdKey(uint64_t timestamp, MIRNominalTypeEnum oftype) : BSQRef(oftype), timestamp(timestamp) { ; }

    BSQLogicalTimeIdKey(const BSQLogicalTimeIdKey& src) : BSQRef(src.nominalType), timestamp(src.timestamp)
    { 
        ; 
    }

    BSQLogicalTimeIdKey& operator=(const BSQLogicalTimeIdKey& src)
    {
        this->timestamp = src.timestamp;
        this->nominalType = src.nominalType;
        return *this;
    }

    virtual ~BSQLogicalTimeIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQLogicalTimeIdKey& tid)
    {
        return HASH_COMBINE((size_t)tid.nominalType, tid.timestamp);
    }

    inline static bool keyEqual(const BSQLogicalTimeIdKey& l, const BSQLogicalTimeIdKey& r)
    {
        return l.nominalType == r.nominalType && l.timestamp == r.timestamp;
    }

    inline static bool keyLess(const BSQLogicalTimeIdKey& l, const BSQLogicalTimeIdKey& r)
    {
        return (l.nominalType != r.nominalType) ? (l.nominalType < r.nominalType) : (l.timestamp < r.timestamp);
    }
};
struct HashFunctor_BSQLogicalTimeIdKey
{
    size_t operator()(const BSQLogicalTimeIdKey& idt) const { return BSQLogicalTimeIdKey::hash(idt); }
};
struct EqualFunctor_BSQLogicalTimeIdKey
{
    bool operator()(const BSQLogicalTimeIdKey& l, const BSQLogicalTimeIdKey& r) const { return BSQLogicalTimeIdKey::keyEqual(l, r); }
};
struct LessFunctor_BSQLogicalTimeIdKey
{
    bool operator()(const BSQLogicalTimeIdKey& l, const BSQLogicalTimeIdKey& r) const { return BSQLogicalTimeIdKey::keyLess(l, r); }
};
struct DisplayFunctor_BSQLogicalTimeIdKey
{
    std::u32string operator()(const BSQLogicalTimeIdKey& idt) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)idt.nominalType]) + std::u32string(U"::") + conv.from_bytes(std::to_string(idt.timestamp)); 
    }
};

class BSQContentHashIdKey : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQContentHashIdKey(const uint8_t hdata[64], MIRNominalTypeEnum oftype) : BSQRef(oftype), hdata() { memcpy((void*)this->hdata, hdata, 64); }

    virtual ~BSQContentHashIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQContentHashIdKey* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    inline static bool keyEqual(const BSQContentHashIdKey* l, const BSQContentHashIdKey* r)
    {
        return l->nominalType == r->nominalType && memcmp(l->hdata, r->hdata, 64) == 0;
    }

    inline static bool keyLess(const BSQContentHashIdKey* l, const BSQContentHashIdKey* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : memcmp(l->hdata, r->hdata, 64) < 0;
    }
};
struct HashFunctor_BSQContentHashIdKey
{
    size_t operator()(const BSQContentHashIdKey* ihc) const { return BSQContentHashIdKey::hash(ihc); }
};
struct EqualFunctor_BSQContentHashIdKey
{
    bool operator()(const BSQContentHashIdKey* l, const BSQContentHashIdKey* r) const { return BSQContentHashIdKey::keyEqual(l, r); }
};
struct LessFunctor_BSQContentHashIdKey
{
    bool operator()(const BSQContentHashIdKey* l, const BSQContentHashIdKey* r) const { return BSQContentHashIdKey::keyLess(l, r); }
};
struct DisplayFunctor_BSQContentHashIdKey
{
    std::u32string operator()(const BSQContentHashIdKey* ihc) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)ihc->nominalType]) + std::u32string(U"::") + std::u32string(ihc->hdata, ihc->hdata + 64); 
    }
};
}
