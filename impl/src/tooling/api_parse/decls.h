
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "bsqregex.h"

class IType;
class UnionType;
class InvokeSignature;
class APIModule;

class InvokeSignature
{
public:
    const std::string name;
    const IType* restype;
    const std::vector<std::string> argnames;
    const std::vector<const IType*> argtypes;
    
    InvokeSignature(std::string name, const IType* restype, std::vector<std::string> argnames, std::vector<const IType*> argtypes): name(name), restype(restype), argnames(argnames), argtypes(argtypes) {;}

    static InvokeSignature* jparse(json j, const std::map<std::string, const IType*>& typemap);
};

class APIModule
{
public:
    const std::map<std::string, const IType*> typemap;
    const std::vector<InvokeSignature*> api;

    //TODO: we are not applying these throughly/uniformly
    const std::map<std::string, std::string> typedefmap;
    const std::map<std::string, std::string> namespacemap;

    static std::set<std::string> s_tzdata;

    APIModule(std::map<std::string, const IType*> typemap, std::vector<InvokeSignature*> api, std::map<std::string, std::string> typedefmap, std::map<std::string, std::string> namespacemap) : typemap(typemap), api(api), typedefmap(typedefmap), namespacemap(namespacemap)
    {
        ;
    }

    ~APIModule();

    std::optional<const InvokeSignature*> getSigForFriendlyName(const std::string& iname) const
    {
        auto ii = std::find_if(this->api.cbegin(), this->api.cend(), [&iname](const InvokeSignature* isig) {
            return isig->name == iname;
        });

        if(ii == this->api.cend())
        {
            return std::nullopt;
        }
        else
        {
            return std::make_optional(*ii);
        }
    }

    std::optional<const IType*> getTypeForFriendlyName(const std::string& iname) const
    {
        //TODO: need to set this up to resolve names per namespace and typedecl mappings
        //      -- ALSO need to update direct references to the typemap->find to use this resolution as well!!!!

        auto ii = this->typemap.find(iname);
        if(ii == this->typemap.cend())
        {
            return std::nullopt;
        }
        else
        {
            return std::make_optional(ii->second);
        }
    }

    std::vector<const IType*> getAllTypesInUnion(const UnionType* tt) const;

    static APIModule* jparse(json j);
};

enum class TypeTag
{
    NoneTag = 0x0,
    NothingTag,
    BoolTag,
    NatTag,
    IntTag,
    BigNatTag,
    BigIntTag,
    RationalTag,
    FloatTag,
    DecimalTag,
    StringTag,
    StringOfTag,
    DataStringTag,
    ByteBufferTag,
    DataBufferTag,
    DateTimeTag,
    UTCDateTimeTag,
    CalendarDateTag,
    TickTimeTag,
    LogicalTimeTag,
    ISOTimeStampTag,
    UUID4Tag,
    UUID7Tag,
    SHAContentHashTag,
    LatLongCoordinateTag,
    ConstructableOfType,
    TupleTag,
    RecordTag,
    ContainerTTag,
    ContainerKVTag,
    EnumTag,
    EntityTag,
    UnionTag
};

struct APIDateTime
{
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
    uint8_t hour;    // 0-23
    uint8_t min;     // 0-59

    const char* tzdata; //timezone name as spec in tzdata database
};

struct APIUTCDateTime
{
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
    uint8_t hour;    // 0-23
    uint8_t min;     // 0-59
};

struct APICalendarDate
{
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
};

struct APIISOTimeStamp
{
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
    uint8_t hour;    // 0-23
    uint8_t min;     // 0-59
    uint8_t sec;     // 0-60
    uint16_t millis; // 0-999
};

template <typename ValueRepr, typename State>
class ApiManagerJSON
{
public:
    ApiManagerJSON() {;}
    virtual ~ApiManagerJSON() {;}

    virtual bool checkInvokeOk(const std::string& checkinvoke, ValueRepr value, State& ctx) = 0;

    virtual bool parseNoneImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual bool parseNothingImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual bool parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, ValueRepr value, State& ctx) = 0;
    virtual bool parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, ValueRepr value, State& ctx) = 0;
    virtual bool parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, ValueRepr value, State& ctx) = 0;
    virtual bool parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, ValueRepr value, State& ctx) = 0;
    virtual bool parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, ValueRepr value, State& ctx) = 0;
    virtual bool parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, ValueRepr value, State& ctx) = 0;
    virtual bool parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, ValueRepr value, State& ctx) = 0;
    virtual bool parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, ValueRepr value, State& ctx) = 0;
    virtual bool parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, ValueRepr value, State& ctx) = 0;
    virtual bool parseByteBufferImpl(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, ValueRepr value, State& ctx) = 0;
    virtual bool parseDateTimeImpl(const APIModule* apimodule, const IType* itype, APIDateTime t, ValueRepr value, State& ctx) = 0;
    virtual bool parseUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, APIUTCDateTime t, ValueRepr value, State& ctx) = 0;
    virtual bool parseCalendarDateImpl(const APIModule* apimodule, const IType* itype, APICalendarDate t, ValueRepr value, State& ctx) = 0;
    virtual bool parseTickTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t t, ValueRepr value, State& ctx) = 0;
    virtual bool parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, ValueRepr value, State& ctx) = 0;
    virtual bool parseISOTimeStampImpl(const APIModule* apimodule, const IType* itype, APIISOTimeStamp t, ValueRepr value, State& ctx) = 0;
    virtual bool parseUUID4Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
    virtual bool parseUUID7Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
    virtual bool parseSHAContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
    virtual bool parseLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, float latitude, float longitude, ValueRepr value, State& ctx) = 0;

    virtual void prepareParseTuple(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
    virtual ValueRepr getValueForTupleIndex(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual void completeParseTuple(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

    virtual void prepareParseRecord(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
    virtual ValueRepr getValueForRecordProperty(const APIModule* apimodule, const IType* itype, ValueRepr value, std::string pname, State& ctx) = 0;
    virtual void completeParseRecord(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

    virtual void prepareParseContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t count, State& ctx) = 0;
    virtual ValueRepr getValueForContainerElementParse_T(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual std::pair<ValueRepr, ValueRepr> getValueForContainerElementParse_KV(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual void completeParseContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

    virtual void prepareParseEntity(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
    virtual void prepareParseEntityMask(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
    virtual ValueRepr getValueForEntityField(const APIModule* apimodule, const IType* itype, ValueRepr value, std::pair<std::string, std::string> fnamefkey, State& ctx) = 0;
    virtual void completeParseEntity(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

    virtual void setMaskFlag(const APIModule* apimodule, ValueRepr flagloc, size_t i, bool flag, State& ctx) = 0;

    virtual ValueRepr parseUnionChoice(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t pick, const IType* picktype, State& ctx) = 0;

    virtual std::optional<bool> extractBoolImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<uint64_t> extractNatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<int64_t> extractIntImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::string> extractBigNatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::string> extractBigIntImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::string> extractFloatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::string> extractDecimalImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::pair<std::string, uint64_t>> extractRationalImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::string> extractStringImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<APIDateTime> extractDateTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<APIUTCDateTime> extractUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<APICalendarDate> extractCalendarDateImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<uint64_t> extractTickTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<uint64_t> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<APIISOTimeStamp> extractISOTimeStampImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::vector<uint8_t>> extractUUID4Impl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::vector<uint8_t>> extractUUID7Impl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::vector<uint8_t>> extractSHAContentHashImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<std::pair<float, float>> extractLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    
    virtual ValueRepr extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual ValueRepr extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, ValueRepr value, std::string pname, State& ctx) = 0;
    virtual ValueRepr extractValueForEntityField(const APIModule* apimodule, const IType* itype, ValueRepr value, std::pair<std::string, std::string> fnamefkey, State& ctx) = 0;

    virtual void prepareExtractContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual std::optional<size_t> extractLengthForContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
    virtual ValueRepr extractValueForContainer_T(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual std::pair<ValueRepr, ValueRepr> extractValueForContainer_KV(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
    virtual void completeExtractContainer(const APIModule* apimodule, const IType* itype, State& ctx) = 0;

    virtual std::optional<size_t> extractUnionChoice(const APIModule* apimodule, const IType* itype, const std::vector<const IType*>& opttypes, ValueRepr intoloc, State& ctx) = 0;
    virtual ValueRepr extractUnionValue(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t uchoice, State& ctx) = 0;
};

class JSONParseHelper
{
public:
    static std::optional<uint64_t> parseToUnsignedNumber(json j);
    static std::optional<int64_t> parseToSignedNumber(json j);
    static std::optional<std::string> parseToBigUnsignedNumber(json j);
    static std::optional<std::string> parseToBigSignedNumber(json j);
    static std::optional<std::string> parseToRealNumber(json j);
    static std::optional<std::string> parseToDecimalNumber(json j);
    static std::optional<std::pair<std::string, uint64_t>> parseToRationalNumber(json j);
    static std::optional<APIDateTime> parseToDateTime(json j);
    static std::optional<APIUTCDateTime> parseToUTCDateTime(json j);
    static std::optional<APICalendarDate> parseToCalendarDate(json j);
    static std::optional<uint64_t> parseToTickTime(json j);
    static std::optional<uint64_t> parseToLogicalTime(json j);
    static std::optional<APIISOTimeStamp> parseToISOTimeStamp(json j);
    static std::optional<std::vector<uint8_t>> parseUUID4(json j);
    static std::optional<std::vector<uint8_t>> parseUUID7(json j);
    static std::optional<std::vector<uint8_t>> parseSHAContentHash(json j);
    static std::optional<std::pair<float, float>> parseLatLongCoordinate(json j);

    static std::optional<json> emitUnsignedNumber(uint64_t n);
    static std::optional<json> emitSignedNumber(int64_t i);
    static std::optional<json> emitBigUnsignedNumber(std::string s);
    static std::optional<json> emitBigSignedNumber(std::string s);
    static std::optional<json> emitRealNumber(std::string s);
    static std::optional<json> emitDecimalNumber(std::string s);
    static std::optional<json> emitRationalNumber(std::pair<std::string, uint64_t> rv);
    static std::optional<json> emitDateTime(APIDateTime t);
    static std::optional<json> emitUTCDateTime(APIUTCDateTime t);
    static std::optional<json> emitCalendarDate(APICalendarDate t);
    static std::optional<json> emitTickTime(uint64_t t);
    static std::optional<json> emitLogicalTime(uint64_t t);
    static std::optional<json> emitISOTimeStamp(APIISOTimeStamp t);
    static std::optional<json> emitUUID4(std::vector<uint8_t> uuid);
    static std::optional<json> emitUUID7(std::vector<uint8_t> uuid);
    static std::optional<json> emitSHAHash(std::vector<uint8_t> hash);
    static std::optional<json> emitLatLongCoordinate(std::pair<float, float> llcoord);

    static std::optional<std::pair<std::string, std::string>> checkEnumName(json j);
};

class IType
{
public:
    const TypeTag tag;
    const std::string name;

    IType(TypeTag tag, std::string name) : tag(tag), name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual bool isUnion() const
    {
        return false;
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const = 0;

    template <typename ValueRepr, typename State>
    bool tparse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const;

    template <typename ValueRepr, typename State>
    std::optional<json> textract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const;
};

class IGroundedType : public IType
{
public:
    IGroundedType(TypeTag tag, std::string name): IType(tag, name) {;}
    virtual ~IGroundedType() {;}
};

class NoneType : public IGroundedType
{
public:
    NoneType() : IGroundedType(TypeTag::NoneTag, "None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j)
    {
        return new NoneType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return "null";
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_null())
        {
            return false;
        }
        
        return apimgr.parseNoneImpl(apimodule, this, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return std::make_optional(nullptr);
    }
};

class NothingType : public IGroundedType
{
public:
    NothingType() : IGroundedType(TypeTag::NothingTag, "Nothing") {;}
    virtual ~NothingType() {;}

    static NothingType* jparse(json j)
    {
        return new NothingType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return "null";
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_null())
        {
            return false;
        }
        
        return apimgr.parseNothingImpl(apimodule, this, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return std::make_optional(nullptr);
    }
};

class BoolType : public IGroundedType
{
public:
    BoolType() : IGroundedType(TypeTag::BoolTag, "Bool") {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j)
    {
        return new BoolType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> bgen(0, 1);
        return bgen(rnd) == 1;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_boolean())
        {
            return false;
        }
        
        return apimgr.parseBoolImpl(apimodule, this, j.get<bool>(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimgr.extractBoolImpl(apimodule, this, value, ctx);
    }
};

class NatType : public IGroundedType
{
public:
    NatType() : IGroundedType(TypeTag::NatTag, "Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j)
    {
        return new NatType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 32);
        return JSONParseHelper::emitUnsignedNumber(ngen(rnd)).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<uint64_t> nval = JSONParseHelper::parseToUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseNatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractNatImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitUnsignedNumber(nval.value());
    }
};

class IntType : public IGroundedType
{
public:
    IntType() : IGroundedType(TypeTag::IntTag, "Int") {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j)
    {
        return new IntType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> igen(-32, 32);
        return JSONParseHelper::emitSignedNumber(igen(rnd)).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<int64_t> nval = JSONParseHelper::parseToSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseIntImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractIntImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitSignedNumber(nval.value());
    }
};

class BigNatType : public IGroundedType
{
public:
    BigNatType() : IGroundedType(TypeTag::BigNatTag, "BigNat") {;}
    virtual ~BigNatType() {;}

    static BigNatType* jparse(json j)
    {
        return new BigNatType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 128);
        return JSONParseHelper::emitBigUnsignedNumber(std::to_string(ngen(rnd))).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToBigUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigNatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractBigNatImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitBigUnsignedNumber(nval.value());
    }
};

class BigIntType : public IGroundedType
{
public:
    BigIntType() : IGroundedType(TypeTag::BigIntTag, "BigInt") {;}
    virtual ~BigIntType() {;}

    static BigIntType* jparse(json j)
    {
        return new BigIntType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> igen(-128, 128);
        return JSONParseHelper::emitBigSignedNumber(std::to_string(igen(rnd))).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToBigSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigIntImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractBigIntImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitBigSignedNumber(nval.value());
    }
};

class RationalType : public IGroundedType
{
public:
    RationalType() : IGroundedType(TypeTag::RationalTag, "Rational") {;}
    virtual ~RationalType() {;}

    static RationalType* jparse(json j)
    {
        return new RationalType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> ngen(-128, 128);
        std::uniform_int_distribution<uint64_t> dgen(1, 32);
        
        return JSONParseHelper::emitRationalNumber(std::make_pair(std::to_string(ngen(rnd)), dgen(rnd))).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<std::pair<std::string, uint64_t>> nval = JSONParseHelper::parseToRationalNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseRationalImpl(apimodule, this, nval.value().first, nval.value().second, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractRationalImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitRationalNumber(nval.value());
    }
};

class FloatType : public IGroundedType
{
public:
    FloatType() : IGroundedType(TypeTag::FloatTag, "Float") {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j)
    {
        return new FloatType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_real_distribution<double> fgen(-128.0, 128.0);
        
        return JSONParseHelper::emitRealNumber(std::to_string(fgen(rnd))).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToRealNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseFloatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractFloatImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitRealNumber(nval.value());
    }
};

class DecimalType : public IGroundedType
{
public:
    DecimalType() : IGroundedType(TypeTag::DecimalTag, "Decimal") {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j)
    {
        return new DecimalType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_real_distribution<float> fgen(-128.0, 128.0);
        
        return JSONParseHelper::emitRealNumber(std::to_string(fgen(rnd))).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToRealNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseDecimalImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractDecimalImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitRealNumber(nval.value());
    }
};

class StringType : public IGroundedType
{
public:
    StringType() : IGroundedType(TypeTag::StringTag, "String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j)
    {
        return new StringType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);
        std::uniform_int_distribution<uint32_t> cgen(32, 126);
        
        auto slen = lgen(rnd);
        std::vector<uint8_t> res;
        res.reserve(slen);

        for(size_t i = 0; i < slen; ++i)
        {
            res.push_back((uint8_t)cgen(rnd));
        }

        return std::string(res.cbegin(), res.cend());
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_string())
        {
            return false;
        }
        
        return apimgr.parseStringImpl(apimodule, this, j.get<std::string>(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimgr.extractStringImpl(apimodule, this, value, ctx);
    }
};

class StringOfType : public IGroundedType
{
public:
    const BSQRegex* validator;

    StringOfType(std::string name, BSQRegex* validator) : IGroundedType(TypeTag::StringOfTag, name), validator(validator) {;}
    
    virtual ~StringOfType()
    {
        delete this->validator;
    }

    static StringOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto validator = BSQRegex::jparse(j["validator"]);

        return new StringOfType(name, validator);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return this->validator->nfare->generate(rnd);
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_string())
        {
            return false;
        }

        auto sstr = j.get<std::string>();

        auto siter = StdStringCodeIterator(sstr);
        bool match = this->validator->nfare->test(siter);
        if(!match)
        {
            return false;
        }
        
        return apimgr.parseStringImpl(apimodule, this, sstr, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimgr.extractStringImpl(apimodule, this, value, ctx);
    }
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string chkinv;

    DataStringType(std::string name, std::string oftype, std::string chkinv) : IGroundedType(TypeTag::DataStringTag, name), oftype(oftype), chkinv(chkinv) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto chkinv = j["chkinv"].get<std::string>();

        return new DataStringType(name, oftype, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("String")->second->jfuzz(apimodule, rnd);
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        bool okparse = apimodule->typemap.find("String")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return apimgr.checkInvokeOk(this->chkinv, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimodule->typemap.find("String")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType() : IGroundedType(TypeTag::ByteBufferTag, "ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j)
    {
        return new ByteBufferType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);
        std::uniform_int_distribution<uint32_t> bgen(0, 255);
        
        auto blen = lgen(rnd);
        std::vector<uint8_t> res;
        res.reserve(blen);

        for(size_t i = 0; i < blen; ++i)
        {
            res.push_back((uint8_t)bgen(rnd));
        }

        return res;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto jdata = j["data"];
        auto jcompress = j["compress"];
        auto jformat = j["format"];
        if(!jdata.is_array() || !jcompress.is_number_unsigned() || j.get<uint8_t>() >= 2 || !jformat.is_number_unsigned() || jformat.get<uint8_t>() >= 4)
        {
            return false;
        }

        std::vector<uint8_t> bbuff;
        bool badval = false;
        std::transform(jdata.cbegin(), jdata.cend(), std::back_inserter(bbuff), [&badval](const json& vv) {
            if(!vv.is_number_unsigned() || vv.get<uint64_t>() >= 256)
            {
                badval = true;
                return (uint8_t)0;
            }
            else
            {
                return vv.get<uint8_t>();
            }
        });

        if(badval)
        {
            return false;
        }

        return apimgr.parseByteBufferImpl(apimodule, this, jcompress.get<uint8_t>(), jformat.get<uint8_t>(), bbuff, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto iiinfo = apimgr.extractByteBufferImpl(apimodule, this, value, ctx);
        if(!iiinfo.has_value())
        {
            return std::nullopt;
        }

        auto rr = json::object();
        rr["compress"] = iiinfo->second.first;
        rr["format"] = iiinfo->second.second;
        rr["data"] = iiinfo->first;

        return std::make_optional(rr);
    }
};

class DataBufferType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string chkinv;

    DataBufferType(std::string name, std::string oftype, std::string chkinv) : IGroundedType(TypeTag::DataBufferTag, name), oftype(oftype), chkinv(chkinv) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto chkinv = j["chkinv"].get<std::string>();

        return new DataBufferType(name, oftype, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("ByteBuffer")->second->jfuzz(apimodule, rnd);
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        bool okparse = apimodule->typemap.find("ByteBuffer")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return apimgr.checkInvokeOk(this->chkinv, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimodule->typemap.find("ByteBuffer")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class DateTimeType : public IGroundedType
{
public:
    DateTimeType() : IGroundedType(TypeTag::DateTimeTag, "DateTime") {;}
    virtual ~DateTimeType() {;}

    static DateTimeType* jparse(json j)
    {
        return new DateTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::time_t tval = std::time(nullptr);

        auto utctime = std::gmtime(&tval);
        char utcstr[20] = {0};
        size_t utcsize = strftime(utcstr, 20, "%Y-%m-%dT%H:%MZ", utctime);
        std::string utcres(utcstr, utcstr + utcsize);
        
        return utcres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToDateTime(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseDateTimeImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractDateTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitDateTime(tval.value());
    }
};

class UTCDateTimeType : public IGroundedType
{
public:
    UTCDateTimeType() : IGroundedType(TypeTag::UTCDateTimeTag, "UTCDateTime") {;}
    virtual ~UTCDateTimeType() {;}

    static UTCDateTimeType* jparse(json j)
    {
        return new UTCDateTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::time_t tval = std::time(nullptr);

        auto utctime = std::gmtime(&tval);
        char utcstr[20] = {0};
        size_t utcsize = strftime(utcstr, 20, "%Y-%m-%dT%H:%Mz", utctime);
        std::string utcres(utcstr, utcstr + utcsize);
        
        return utcres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToUTCDateTime(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseUTCDateTimeImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractUTCDateTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitUTCDateTime(tval.value());
    }
};

class CalendarDateType : public IGroundedType
{
public:
    CalendarDateType() : IGroundedType(TypeTag::CalendarDateTag, "CalendarDate") {;}
    virtual ~CalendarDateType() {;}

    static CalendarDateType* jparse(json j)
    {
        return new CalendarDateType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::time_t tval = std::time(nullptr);

        auto utctime = std::gmtime(&tval);
        char utcstr[20] = {0};
        size_t utcsize = strftime(utcstr, 20, "%Y-%m-%d", utctime);
        std::string utcres(utcstr, utcstr + utcsize);
        
        return utcres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToCalendarDate(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseCalendarDateImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractCalendarDateImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitCalendarDate(tval.value());
    }
};

class TickTimeType : public IGroundedType
{
public:
    TickTimeType() : IGroundedType(TypeTag::TickTimeTag, "TickTime") {;}
    virtual ~TickTimeType() {;}

    static TickTimeType* jparse(json j)
    {
        return new TickTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 128);
        return "L" + std::to_string(ngen(rnd));
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToTickTime(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseTickTimeImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractTickTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitTickTime(tval.value());
    }
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType() : IGroundedType(TypeTag::LogicalTimeTag, "LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j)
    {
        return new LogicalTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 128);
        return "L" + std::to_string(ngen(rnd));
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToLogicalTime(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseLogicalTimeImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractLogicalTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitLogicalTime(tval.value());
    }
};

class ISOTimeStampType : public IGroundedType
{
public:
    ISOTimeStampType() : IGroundedType(TypeTag::ISOTimeStampTag, "ISOTimeStamp") {;}
    virtual ~ISOTimeStampType() {;}

    static ISOTimeStampType* jparse(json j)
    {
        return new ISOTimeStampType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::time_t tval = std::time(nullptr);

        auto utctime = std::gmtime(&tval);
        char utcstr[30] = {0};
        size_t utcsize = strftime(utcstr, 30, "%Y-%m-%dT%H:%M:%S.000Z", utctime);
        std::string utcres(utcstr, utcstr + utcsize);
        
        return utcres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto t = JSONParseHelper::parseToISOTimeStamp(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseISOTimeStampImpl(apimodule, this, t.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto tval = apimgr.extractISOTimeStampImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitISOTimeStamp(tval.value());
    }
};

class UUID4Type : public IGroundedType
{
public:
    UUID4Type() : IGroundedType(TypeTag::UUID4Tag, "UUID4") {;}
    virtual ~UUID4Type() {;}

    static UUID4Type* jparse(json j)
    {
        return new UUID4Type();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::vector<std::string> uuids = {
            "45fa4fbe-7c18-400f-99c8-57d824baa1db",
            "07fdf94f-41a8-4d58-8f1b-7090f02aea3c",
            "1d999dd0-75da-4d57-b4c7-78afd6d1c7e8",
            "09f4758f-83bd-4bb4-b39c-b3de9476c79e",
            "86a7dddf-6302-4feb-b2b7-0c7bb1c9526c",
            "6e37a758-415f-448f-a7b2-e4ce9309ee94",
            "12694350-cd2d-4a71-b188-b215ba4db8aa",
            "5037fa0b-78ec-47f3-926c-ef138a752c09",
            "03423fa4-8ab2-4f2f-9c73-01c682d261c3",
            "e6ff1343-47e2-461c-8391-73aae8848bd6"
        };

        std::uniform_int_distribution<size_t> lgen(0, 9);
        return uuids[lgen(rnd)];
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto uuid = JSONParseHelper::parseUUID4(j);
        if(!uuid.has_value())
        {
            return false;
        }

        return apimgr.parseUUID4Impl(apimodule, this, uuid.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto uval = apimgr.extractUUID4Impl(apimodule, this, value, ctx);
        if(!uval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitUUID4(uval.value());
    }
};

class UUID7Type : public IGroundedType
{
public:
    UUID7Type() : IGroundedType(TypeTag::UUID7Tag, "UUID7") {;}
    virtual ~UUID7Type() {;}

    static UUID7Type* jparse(json j)
    {
        return new UUID7Type();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::vector<std::string> uuids = {
            "45fa4fbe-7c18-400f-99c8-57d824baa1db",
            "07fdf94f-41a8-4d58-8f1b-7090f02aea3c",
            "1d999dd0-75da-4d57-b4c7-78afd6d1c7e8",
            "09f4758f-83bd-4bb4-b39c-b3de9476c79e",
            "86a7dddf-6302-4feb-b2b7-0c7bb1c9526c",
            "6e37a758-415f-448f-a7b2-e4ce9309ee94",
            "12694350-cd2d-4a71-b188-b215ba4db8aa",
            "5037fa0b-78ec-47f3-926c-ef138a752c09",
            "03423fa4-8ab2-4f2f-9c73-01c682d261c3",
            "e6ff1343-47e2-461c-8391-73aae8848bd6"
        };

        std::uniform_int_distribution<size_t> lgen(0, 9);
        return uuids[lgen(rnd)];
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto uuid = JSONParseHelper::parseUUID7(j);
        if(!uuid.has_value())
        {
            return false;
        }

        return apimgr.parseUUID7Impl(apimodule, this, uuid.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto uval = apimgr.extractUUID7Impl(apimodule, this, value, ctx);
        if(!uval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitUUID7(uval.value());
    }
};

class SHAContentHashType : public IGroundedType
{
public:
    SHAContentHashType() : IGroundedType(TypeTag::SHAContentHashTag, "SHAContentHash") {;}
    virtual ~SHAContentHashType() {;}

    static SHAContentHashType* jparse(json j)
    {
        return new SHAContentHashType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
         std::vector<std::string> shas = {
            "0x31bca02094eb78126a517b206a88c73cfa9ec6f704c7030d18212cace820f025f00bf0ea68dbf3f3a5436ca63b53bf7bf80ad8d5de7d8359d0b7fed9dbc3ab99",
            "0x4dff4ea340f0a823f15d3f4f01ab62eae0e5da579ccb851f8db9dfe84c58b2b37b89903a740e1ee172da793a6e79d560e5f7f9bd058a12a280433ed6fa46510a",
            "0x40b244112641dd78dd4f93b6c9190dd46e0099194d5a44257b7efad6ef9ff4683da1eda0244448cb343aa688f5d3efd7314dafe580ac0bcbf115aeca9e8dc114",
            "0x3bafbf08882a2d10133093a1b8433f50563b93c14acd05b79028eb1d12799027241450980651994501423a66c276ae26c43b739bc65c4e16b10c3af6c202aebb",
            "0xa321d8b405e3ef2604959847b36d171eebebc4a8941dc70a4784935a4fca5d5813de84dfa049f06549aa61b20848c1633ce81b675286ea8fb53db240d831c568",
            "0x06df05371981a237d0ed11472fae7c94c9ac0eff1d05413516710d17b10a4fb6f4517bda4a695f02d0a73dd4db543b4653df28f5d09dab86f92ffb9b86d01e25",
            "0x3c9ad55147a7144f6067327c3b82ea70e7c5426add9ceea4d07dc2902239bf9e049b88625eb65d014a7718f79354608cab0921782c643f0208983fffa3582e40",
            "0xf05210c5b4263f0ec4c3995bdab458d81d3953f354a9109520f159db1e8800bcd45b97c56dce90a1fc27ab03e0b8a9af8673747023c406299374116d6f966981",
            "0xbc23b8b01772d2dd67efb8fe1a5e6bd0f44b97c36101be6cc09f253b53e68d67a22e4643068dfd1341980134ea57570acf65e306e4d96cef4d560384894c88a4",
            "0x0dc526d8c4fa04084f4b2a6433f4cd14664b93df9fb8a9e00b77ba890b83704d24944c93caa692b51085bb476f81852c27e793600f137ae3929018cd4c8f1a45"
        };

        std::uniform_int_distribution<size_t> lgen(0, 9);
        return shas[lgen(rnd)];
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto hash = JSONParseHelper::parseSHAContentHash(j);
        if(!hash.has_value())
        {
            return false;
        }

        return apimgr.parseSHAContentHashImpl(apimodule, this, hash.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto hash = apimgr.extractSHAContentHashImpl(apimodule, this, value, ctx);
        if(!hash.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitSHAHash(hash.value());
    }
};

class LatLongCoordinateType : public IGroundedType
{
public:
    LatLongCoordinateType() : IGroundedType(TypeTag::LatLongCoordinateTag, "LatLongCoordinate") {;}
    virtual ~LatLongCoordinateType() {;}

    static LatLongCoordinateType* jparse(json j)
    {
        return new LatLongCoordinateType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::vector<std::string> uuids = {
            "45fa4fbe-7c18-400f-99c8-57d824baa1db",
            "07fdf94f-41a8-4d58-8f1b-7090f02aea3c",
            "1d999dd0-75da-4d57-b4c7-78afd6d1c7e8",
            "09f4758f-83bd-4bb4-b39c-b3de9476c79e",
            "86a7dddf-6302-4feb-b2b7-0c7bb1c9526c",
            "6e37a758-415f-448f-a7b2-e4ce9309ee94",
            "12694350-cd2d-4a71-b188-b215ba4db8aa",
            "5037fa0b-78ec-47f3-926c-ef138a752c09",
            "03423fa4-8ab2-4f2f-9c73-01c682d261c3",
            "e6ff1343-47e2-461c-8391-73aae8848bd6"
        };

        std::uniform_int_distribution<size_t> lgen(0, 9);
        return uuids[lgen(rnd)];
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto llv = JSONParseHelper::parseLatLongCoordinate(j);
        if(!llv.has_value())
        {
            return false;
        }

        return apimgr.parseLatLongCoordinateImpl(apimodule, this, llv.value().first, llv.value().second, value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto uval = apimgr.extractLatLongCoordinateImpl(apimodule, this, value, ctx);
        if(!uval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitLatLongCoordinate(uval.value());
    }
};

class ConstructableOfType : public IGroundedType
{
public:
    const std::string oftype;
    const std::optional<std::string> validatefunc; 

    ConstructableOfType(std::string name, std::string oftype, std::optional<std::string> validatefunc) : IGroundedType(TypeTag::ConstructableOfType, name), oftype(oftype), validatefunc(validatefunc) {;}
    virtual ~ConstructableOfType() {;}

    static ConstructableOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto validatefunc = (j["validatefunc"] != nullptr ? std::make_optional(j["validatefunc"].get<std::string>()) : std::nullopt);
    
        return new ConstructableOfType(name, oftype, validatefunc);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find(this->oftype)->second->jfuzz(apimodule, rnd);
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        bool okparse = apimodule->typemap.find(this->oftype)->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->validatefunc.has_value() || apimgr.checkInvokeOk(this->validatefunc.value(), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        return apimodule->typemap.find(this->oftype)->second->textract(apimgr, apimodule, value, ctx);
    }
};

class TupleType : public IGroundedType
{
public:
    const std::vector<std::string> ttypes;

    TupleType(std::string name, std::vector<std::string> ttypes) : IGroundedType(TypeTag::TupleTag, name), ttypes(ttypes) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();

        std::vector<std::string> ttypes;
        auto jtypes = j["ttypes"];
        std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
            return jv.get<std::string>();
        });

        return new TupleType(name, ttypes);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        auto tj = json::array();
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            const std::string& tt = this->ttypes[i];

            auto jval = apimodule->typemap.find(tt)->second->jfuzz(apimodule, rnd);
            tj.push_back(jval);
        }

        return tj;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_array() || this->ttypes.size() != j.size())
        {
            return false;
        }

        apimgr.prepareParseTuple(apimodule, this, ctx);
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i])->second;

            ValueRepr vval = apimgr.getValueForTupleIndex(apimodule, this, value, i, ctx);
            bool ok = tt->tparse(apimgr, apimodule, j[i], vval, ctx);
            if(!ok)
            {
                return false;
            }
        }
        apimgr.completeParseTuple(apimodule, this, value, ctx);

        return true;
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto jres = json::array();
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i])->second;

            ValueRepr vval = apimgr.extractValueForTupleIndex(apimodule, this, value, i, ctx);
            auto rr = tt->textract(apimgr, apimodule, vval, ctx);
            if(!rr.has_value())
            {
                return std::nullopt;
            }

            jres.push_back(rr.value());
        }
        
        return std::make_optional(jres);
    }
};

class RecordType : public IGroundedType
{
public:
    const std::vector<std::string> props;
    const std::vector<std::string> ttypes;

    RecordType(std::string name, std::vector<std::string> props, std::vector<std::string> ttypes) : IGroundedType(TypeTag::RecordTag, name), props(props), ttypes(ttypes) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();

        std::vector<std::string> props;
        auto jprops = j["props"];
        std::transform(jprops.cbegin(), jprops.cend(), std::back_inserter(props), [](const json& jv) {
            return jv.get<std::string>();
        });

        std::vector<std::string> ttypes;
        auto jtypes = j["ttypes"];
        std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
            return jv.get<std::string>();
        });

        return new RecordType(name, props, ttypes);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        auto tj = json::object();
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            const std::string& tt = this->ttypes[i];

            auto jval = apimodule->typemap.find(tt)->second->jfuzz(apimodule, rnd);
            tj[this->props[i]] = jval;
        }

        return tj;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_object() || this->props.size() != j.size())
        {
            return false;
        }

        auto allprops = std::all_of(this->props.cbegin(), this->props.cend(), [&j](const std::string& prop){
            return j.contains(prop);
        });
        if(!allprops)
        {
            return false;
        }

        apimgr.prepareParseRecord(apimodule, this, ctx);
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i])->second;

            ValueRepr vval = apimgr.getValueForRecordProperty(apimodule, this, value, this->props[i], ctx);
            bool ok = tt->tparse(apimgr, apimodule, j[this->props[i]], vval, ctx);
            if(!ok)
            {
                return false;
            }
        }
        apimgr.completeParseRecord(apimodule, this, value, ctx);

        return true;
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto jres = json::object();
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i])->second;

            ValueRepr vval = apimgr.extractValueForRecordProperty(apimodule, this, value, this->props[i], ctx);
            auto rr = tt->textract(apimgr, apimodule, vval, ctx);
            if(!rr.has_value())
            {
                return std::nullopt;
            }

            jres[this->props[i]] = rr.value();
        }
        
        return std::make_optional(jres);
    }
};

enum class ContainerCategory
{
    List = 0x0,
    Stack,
    Queue,
    Set
};

class ContainerTType : public IGroundedType
{
public:
    const ContainerCategory category;
    const std::string elemtype;

    ContainerTType(std::string name, ContainerCategory category, std::string elemtype) : IGroundedType(TypeTag::ContainerTTag, name), category(category), elemtype(elemtype) {;}
    virtual ~ContainerTType() {;}

    static ContainerTType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto category = j["category"].get<ContainerCategory>();
        auto elemtype = j["elemtype"].get<std::string>();

        return new ContainerTType(name, category, elemtype);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);

        auto clen = lgen(rnd);
        auto tj = json::array();
        for(size_t i = 0; i < clen; ++i)
        {
            auto jval = apimodule->typemap.find(this->elemtype)->second->jfuzz(apimodule, rnd);
            tj.push_back(jval);
        }

        return tj;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_array())
        {
            return false;
        }

        apimgr.prepareParseContainer(apimodule, this, value, j.size(), ctx);
        auto tt = apimodule->typemap.find(this->elemtype)->second;
        for(size_t i = 0; i < j.size(); ++i)
        {
            ValueRepr vval = apimgr.getValueForContainerElementParse_T(apimodule, this, value, i, ctx);
            bool ok = tt->tparse(apimgr, apimodule, j[i], vval, ctx);
            if(!ok)
            {
                return false;
            }
        }
        apimgr.completeParseContainer(apimodule, this, value, ctx);

        return true;
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        apimgr.prepareExtractContainer(apimodule, this, value, ctx);
        auto clen = apimgr.extractLengthForContainer(apimodule, this, value, ctx);
        if(!clen.has_value())
        {
            return std::nullopt;
        }

        auto jres = json::array();
        auto tt = apimodule->typemap.find(this->elemtype)->second;
        for(size_t i = 0; i < clen.value(); ++i)
        {
            ValueRepr vval = apimgr.extractValueForContainer_T(apimodule, this, value, i, ctx);
            auto rr = tt->textract(apimgr, apimodule, vval, ctx);
            if(!rr.has_value())
            {
                return std::nullopt;
            }

            jres.push_back(rr.value());
        }
        
        apimgr.completeExtractContainer(apimodule, this, ctx);
        return std::make_optional(jres);
    }
};

class ContainerKVType : public IGroundedType
{
public:
    const std::string ktype;
    const std::string vtype;

    ContainerKVType(std::string name, std::string ktype, std::string vtype) : IGroundedType(TypeTag::ContainerKVTag, name), ktype(ktype), vtype(vtype) {;}
    virtual ~ContainerKVType() {;}

    static ContainerKVType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto ktype = j["ktype"].get<std::string>();
        auto vtype = j["vtype"].get<std::string>();

        return new ContainerKVType(name, ktype, vtype);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);

        auto clen = lgen(rnd);
        auto tj = json::array();
        for(size_t i = 0; i < clen; ++i)
        {
            auto kval = apimodule->typemap.find(this->ktype)->second->jfuzz(apimodule, rnd);
            auto vval = apimodule->typemap.find(this->vtype)->second->jfuzz(apimodule, rnd);

            auto kventry = json::array({kval, vval});
            tj.push_back(kventry);
        }

        return tj;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(!j.is_array())
        {
            return false;
        }

        apimgr.prepareParseContainer(apimodule, this, value, j.size(), ctx);
        auto kt = apimodule->typemap.find(this->ktype)->second;
        auto vt = apimodule->typemap.find(this->vtype)->second;
        for(size_t i = 0; i < j.size(); ++i)
        {
            std::pair<ValueRepr, ValueRepr> vval = apimgr.getValueForContainerElementParse_KV(apimodule, this, value, i, ctx);
            bool kok = kt->tparse(apimgr, apimodule, j[i][0], vval.first, ctx);
            bool vok = vt->tparse(apimgr, apimodule, j[i][1], vval.second, ctx);
            if(!kok || !vok)
            {
                return false;
            }
        }
        apimgr.completeParseContainer(apimodule, this, value, ctx);

        return true;
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        apimgr.prepareExtractContainer(apimodule, this, value, ctx);
        auto clen = apimgr.extractLengthForContainer(apimodule, this, value, ctx);
        if(!clen.has_value())
        {
            return std::nullopt;
        }

        auto jres = json::array();
        auto kt = apimodule->typemap.find(this->ktype)->second;
        auto vt = apimodule->typemap.find(this->vtype)->second;
        for(size_t i = 0; i < clen.value(); ++i)
        {
            std::pair<ValueRepr, ValueRepr> vval = apimgr.extractValueForContainer_KV(apimodule, this, value, i, ctx);
            auto kr = kt->textract(apimgr, apimodule, vval.first, ctx);
            auto vr = vt->textract(apimgr, apimodule, vval.second, ctx);
            if(!kr.has_value() || !vr.has_value())
            {
                return std::nullopt;
            }

            auto jentry = json::array({kr.value(), vr.value()});
            jres.push_back(jentry);
        }
        
        apimgr.completeExtractContainer(apimodule, this, ctx);
        return std::make_optional(jres);
    }
};

class EnumType : public IGroundedType
{
public:
    const std::vector<std::string> enums;

    EnumType(std::string name, std::vector<std::string> enums) : IGroundedType(TypeTag::EnumTag, name), enums(enums) {;}
    virtual ~EnumType() {;}

    static EnumType* jparse(json j)
    {
        std::vector<std::string> enums;
        auto jenuminvs = j["enums"];
        std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enums), [](const json& jv) {
            return jv.get<std::string>();
        });

        return new EnumType(j["name"].get<std::string>(), enums);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, this->enums.size() - 1);
        return JSONParseHelper::emitUnsignedNumber(ngen(rnd)).value();
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto nstrinfo = JSONParseHelper::checkEnumName(j);
        if(!nstrinfo.has_value())
        {
            return false;
        }

        if(nstrinfo.value().first != this->name)
        {
            return false;
        }

        auto namestr = nstrinfo.value().second;
        auto pos = std::find_if(this->enums.cbegin(), this->enums.cend(), [&namestr](const std::string& entry) {
            return entry == namestr;
        });

        if(pos == this->enums.cend())
        {
            return false;
        }
        
        return apimgr.parseNatImpl(apimodule, this, (uint64_t)std::distance(this->enums.cbegin(), pos), value, ctx);
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto nval = apimgr.extractNatImpl(apimodule, this, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        return std::make_optional(this->name + "::" + this->enums[nval.value()]);
    }
};

class EntityType : public IGroundedType
{
public:
    const std::vector<std::pair<std::string, std::string>> consfields; //name, fkey
    const std::vector<std::pair<std::string, bool>> ttypes;

    const std::optional<std::string> validatefunc; //key
    const std::optional<std::string> consfunc; //key

    EntityType(std::string name, std::vector<std::pair<std::string, std::string>> consfields, std::vector<std::pair<std::string, bool>> ttypes, std::optional<std::string> validatefunc, std::optional<std::string> consfunc) : IGroundedType(TypeTag::EntityTag, name), consfields(consfields), ttypes(ttypes), validatefunc(validatefunc), consfunc(consfunc) {;}
    virtual ~EntityType() {;}

    static EntityType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();

        std::vector<std::pair<std::string, std::string>> consfields;
        auto jprops = j["consfields"];
        std::transform(jprops.cbegin(), jprops.cend(), std::back_inserter(consfields), [](const json& jv) {
            return std::make_pair(jv["fname"].get<std::string>(), jv["fkey"].get<std::string>());
        });

        std::vector<std::pair<std::string, bool>> ttypes;
        auto jtypes = j["ttypes"];
        std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
            return std::make_pair(jv["declaredType"].get<std::string>(), jv["isOptional"].get<bool>());
        });

        auto validatefunc = (j["validatefunc"] != nullptr ? std::make_optional(j["validatefunc"].get<std::string>()) : std::nullopt);
        auto consfunc = (j["consfunc"] != nullptr ? std::make_optional(j["consfunc"].get<std::string>()) : std::nullopt);

        return new EntityType(name, consfields, ttypes, validatefunc, consfunc);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        auto jres = json::object();
        for(size_t i = 0; i < this->consfields.size(); ++i)
        {
            jres[this->consfields[i].first] = apimodule->typemap.find(this->ttypes[i].first)->second->jfuzz(apimodule, rnd);
        }

        return jres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        if(j.is_array() && j.size() == 2 && j[0].is_string())
        {
            if(j[0].get<std::string>() != this->name)
            {
                return false;
            }
            j = j[1];
        }

        if(!j.is_object())
        {
            return false;
        }

        for (auto iter = j.cbegin(); iter != j.end(); iter++) {
            auto fkey = iter.key();
            if(fkey == "__type_tag__")
            {
                continue;
            }

            auto fpos = std::find_if(this->consfields.cbegin(), this->consfields.cend(), [&fkey](const std::pair<std::string, std::string>& fnamekey) {
                return fnamekey.second == fkey;
            });

            if(fpos == this->consfields.cend())
            {
                return false;
            }
        }

        auto firstoptpos = std::find_if(this->ttypes.cbegin(), this->ttypes.cend(), [](const std::pair<std::string, bool>& tentry) {
            return tentry.second;
        });
        auto firstoptdist = std::distance(this->ttypes.cbegin(), firstoptpos);

        apimgr.prepareParseEntity(apimodule, this, ctx);
        apimgr.prepareParseEntityMask(apimodule, this, ctx);
        for(size_t i = 0; i < this->consfields.size(); ++i)
        {
            auto fname = this->consfields[i].first;
        
            if(j.find(fname) == j.cend())
            {
                if(!this->ttypes[i].second)
                {
                    return false;
                }

                apimgr.setMaskFlag(apimodule, value, i - firstoptdist, false, ctx);
            }
            else
            {
                auto tt = apimodule->typemap.find(this->ttypes[i].first)->second;

                ValueRepr vval = apimgr.getValueForEntityField(apimodule, this, value, this->consfields[i], ctx);
                bool ok = tt->tparse(apimgr, apimodule, j[fname], vval, ctx);
                if(!ok)
                {
                    return false;
                }

                if(this->ttypes[i].second)
                {
                    apimgr.setMaskFlag(apimodule, value, i - firstoptdist, true, ctx);
                }
            }
        }
        apimgr.completeParseEntity(apimodule, this, value, ctx);

        return true;
    }

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto jres = json::object();
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i].first)->second;

            ValueRepr vval = apimgr.extractValueForEntityField(apimodule, this, value, this->consfields[i], ctx);
            auto rr = tt->textract(apimgr, apimodule, vval, ctx);
            if(!rr.has_value())
            {
                return std::nullopt;
            }

            jres[this->consfields[i].first] = rr.value();
        }
        
        return std::make_optional(jres);
    }
};

class UnionType : public IType
{
public:
    const std::vector<std::string> opts;

    UnionType(std::string name, std::vector<std::string> opts) : IType(TypeTag::UnionTag, name), opts(opts) {;}
    virtual ~UnionType() {;}

    static UnionType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();

        std::vector<std::string> opts;
        auto jopts = j["opts"];
        std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](const json& jv) {
            return jv.get<std::string>();
        });

        return new UnionType(name, opts);
    }

    virtual bool isUnion() const override
    {
        return true;
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, this->opts.size() - 1);
        auto oftype = this->opts[ngen(rnd)];

        auto jres = json::array();
        jres.push_back(oftype);
        jres.push_back(apimodule->typemap.find(oftype)->second->jfuzz(apimodule, rnd));
        return jres;
    }

    template <typename ValueRepr, typename State>
    bool parse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
    {
        auto opttypes = apimodule->getAllTypesInUnion(this);

        if(j.is_object())
        {
            auto typetagref = j["__type_tag__"];
            if(!typetagref.is_string())
            {
                return false;
            }

            auto oftyperef = apimodule->typemap.find(typetagref.get<std::string>());
            if(oftyperef == apimodule->typemap.cend())
            {
                return false;
            }

            auto ofidxref = std::find_if(opttypes.cbegin(), opttypes.cend(), [oftyperef](const IType* tt) {
                return tt->name == oftyperef->second->name;
            });
            if(ofidxref == opttypes.cend())
            {
                return false;
            }

            auto ofidx = std::distance(opttypes.cbegin(), ofidxref);
            auto vval = apimgr.parseUnionChoice(apimodule, oftyperef->second, value, ofidx, oftyperef->second, ctx);
            return oftyperef->second->tparse(apimgr, apimodule, j, vval, ctx);
        }
        else{
            if(!j.is_array() || j.size() != 2 || !j[0].is_string())
            {
                return false;
            }

            auto oftyperef = apimodule->typemap.find(j[0].get<std::string>());
            if(oftyperef == apimodule->typemap.cend())
            {
                return false;
            }

            auto ofidxref = std::find_if(opttypes.cbegin(), opttypes.cend(), [oftyperef](const IType* tt) {
                return tt->name == oftyperef->second->name;
            });
            if(ofidxref == opttypes.cend())
            {
                return false;
            }

            auto ofidx = std::distance(opttypes.cbegin(), ofidxref);

            auto vval = apimgr.parseUnionChoice(apimodule, oftyperef->second, value, ofidx, oftyperef->second, ctx);
            return oftyperef->second->tparse(apimgr, apimodule, j[1], vval, ctx);
        }
    } 

    template <typename ValueRepr, typename State>
    std::optional<json> extract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
    {
        auto opttypes = apimodule->getAllTypesInUnion(this);

        auto nval = apimgr.extractUnionChoice(apimodule, this, opttypes, value, ctx);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        auto choicetype = opttypes[nval.value()];
        auto uvalue = apimgr.extractUnionValue(apimodule, this, value, nval.value(), ctx);

        auto cval = choicetype->textract(apimgr, apimodule, uvalue, ctx);
        if(!cval.has_value())
        {
            return std::nullopt;
        }

        json rj = cval.value();
        if(rj.is_object())
        {
            rj["__type_tag__"] = choicetype->name;
        }
        else
        {
            rj = json::array();
            rj[0] = choicetype->name;
            rj[1] = cval.value();
        }

        return std::make_optional(rj);
    }
};

template <typename ValueRepr, typename State>
bool IType::tparse(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, json j, ValueRepr value, State& ctx) const
{
    switch(this->tag)
    {
        case TypeTag::NoneTag:
            return dynamic_cast<const NoneType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::NothingTag:
            return dynamic_cast<const NothingType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::BoolTag:
            return dynamic_cast<const BoolType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::NatTag:
            return dynamic_cast<const NatType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::IntTag:
            return dynamic_cast<const IntType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::BigNatTag:
            return dynamic_cast<const BigNatType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::BigIntTag:
            return dynamic_cast<const BigIntType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::RationalTag:
            return dynamic_cast<const RationalType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::FloatTag:
            return dynamic_cast<const FloatType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::DecimalTag:
            return dynamic_cast<const DecimalType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::StringTag:
            return dynamic_cast<const StringType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::StringOfTag:
            return dynamic_cast<const StringOfType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::DataStringTag:
            return dynamic_cast<const DataStringType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::ByteBufferTag:
            return dynamic_cast<const ByteBufferType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::DataBufferTag:
            return dynamic_cast<const DataBufferType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::DateTimeTag:
            return dynamic_cast<const DateTimeType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::UTCDateTimeTag:
            return dynamic_cast<const UTCDateTimeType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::CalendarDateTag:
            return dynamic_cast<const CalendarDateType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::TickTimeTag:
            return dynamic_cast<const TickTimeType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::LogicalTimeTag:
            return dynamic_cast<const LogicalTimeType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::ISOTimeStampTag:
            return dynamic_cast<const ISOTimeStampType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::UUID4Tag:
            return dynamic_cast<const UUID4Type*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::UUID7Tag:
            return dynamic_cast<const UUID7Type*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::SHAContentHashTag:
            return dynamic_cast<const SHAContentHashType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::LatLongCoordinateTag:
            return dynamic_cast<const LatLongCoordinateType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::ConstructableOfType:
            return dynamic_cast<const ConstructableOfType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::TupleTag:
            return dynamic_cast<const TupleType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::RecordTag:
            return dynamic_cast<const RecordType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::ContainerTTag:
            return dynamic_cast<const ContainerTType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::ContainerKVTag:
            return dynamic_cast<const ContainerKVType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::EnumTag:
            return dynamic_cast<const EnumType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::EntityTag:
            return dynamic_cast<const EntityType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        case TypeTag::UnionTag:
            return dynamic_cast<const UnionType*>(this)->parse(apimgr, apimodule, j, value, ctx);
        default: 
        {
            assert(false);
            return false;
        }
    }
}

template <typename ValueRepr, typename State>
std::optional<json> IType::textract(ApiManagerJSON<ValueRepr, State>& apimgr, const APIModule* apimodule, ValueRepr value, State& ctx) const
{
    switch(this->tag)
    {
        case TypeTag::NoneTag:
            return dynamic_cast<const NoneType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::NothingTag:
            return dynamic_cast<const NothingType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::BoolTag:
            return dynamic_cast<const BoolType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::NatTag:
            return dynamic_cast<const NatType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::IntTag:
            return dynamic_cast<const IntType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::BigNatTag:
            return dynamic_cast<const BigNatType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::BigIntTag:
            return dynamic_cast<const BigIntType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::RationalTag:
            return dynamic_cast<const RationalType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::FloatTag:
            return dynamic_cast<const FloatType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::DecimalTag:
            return dynamic_cast<const DecimalType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::StringTag:
            return dynamic_cast<const StringType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::StringOfTag:
            return dynamic_cast<const StringOfType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::DataStringTag:
            return dynamic_cast<const DataStringType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::ByteBufferTag:
            return dynamic_cast<const ByteBufferType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::DataBufferTag:
            return dynamic_cast<const DataBufferType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::DateTimeTag:
            return dynamic_cast<const DateTimeType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::UTCDateTimeTag:
            return dynamic_cast<const UTCDateTimeType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::CalendarDateTag:
            return dynamic_cast<const CalendarDateType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::TickTimeTag:
            return dynamic_cast<const TickTimeType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::LogicalTimeTag:
            return dynamic_cast<const LogicalTimeType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::ISOTimeStampTag:
            return dynamic_cast<const ISOTimeStampType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::UUID4Tag:
            return dynamic_cast<const UUID4Type*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::UUID7Tag:
            return dynamic_cast<const UUID7Type*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::SHAContentHashTag:
            return dynamic_cast<const SHAContentHashType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::LatLongCoordinateTag:
            return dynamic_cast<const LatLongCoordinateType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::ConstructableOfType:
            return dynamic_cast<const ConstructableOfType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::TupleTag:
            return dynamic_cast<const TupleType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::RecordTag:
            return dynamic_cast<const RecordType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::ContainerTTag:
            return dynamic_cast<const ContainerTType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::ContainerKVTag:
            return dynamic_cast<const ContainerKVType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::EnumTag:
            return dynamic_cast<const EnumType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::EntityTag:
            return dynamic_cast<const EntityType*>(this)->extract(apimgr, apimodule, value, ctx);
        case TypeTag::UnionTag:
            return dynamic_cast<const UnionType*>(this)->extract(apimgr, apimodule, value, ctx);
        default: 
        {
            assert(false);
            return std::nullopt;
        }
    }
}


