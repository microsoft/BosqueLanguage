
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "bsqregex.h"

class IType;
class InvokeSignature;
class APIModule;

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
    PrimitiveOfTag,
    DataStringTag,
    ByteBufferTag,
    DataBufferTag,
    ISOTimeTag,
    LogicalTimeTag,
    UUIDTag,
    ContentHashTag,
    ISOTimeOfTag,
    LogicalTimeOfTag,
    UUIDOfTag,
    ContentHashOfTag,
    TupleTag,
    RecordTag,
    SomethingTag,
    OkTag,
    ErrTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    EnumTag,
    EntityTag,
    UnionTag,
    ConceptTag
};

template <typename ObjModel, typename ParseContext, typename ExtractContext>
class ApiManagerJSON
{
public:
    virtual bool checkInvokeOk(const std::string& checkinvoke, ObjModel& value);

    virtual bool parseNoneImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseNothingImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseDataStringImpl(const APIModule* apimodule, const IType* itype, std::string s, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseByteBufferImpl(const APIModule* apimodule, const IType* itype, vector<uint8_t>& data, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseISOTimeImpl(const APIModule* apimodule, const IType* itype, TimeData t, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseUUIDImpl(const APIModule* apimodule, const IType* itype, std::string s, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseContentHashImpl(const APIModule* apimodule, const IType* itype, std::string s, ObjModel& value, ParseContext& ctx) const = 0;
    
    TupleTag,
    RecordTag,
    SomethingTag,
    OkTag,
    ErrTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    EnumTag,
    EntityTag,
    UnionTag,
    ConceptTag


    virtual std::optional<bool> extractBoolImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<uint64_t> extractNatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<int64_t> extractIntImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractBigNatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractBigIntImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractFloatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractDecimalImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::pair<std::string, uint64_t>> extractRationalImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractStringImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::vector<uint8_t>> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<TimeData> extractISOTimeImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<uint64_t> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractUUIDImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<std::string> extractContentHashImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;

    TupleTag,
    RecordTag,
    SomethingTag,
    OkTag,
    ErrTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    EnumTag,
    EntityTag,
    UnionTag,
    ConceptTag
};

struct TimeData
{
    uint16_t millis; // 0-999
    uint16_t year;   // Year since 1900
    uint8_t month;   // 0-11
    uint8_t day;     // 1-31
    uint8_t hour;    // 0-23
    uint8_t min;     // 0-59
    uint8_t sec;     // 0-60
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
    static std::optional<TimeData> parseToTimeData(json j);

    static std::optional<json> emitUnsignedNumber(uint64_t n);
    static std::optional<json> emitSignedNumber(int64_t i);
    static std::optional<json> emitBigUnsignedNumber(std::string s);
    static std::optional<json> emitBigSignedNumber(std::string s);
    static std::optional<json> emitRealNumber(std::string s);
    static std::optional<json> emitDecimalNumber(std::string s);
    static std::optional<json> emitRationalNumber(std::pair<std::string, uint64_t> rv);
    static std::optional<json> emitTimeData(TimeData t);

    static std::optional<std::string> checkIsUUID(json j);
    static std::optional<std::string> checkIsContentHash(json j);
};

class IType
{
public:
    const TypeTag tag;
    const std::string name;

    IType(TypeTag tag, std::string name) : tag(tag), name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const = 0;

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool tparse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx);

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> textract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const;
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
    NoneType() : IGroundedType(TypeTag::NoneTag, "NSCore::None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j)
    {
        return new NoneType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return "null";
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_null())
        {
            return false;
        }
        
        return apimgr.parseNoneImpl(apimodule, this, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return std::make_optional(nullptr);
    }
};

class NothingType : public IGroundedType
{
public:
    NothingType() : IGroundedType(TypeTag::NothingTag, "NSCore::Nothing") {;}
    virtual ~NothingType() {;}

    static NothingType* jparse(json j)
    {
        return new NothingType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return "null";
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_null())
        {
            return false;
        }
        
        return apimgr.parseNothingImpl(apimodule, this, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return std::make_optional(nullptr);
    }
};

class BoolType : public IGroundedType
{
public:
    BoolType() : IGroundedType(TypeTag::BoolTag, "NSCore::Bool") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_boolean())
        {
            return false;
        }
        
        return apimgr.parseBoolImpl(apimodule, this, j.get<bool>(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractBoolImpl(apimodule, this, value, ctx);
    }
};

class NatType : public IGroundedType
{
public:
    NatType() : IGroundedType(TypeTag::NatTag, "NSCore::Nat") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<uint64_t> nval = JSONParseHelper::parseToUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseNatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    IntType() : IGroundedType(TypeTag::IntTag, "NSCore::Int") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<int64_t> nval = JSONParseHelper::parseToSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseIntImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    BigNatType() : IGroundedType(TypeTag::BigNatTag, "NSCore::BigNat") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper.parseToBigUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigNatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    BigIntType() : IGroundedType(TypeTag::BigIntTag, "NSCore::BigInt") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper.parseToBigSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigIntImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    RationalType() : IGroundedType(TypeTag::RationalTag, "NSCore::Rational") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::pair<std::string, uint64_t>> nval = JSONParseHelper::parseToRationalNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseRationalImpl(apimodule, this, nval.value().first, nval.value().second, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    FloatType() : IGroundedType(TypeTag::FloatTag, "NSCore::Float") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToRealNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseFloatImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    DecimalType() : IGroundedType(TypeTag::DecimalTag, "NSCore::Decimal") {;}
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper::parseToRealNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseDecimalImpl(apimodule, this, nval.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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
    StringType() : IGroundedType(TypeTag::StringTag, "NSCore::String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j)
    {
        return new StringType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);
        std::uniform_int_distribution<uint8_t> cgen(32, 126);
        
        auto slen = lgen(rnd);
        std::vector<uint8_t> res;
        res.reserve(slen);

        for(size_t i = 0; i < slen; ++i)
        {
            res.push_back(cgen(rnd));
        }

        return std::string(res.cbegin(), res.cend());
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_string())
        {
            return false;
        }
        
        return apimgr.parseStringImpl(apimodule, this, j.get<std::string>(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_string())
        {
            return false;
        }

        auto sstr = j.get<std::string>();

        auto siter = StdStringCodeIterator(sstr);
        bool match = this->validator->nfare->match(siter);
        if(!match)
        {
            return false;
        }
        
        return apimgr.parseStringImpl(apimodule, this, sstr, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractStringImpl(apimodule, this, value, ctx);
    }
};

class PrimitiveOfType : public IGroundedType
{
public:
    const std::string oftype;
    const std::optional<std::string> chkinv; 

    PrimitiveOfType(std::string name, std::string oftype, std::optional<std::string> chkinv) : IGroundedType(TypeTag::PrimitiveOfTag, name), oftype(oftype), chkinv(chkinv) {;}
    virtual ~PrimitiveOfType() {;}

    static PrimitiveOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);
    
        return new PrimitiveOfType(name, oftype, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find(this->oftype)->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find(this->oftype)->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find(this->oftype)->second->textract(apimgr, apimodule, value, ctx);
    }
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;
    const std::optional<std::string> chkinv;

    DataStringType(std::string name, std::string oftype, std::optional<std::string> chkinv) : IGroundedType(TypeTag::DataStringTag, name), oftype(oftype), chkinv(chkinv) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);

        return new DataStringType(name, oftype, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("String")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("String")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("String")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType() : IGroundedType(TypeTag::ByteBufferTag, "NSCore::ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j)
    {
        return new ByteBufferType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<size_t> lgen(0, 64);
        std::uniform_int_distribution<uint8_t> bgen(0, 255);
        
        auto blen = lgen(rnd);
        std::vector<uint8_t> res;
        res.reserve(blen);

        for(size_t i = 0; i < blen; ++i)
        {
            res.push_back(bgen(rnd));
        }

        return res;
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_array())
        {
            return false;
        }

        std::vector<uint8_t> bbuff;
        bool badval = false;
        std::transform(j.cbegin(), j.cend(), [&badval](const json& vv) {
            if(!vv.is_number_unsigned() || vv.get<uint64_t>() >= 256)
            {
                badval = true;
                return 0;
            }
            else
            {
                return vv.get<uint64_t>();
            }
        });

        if(badval)
        {
            return false;
        }

        return apimgr.parseByteBufferImpl(apimodule, this, bbuff, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractByteBufferImpl(apimodule, this, value, ctx);
    }
};

class DataBufferType : public IGroundedType
{
public:
    const std::string oftype;
    const std::optional<std::string> chkinv;

    DataBufferType(std::string name, std::string oftype, std::optional<std::string> chkinv) : IGroundedType(TypeTag::DataBufferTag, name), oftype(oftype), chkinv(chkinv) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto oftype = j["oftype"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);

        return new DataBufferType(name, oftype, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("ByteBuffer")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("ByteBuffer")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("ByteBuffer")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class ISOTimeType : public IGroundedType
{
public:
    ISOTimeType() : IGroundedType(TypeTag::ISOTimeTag, "NSCore::ISOTime") {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j)
    {
        return new ISOTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::time_t tval = std::time(nullptr);
        auto utctime = std::gmtime(&tval);

        char sstr[20] = {0};
        strftime(sstr, 20, "%Y-%m-%dT%H:%M:%S", utctime);

        std::string res(sstr, sstr + 20);
        return res + ".000Z";
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        auto t = JSONParseHelper::parseToTimeData(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseISOTimeImpl(apimodule, this, t, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        auto tval = apimgr.extractISOTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitTimeData(tval.value());
    }
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType() : IGroundedType(TypeTag::LogicalTimeTag, "NSCore::LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j)
    {
        return new LogicalTimeType();
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 128);
        return JSONParseHelper::emitUnsignedNumber(ngen(rnd)).value();
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        auto t = JSONParseHelper::parseToUnsignedNumber(j);
        if(!t.has_value())
        {
            return false;
        }

        return apimgr.parseLogicalTimeImpl(apimodule, this, t, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        auto tval = apimgr.extractLogicalTimeImpl(apimodule, this, value, ctx);
        if(!tval.has_value())
        {
            return std::nullopt;
        }

        return JSONParseHelper::emitUnsignedNumber(tval.value());
    }
};

class UUIDType : public IGroundedType
{
public:
    UUIDType() : IGroundedType(TypeTag::UUIDTag, "NSCore::UUID") {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j)
    {
        return new UUIDType();
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        auto uuid = JSONParseHelper::checkIsUUID(j);
        if(!uuid.has_value())
        {
            return false;
        }

        return apimgr.parseUUIDImpl(apimodule, this, uuid.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        auto uval = apimgr.extractUUIDImpl(apimodule, this, value, ctx);
        if(!uval.has_value())
        {
            return std::nullopt;
        }

        return uval;
    }
};

class ContentHashType : public IGroundedType
{
public:
    ContentHashType() : IGroundedType(TypeTag::ContentHashTag, "NSCore::ContentHash") {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j)
    {
        return new ContentHashType();
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

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        auto hash = JSONParseHelper::checkIsContentHash(j);
        if(!hash.has_value())
        {
            return false;
        }

        return apimgr.parseContentHashImpl(apimodule, this, hash.value(), value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        auto hash = apimgr.extractContentHashImpl(apimodule, this, value, ctx);
        if(!hash.has_value())
        {
            return std::nullopt;
        }

        return hash;
    }
};

class ISOTimeOfType : public IGroundedType
{
public:
    const std::optional<std::string> chkinv; 

    ISOTimeOfType(std::string name, std::optional<std::string> chkinv) : IGroundedType(TypeTag::ISOTimeOfTag, name), chkinv(chkinv) {;}
    virtual ~ISOTimeOfType() {;}

    static ISOTimeOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);
    
        return new ISOTimeOfType(name, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("ISOTime")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("ISOTime")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("ISOTime")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class LogicalTimeOfType : public IGroundedType
{
public:
    const std::optional<std::string> chkinv; 

    LogicalTimeOfType(std::string name, std::optional<std::string> chkinv) : IGroundedType(TypeTag::LogicalTimeOfTag, name), chkinv(chkinv) {;}
    virtual ~LogicalTimeOfType() {;}

    static LogicalTimeOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);
    
        return new LogicalTimeOfType(name, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("LogicalTime")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("LogicalTime")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("LogicalTime")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class UUIDOfOfType : public IGroundedType
{
public:
    const std::optional<std::string> chkinv; 

    UUIDOfOfType(std::string name, std::optional<std::string> chkinv) : IGroundedType(TypeTag::UUIDOfTag, name), chkinv(chkinv) {;}
    virtual ~UUIDOfOfType() {;}

    static UUIDOfOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);
    
        return new UUIDOfOfType(name, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("UUID")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("UUID")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("UUID")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class ContentHashOfType : public IGroundedType
{
public:
    const std::optional<std::string> chkinv; 

    ContentHashOfType(std::string name, std::optional<std::string> chkinv) : IGroundedType(TypeTag::ContentHashOfTag, name), chkinv(chkinv) {;}
    virtual ~ContentHashOfType() {;}

    static ContentHashOfType* jparse(json j)
    {
        auto name = j["name"].get<std::string>();
        auto chkinv = (j["chkinv"] != nullptr ? std::make_optional(j["chkinv"].get<std::string>()) : std::nullopt);
    
        return new ContentHashOfType(name, chkinv);
    }

    virtual json jfuzz(const APIModule* apimodule, RandGenerator& rnd) const override final
    {
        return apimodule->typemap.find("ContentHash")->second->jfuzz(apimodule, rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        bool okparse = apimodule->typemap.find("ContentHash")->second->tparse(apimgr, apimodule, j, value, ctx);
        if(!okparse)
        {
            return false;
        }

        return !this->chkinv.has_value() || apimgr.checkInvokeOk(this->chkinv.value(), value);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("ContentHash")->second->textract(apimgr, apimodule, value, ctx);
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
        std::vector<json> tj;
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            const std::string& tt = this->ttypes[i];

            auto jval = apimodule->typemap.find(tt)->second->jfuzz(apimodule, rnd);
            tj.push_back(jval);
        }

        return tj;
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        if(!j.is_array() || this->ttypes.size() != j.size())
        {
            return false;
        }

        apimgr.prepareParseTuple(this);
        for(size_t i = 0; i < this->ttypes.size(); ++i)
        {
            auto tt = apimodule->typemap.find(this->ttypes[i])->second;

            ObjModel& vval = apimgr.getValueForTupleIndex(tt, i);
            bool ok = tt->tparse(apimgr, apimodule, j[i], vval, ctx);
            if(!ok)
            {
                return false;
            }
        }
        apimgr.completeParseTuple(this, value);

        return true;
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimodule->typemap.find("ContentHash")->second->textract(apimgr, apimodule, value, ctx);
    }
};

class RecordType : public IGroundedType
{
public:
    const std::vector<std::string> props;
    const std::vector<std::string> ttypes;

    RecordType(std::string name, std::vector<std::string> props, std::vector<std::string> ttypes) : IGroundedType(name), props(props), ttypes(ttypes) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SomethingType : public IGroundedType
{
public:
    const std::string oftype;

    SomethingType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~SomethingType() {;}

    static SomethingType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class OkType : public IGroundedType
{
public:
    const std::string oftype;

    OkType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~OkType() {;}

    static OkType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ErrType : public IGroundedType
{
public:
    const std::string oftype;

    ErrType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~ErrType() {;}

    static ErrType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ListType : public IGroundedType
{
public:
    const std::string oftype;

    ListType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~ListType() {;}

    static ListType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StackType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    StackType(std::string name, std::string oftype, std::string ultype) : IGroundedType(name), oftype(oftype), ultype(ultype) {;}
    virtual ~StackType() {;}

    static StackType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};


class QueueType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    QueueType(std::string name, std::string oftype, std::string ultype) : IGroundedType(name), oftype(oftype), ultype(ultype) {;}
    virtual ~QueueType() {;}

    static QueueType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SetType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    const std::string unqchkinv;
    const std::string unqconvinv;

    SetType(std::string name, std::string oftype, std::string ultype, std::string unqchkinv, std::string unqconvinv) : IGroundedType(name), oftype(oftype), ultype(ultype), unqchkinv(unqchkinv), unqconvinv(unqconvinv) {;}
    virtual ~SetType() {;}

    static SetType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class MapType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string ultype;

    const std::string unqchkinv;

    MapType(std::string name, std::string oftype, std::string ultype, std::string unqchkinv) : IGroundedType(name), oftype(oftype), ultype(ultype), unqchkinv(unqchkinv) {;}
    virtual ~MapType() {;}

    static MapType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class EnumType : public IGroundedType
{
public:
    const std::string usinginv;
    const std::vector<std::pair<std::string, uint32_t>> enums;

    EnumType(std::string name, std::string usinginv, std::vector<std::pair<std::string, uint32_t>> enums) : IGroundedType(name), usinginv(usinginv), enums(enums) {;}
    virtual ~EnumType() {;}

    static EnumType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class EntityType : public IGroundedType
{
public:
    const std::vector<std::string> fields;
    const std::vector<std::string> ttypes;

    EntityType(std::string name, std::vector<std::string> fields, std::vector<std::string> ttypes) : IGroundedType(name), fields(fields), ttypes(ttypes) {;}
    virtual ~EntityType() {;}

    static EntityType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class UnionType : public IType
{
public:
    const std::vector<std::string> opts;

    UnionType(std::string name, std::vector<std::string> opts) : IType(name), opts(opts) {;}
    virtual ~UnionType() {;}

    static UnionType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ConceptType : public IType
{
public:
    const std::vector<std::string> opts;

    ConceptType(std::string name, std::vector<std::string> opts) : IType(name), opts(opts) {;}
    virtual ~ConceptType() {;}

    static ConceptType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

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
    const InvokeSignature* api;

    const size_t bv_width;
    const std::map<std::string, std::vector<std::pair<std::string, json>>> constants;

    APIModule(std::map<std::string, const IType*> typemap, InvokeSignature* api, size_t bv_width, std::map<std::string, std::vector<std::pair<std::string, json>>> constants)
    : typemap(typemap), api(api), bv_width(bv_width), constants(constants)
    {
        ;
    }

    ~APIModule()
    {
        for(auto iter = this->typemap.begin(); iter != this->typemap.end(); ++iter)
        {
            delete iter->second;
        }

        delete this->api;
    }

    static APIModule* jparse(json j);
};

