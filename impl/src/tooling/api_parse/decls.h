
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <chrono>
#include <cstdio>

#include <string>
#include <regex>

#include <optional>
#include <vector>
#include <stack>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "json.hpp"
typedef nlohmann::json json;

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
    BufferOfTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag,
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
    virtual bool parseNoneImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseNothingImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBoolImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseNatImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseIntImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBigNatImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBigIntImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseFloatImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseDecimalImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseRationalImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseStringImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseStringOfImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parsePrimitiveOfImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseDataStringImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseByteBufferImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseBufferOfImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseDataBufferImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseISOTimeImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseUUIDImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    virtual bool parseContentHashImpl(const APIModule* apimodule, const IType* itype, json j, ObjModel& value, ParseContext& ctx) const = 0;
    
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

    virtual std::optional<json> extractNoneImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractNothingImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractBoolImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractNatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractIntImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractBigNatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractBigIntImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractFloatImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractDecimalImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractRationalImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractStringImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractStringOfImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractPrimitiveOfImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractDataStringImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractBufferOfImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractDataBufferImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractISOTimeImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractUUIDImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    virtual std::optional<json> extractContentHashImpl(const APIModule* apimodule, const IType* itype, ObjModel& value, ExtractContext& ctx) const = 0;
    
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
};

class IType
{
public:
    const TypeTag tag;
    const std::string name;

    IType(TypeTag tag, std::string name) : tag(tag), name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json jfuzz(RandGenerator& rnd) const = 0;
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

    virtual json jfuzz(RandGenerator& rnd) const override final
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
        
        return apimgr.parseNoneImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractNoneImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
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
        
        return apimgr.parseNothingImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractNothingImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
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
        
        return apimgr.parseBoolImpl(apimodule, this, j, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 32);
        return ngen(rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<uint64_t> nval = JSONParseHelper::parseToUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseNatImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractNatImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> igen(-32, 32);
        return igen(rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<int64_t> nval = JSONParseHelper::parseToSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseIntImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractIntImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<uint64_t> ngen(0, 128);
        return ngen(rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper.parseToBigUnsignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigNatImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractBigNatImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> igen(-128, 128);
        return igen(rnd);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::string> nval = JSONParseHelper.parseToBigSignedNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseBigIntImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractBigIntImpl(apimodule, this, value, ctx);
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

    virtual json jfuzz(RandGenerator& rnd) const override final
    {
        std::uniform_int_distribution<int64_t> ngen(-128, 128);
        std::uniform_int_distribution<uint64_t> dgen(1, 32);
        
        return std::to_string(ngen(rnd)) + "/" + std::to_string(dgen(rnd));
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    bool parse(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, json j, ObjModel& value, ParseContext& ctx) const
    {
        std::optional<std::pair<std::string, uint64_t>> nval = JSONParseHelper::parseToRationalNumber(j);
        if(!nval.has_value())
        {
            return false;
        }
        
        return apimgr.parseRationalImpl(apimodule, this, j, value, ctx);
    }

    template <typename ObjModel, typename ParseContext, typename ExtractContext>
    std::optional<json> extract(const ApiManagerJSON<ObjModel, ParseContext, ExtractContext>& apimgr, const APIModule* apimodule, ObjModel& value, ExtractContext& ctx) const
    {
        return apimgr.extractRationalImpl(apimodule, this, value, ctx);
    }
};

class FloatType : public IGroundedType
{
public:
    FloatType() : IGroundedType("NSCore::Float") {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DecimalType : public IGroundedType
{
public:
    DecimalType() : IGroundedType("NSCore::Decimal") {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringType : public IGroundedType
{
public:
    StringType() : IGroundedType("NSCore::String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class PrimitiveOfType : public IGroundedType
{
public:
    const std::string oftype;
    const std::string usinginv; //may be sentinal "[NO CONSTRUCTOR]"

    PrimitiveOfType(std::string name, std::string oftype, std::string usinginv) : IGroundedType(name), oftype(oftype), usinginv(usinginv) {;}
    virtual ~PrimitiveOfType() {;}

    static PrimitiveOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringOfType : public IGroundedType
{
public:
    const std::string validator;

    StringOfType(std::string name, std::string validator) : IGroundedType(name), validator(validator) {;}
    virtual ~StringOfType() {;}

    static StringOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;

    DataStringType(std::string name, std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType() : IGroundedType("NSCore::ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BufferOfType : public IGroundedType
{
public:
    BufferOfType(std::string name) : IGroundedType(name) {;}
    virtual ~BufferOfType() {;}

    static BufferOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataBufferType : public IGroundedType
{
public:
    DataBufferType(std::string name) : IGroundedType(name) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ISOTimeType : public IGroundedType
{
public:
    ISOTimeType() : IGroundedType("NSCore::ISOTime") {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType() : IGroundedType("NSCore::LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j,const z3::expr& ctx,  z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class UUIDType : public IGroundedType
{
public:
    UUIDType() : IGroundedType("NSCore::UUID") {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ContentHashType : public IGroundedType
{
public:
    ContentHashType() : IGroundedType("NSCore::ContentHash") {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class TupleType : public IGroundedType
{
public:
    const std::vector<std::string> ttypes;

    TupleType(std::string name, std::vector<std::string> ttypes) : IGroundedType(name), ttypes(ttypes) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
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

