

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
#include "z3++.h"

typedef nlohmann::json json;

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
    UnionTag
};

z3::func_decl getArgContextConstructor(const APIModule* apimodule, z3::context& c, const char* fname, const z3::sort& ressort);
z3::expr genInitialContextArg(const APIModule* apimodule, z3::context& c);
z3::expr genInitialContextResult(const APIModule* apimodule, z3::context& c);
z3::expr extendContext(const APIModule* apimodule, z3::context& c, const z3::expr& ctx, size_t i);

class ExtractionInfo
{
public:
    const APIModule* apimodule;

    ExtractionInfo(const APIModule* apimodule): apimodule(apimodule) {;}

    std::optional<bool> expBoolAsBool(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<uint64_t> expBVAsUInt(z3::solver& s, z3::model& m, const z3::expr& e) const;
    std::optional<int64_t> expBVAsInt(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<std::string> expIntAsUInt(z3::solver& s, z3::model& m, const z3::expr& e) const;
    std::optional<std::string> expIntAsInt(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<std::string> evalRealAsFP(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<std::string> evalStringAsString(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<size_t> bvToCardinality(z3::solver& s, z3::model& m, const z3::expr& bv) const;
    std::optional<size_t> intToCardinality(z3::solver& s, z3::model& m, const z3::expr& iv) const;

    std::optional<json> evalToBool(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<json> evalToUnsignedNumber(z3::solver& s, z3::model& m, const z3::expr& e) const;
    std::optional<json> evalToSignedNumber(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<json> evalToRealNumber(z3::solver& s, z3::model& m, const z3::expr& e) const;
    std::optional<json> evalToDecimalNumber(z3::solver& s, z3::model& m, const z3::expr& e) const;

    std::optional<json> evalToString(z3::solver& s, z3::model& m, const z3::expr& e) const;
};

class ParseInfo
{
public:
    const APIModule* apimodule;
    std::stack<z3::expr_vector*> chks;

    ParseInfo(const APIModule* apimodule, z3::expr_vector* topv): apimodule(apimodule), chks()
    {
        chks.push(topv);
    }

    std::optional<uint64_t> parseToUnsignedNumber(json j) const;
    std::optional<int64_t> parseToSignedNumber(json j) const;

    std::optional<std::string> parseToBigUnsignedNumber(json j) const;
    std::optional<std::string> parseToBigSignedNumber(json j) const;

    std::optional<std::string> parseToRealNumber(json j) const;
    std::optional<std::string> parseToDecimalNumber(json j) const;
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const = 0;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const = 0;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const = 0;
};

class IGroundedType : public IType
{
public:
    IGroundedType(std::string name): IType(name) {;}
    virtual ~IGroundedType() {;}
};

class NoneType : public IGroundedType
{
public:
    NoneType() : IGroundedType("NSCore::None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class NothingType : public IGroundedType
{
public:
    NothingType() : IGroundedType("NSCore::Nothing") {;}
    virtual ~NothingType() {;}

    static NothingType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BoolType : public IGroundedType
{
public:
    BoolType() : IGroundedType("NSCore::Bool") {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class NatType : public IGroundedType
{
public:
    NatType() : IGroundedType("NSCore::Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class IntType : public IGroundedType
{
public:
    IntType() : IGroundedType("NSCore::Int") {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BigNatType : public IGroundedType
{
public:
    BigNatType() : IGroundedType("NSCore::BigNat") {;}
    virtual ~BigNatType() {;}

    static BigNatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BigIntType : public IGroundedType
{
public:
    BigIntType() : IGroundedType("NSCore::BigInt") {;}
    virtual ~BigIntType() {;}

    static BigIntType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class RationalType : public IGroundedType
{
public:
    RationalType() : IGroundedType("NSCore::Rational") {;}
    virtual ~RationalType() {;}

    static RationalType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class FloatType : public IGroundedType
{
public:
    FloatType() : IGroundedType("NSCore::Float") {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DecimalType : public IGroundedType
{
public:
    DecimalType() : IGroundedType("NSCore::Decimal") {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringType : public IGroundedType
{
public:
    StringType() : IGroundedType("NSCore::String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class PrimitiveOfType : public IGroundedType
{
public:
    const std::string oftype;

    PrimitiveOfType(std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~PrimitiveOfType() {;}

    static PrimitiveOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType() : IGroundedType("NSCore::ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BufferOfType : public IGroundedType
{
public:
    BufferOfType(std::string name) : IGroundedType(name) {;}
    virtual ~BufferOfType() {;}

    static BufferOfType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataBufferType : public IGroundedType
{
public:
    DataBufferType(std::string name) : IGroundedType(name) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ISOTimeType : public IGroundedType
{
public:
    ISOTimeType() : IGroundedType("NSCore::ISOTime") {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType() : IGroundedType("NSCore::LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j,const z3::expr& ctx,  z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class UUIDType : public IGroundedType
{
public:
    UUIDType() : IGroundedType("NSCore::UUID") {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ContentHashType : public IGroundedType
{
public:
    ContentHashType() : IGroundedType("NSCore::ContentHash") {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SomethingType : public IGroundedType
{
public:
    const std::string oftype;

    SomethingType(std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~SomethingType() {;}

    static SomethingType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class OkType : public IGroundedType
{
public:
    const std::string oftype;

    OkType(std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~OkType() {;}

    static OkType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class ErrType : public IGroundedType
{
public:
    const std::string oftype;

    ErrType(std::string oftype) : IGroundedType(name), oftype(oftype) {;}
    virtual ~ErrType() {;}

    static ErrType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StackType : public IGroundedType
{
public:
    const std::string ultype;

    StackType(std::string name, std::string ultype) : IGroundedType(name), ultype(ultype) {;}
    virtual ~StackType() {;}

    static StackType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};


class QueueType : public IGroundedType
{
public:
    const std::string ultype;

    QueueType(std::string name, std::string ultype) : IGroundedType(name), ultype(ultype) {;}
    virtual ~QueueType() {;}

    static QueueType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class SetType : public IGroundedType
{
public:
    const std::string ultype;

    SetType(std::string name, std::string ultype) : IGroundedType(name), ultype(ultype) {;}
    virtual ~SetType() {;}

    static SetType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};


class MapType : public IGroundedType
{
public:
    const std::string ultype;

    MapType(std::string name, std::string ultype) : IGroundedType(name), ultype(ultype) {;}
    virtual ~MapType() {;}

    static MapType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class EnumType : public IGroundedType
{
public:
    const std::string underlying;
    const std::vector<std::string> enuminvs; //list of full enum names

    EnumType(std::string name, std::string underlying, std::vector<std::string> enuminvs) : IGroundedType(name), underlying(underlying), enuminvs(enuminvs) {;}
    virtual ~EnumType() {;}

    static EnumType* jparse(json j);

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

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
