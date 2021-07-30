

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
    NumberOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag,
    TupleTag,
    RecordTag,
    ListTag,
    EnumTag,
    UnionTag
};

struct NumericFuzzLimits
{
    uint16_t nat_max;
    int16_t int_min;
    int16_t int_max;

    double float_min;
    double float_max;
    double decimal_min;
    double decimal_max;

    uint64_t iso_time_min;
    uint64_t iso_time_max;
    uint16_t ltime_max;

    uint16_t re_repeat_max;
    uint16_t strlen_max;
    uint16_t container_max;
};

class FuzzInfo
{
public:
    const APIModule* apimodule;
    const NumericFuzzLimits limits;

    std::map<std::string, std::vector<std::pair<std::string, json>>> reuse;

    bool hasConstantsForType(std::string tag) const;
    json pickConstantForType(std::string tag, RandGenerator& rnd) const;

    bool hasReuseForType(std::string tag) const;
    void addReuseForType(std::string tag, json j);
    json pickReuseForType(std::string tag, RandGenerator& rnd) const;

    bool sampleKnownOpt(std::string tag, RandGenerator& rnd, json& j);

    FuzzInfo(const APIModule* apimodule, NumericFuzzLimits limits) : limits(limits) {;}
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

////
//Regex

enum class SpecialCharKind 
{
    Wildcard = 0x0,
    WhiteSpace
};

class BSQRegexOpt
{
public:
    BSQRegexOpt() {;}
    virtual ~BSQRegexOpt() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const = 0;

    static BSQRegexOpt* parse(json j);
};

class BSQLiteralRe : public BSQRegexOpt
{
public:
    const std::string restr;
    const std::string escstr;
    const std::vector<uint8_t> litstr;

    BSQLiteralRe(std::string restr, std::string escstr, std::vector<uint8_t> litstr) : BSQRegexOpt(), restr(restr), escstr(escstr), litstr(litstr) {;}
    virtual ~BSQLiteralRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQLiteralRe* parse(json j);
};

class BSQCharRangeRe : public BSQRegexOpt
{
public:
    const uint64_t low;
    const uint64_t high;

    BSQCharRangeRe(uint64_t low, uint64_t high) : BSQRegexOpt(), low(low), high(high) {;}
    virtual ~BSQCharRangeRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQCharRangeRe* parse(json j);
};

class BSQCharClassRe : public BSQRegexOpt
{
public:
    const SpecialCharKind kind;

    BSQCharClassRe(SpecialCharKind kind) : BSQRegexOpt(), kind(kind) {;}
    virtual ~BSQCharClassRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQCharClassRe* parse(json j);
};

class BSQStarRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQStarRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQStarRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQStarRepeatRe* parse(json j);
};

class BSQPlusRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQPlusRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQPlusRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQPlusRepeatRe* parse(json j);
};

class BSQRangeRepeatRe : public BSQRegexOpt
{
public:
    const uint32_t low;
    const uint32_t high;
    const BSQRegexOpt* opt;

    BSQRangeRepeatRe(uint32_t low, uint32_t high, const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt), low(low), high(high) {;}
    virtual ~BSQRangeRepeatRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQRangeRepeatRe* parse(json j);
};

class BSQOptionalRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQOptionalRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQOptionalRe* parse(json j);
};

class BSQAlternationRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQAlternationRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQAlternationRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQAlternationRe* parse(json j);
};

class BSQSequenceRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQSequenceRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQSequenceRe() {;}

    virtual std::string generate(RandGenerator& rnd, FuzzInfo& finfo) const override final;

    static BSQSequenceRe* parse(json j);
};

class BSQRegex
{
public:
    const std::string restr;
    const BSQRegexOpt* re;

    BSQRegex(std::string restr, const BSQRegexOpt* re): restr(restr), re(re) {;}
    ~BSQRegex() {;}

    std::string generate(RandGenerator& rnd, FuzzInfo& finfo);

    static BSQRegex* parse(json j);
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const = 0;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class StringOfType : public IGroundedType
{
public:
    const std::string validator;
    const BSQRegex* re_validate;

    StringOfType(std::string name, std::string validator, const BSQRegex* re_validate) : IGroundedType(name), validator(validator), re_validate(re_validate) {;}
    virtual ~StringOfType() {;}

    static StringOfType* jparse(json j);

   virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class NumberOfType : public IGroundedType
{
public:
    const std::string primitive;
    const std::string oftype; //either another numberof or a primitive

    NumberOfType(std::string name, std::string primitive, std::string oftype) : IGroundedType(name), primitive(primitive), oftype(oftype) {;}
    virtual ~NumberOfType() {;}

    static NumberOfType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;
    const bool isvalue;

    DataStringType(std::string name, std::string oftype, bool isvalue) : IGroundedType(name), oftype(oftype), isvalue(isvalue) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class BufferType : public IGroundedType
{
public:
    BufferType(std::string name) : IGroundedType(name) {;}
    virtual ~BufferType() {;}

    static BufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

   virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class TupleType : public IGroundedType
{
public:
    const bool isvalue;
    const std::vector<std::string> ttypes;

    TupleType(std::string name, bool isvalue, std::vector<std::string> ttypes) : IGroundedType(name), isvalue(isvalue), ttypes(ttypes) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual bool toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual std::optional<json> z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const override final;
};

class RecordType : public IGroundedType
{
public:
    const bool isvalue;
    const std::vector<std::string> props;
    const std::vector<std::string> ttypes;

    RecordType(std::string name, bool isvalue, std::vector<std::string> props, std::vector<std::string> ttypes) : IGroundedType(name), isvalue(isvalue), props(props), ttypes(ttypes) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

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
