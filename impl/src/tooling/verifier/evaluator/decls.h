

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>
#include <regex>

#include <optional>
#include <vector>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "json.hpp"
#include "z3++.h"

typedef nlohmann::json json;

class IType;

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
    ContentHashTag
};

struct NumericLimits
{
    uint16_t nat_max;
    int16_t int_min;
    int16_t int_max;

    double float_min;
    double float_max;
    double decimal_min;
    double decimal_max;

    uint16_t re_repeat_max;
    uint16_t strlen_max;
    uint16_t container_max;
};

class FuzzInfo
{
public:
    const NumericLimits limits;
    const std::map<std::string, const IType*> typemap;

    std::map<std::string, std::vector<std::pair<std::string, json>>> constants;
    std::map<std::string, std::vector<std::pair<std::string, json>>> reuse;

    bool hasConstantsForType(std::string tag) const;
    void addConstantForType(std::string tag, json j);
    json pickConstantForType(std::string tag, RandGenerator& rnd) const;

    bool hasReuseForType(std::string tag) const;
    void addReuseForType(std::string tag, json j);
    json pickReuseForType(std::string tag, RandGenerator& rnd) const;

    bool sampleKnownOpt(std::string tag, RandGenerator& rnd, json& j);

    FuzzInfo(NumericLimits limits, std::map<std::string, const IType*> typemap) : limits(limits), typemap(typemap) {;}
};

class ExtractionInfo
{
private:
    void loadFuncs();

public:
    z3::context* c;
    z3::model* m;
    std::map<std::string, std::optional<z3::func_decl>> consfuncs;
    std::map<std::string, std::optional<z3::func_decl>> succfuncs;

    ExtractionInfo(z3::context* c, z3::model* m) : c(c), m(m)
    {
        this->loadFuncs();
    }

    z3::expr evalConsFunc(const std::string& tname, const z3::expr& ctx)
    {
        auto valexp = this->consfuncs[tname].value()(ctx);
        auto resexp = this->m->eval(valexp, true);

        return resexp;
    }

    z3::expr advanceCtx(const z3::expr& ctx)
    {
        return z3::concat(ctx, this->consfuncs["MakeStep"].value()(this->c->bv_val(0, 5)));
    }

    z3::expr evalResultSuccess(const std::string& tname, const z3::expr& exp)
    {
        return this->succfuncs[tname].value()(exp);
    }

    json bvToNatJSON(const z3::expr& bv) const;
    json bvToIntJSON(const z3::expr& bv) const;

    json intToBigNatJSON(const z3::expr& iv) const;
    json intToBigIntJSON(const z3::expr& iv) const;

    json realToRationalJSON(const z3::expr& iv) const;
    json realToFloatJSON(const z3::expr& iv) const;
    json realToDecimalJSON(const z3::expr& iv) const;
};

class ConvInfo
{
public:
    const std::map<std::string, const IType*> typemap;

    ConvInfo(std::map<std::string, const IType*> typemap) : typemap(typemap) {;}
};

class ParseInfo
{
private:
    void loadFuncs();

public:
    const std::map<std::string, const IType*> typemap;

    const size_t bv_width;

    std::optional<z3::expr> const_none;
    z3::context* c;

    const std::regex re_numberinon;
    const std::regex re_numberinoi;
    const std::regex re_numberinof;

    ParseInfo(std::map<std::string, const IType*> typemap, size_t bv_width, z3::context* c) 
    : typemap(typemap), bv_width(bv_width), c(c), 
    re_numberinon("^(+)?(0|[1-9][0-9]*)$"), re_numberinoi("^(+|-)?(0|[1-9][0-9]*)$"), re_numberinof("^(+|-)?(0|[1-9][0-9]*)|([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$")
    {
        this->loadFuncs();
    }
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
    const std::string litval;

    BSQLiteralRe(std::string lv) : BSQRegexOpt(), litval(lv) {;}
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
    const std::regex re_exec;
    const BSQRegexOpt* re;

    BSQRegex(std::string restr, const BSQRegexOpt* re): restr(restr), re_exec(restr), re(re) {;}
    ~BSQRegex() {;}

    std::string generate(RandGenerator& rnd, FuzzInfo& finfo);

    static BSQRegex* parse(json j);
};

struct ParseExprs
{
    std::optional<z3::expr> value;
    std::optional<z3::expr> chks;
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const = 0;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const = 0;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const = 0;
    virtual ParseExprs parseJSON(ParseInfo* pinfo, json j) const = 0;
};

class NoneType : public IType
{
public:
    NoneType() : IType("NSCore::None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class BoolType : public IType
{
public:
    BoolType() : IType("NSCore::Bool") {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class NatType : public IType
{
public:
    NatType() : IType("NSCore::Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class IntType : public IType
{
public:
    IntType() : IType("NSCore::Int") {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class BigNatType : public IType
{
public:
    BigNatType() : IType("NSCore::BigNat") {;}
    virtual ~BigNatType() {;}

    static BigNatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class BigIntType : public IType
{
public:
    BigIntType() : IType("NSCore::BigInt") {;}
    virtual ~BigIntType() {;}

    static BigIntType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class RationalType : public IType
{
public:
    RationalType() : IType("NSCore::Rational") {;}
    virtual ~RationalType() {;}

    static RationalType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class FloatType : public IType
{
public:
    FloatType() : IType("NSCore::Float") {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class DecimalType : public IType
{
public:
    DecimalType() : IType("NSCore::Decimal") {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class StringType : public IType
{
public:
    StringType() : IType("NSCore::String") {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class StringOfType : public IType
{
public:
    const std::string validator;
    const BSQRegex* re_validate;

    StringOfType(std::string name, std::string validator, const BSQRegex* re_validate) : IType(name), validator(validator), re_validate(re_validate) {;}
    virtual ~StringOfType() {;}

    static StringOfType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class NumberOfType : public IType
{
public:
    const std::string primitive;
    const std::string oftype; //either another numberof or a primitive

    NumberOfType(std::string name, std::string primitive, std::string oftype) : IType(name), primitive(primitive), oftype(oftype) {;}
    virtual ~NumberOfType() {;}

    static NumberOfType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class DataStringType : public IType
{
public:
    const std::string oftype;
    const bool isvalue;

    DataStringType(std::string name, std::string oftype, bool isvalue) : IType(name), oftype(oftype), isvalue(isvalue) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class ByteBufferType : public IType
{
public:
    ByteBufferType() : IType("NSCore::ByteBuffer") {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class BufferType : public IType
{
public:
    BufferType(std::string name) : IType(name) {;}
    virtual ~BufferType() {;}

    static BufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class DataBufferType : public IType
{
public:
    DataBufferType(std::string name) : IType(name) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::string consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class ISOTimeType : public IType
{

};

class LogicalTimeType : public IType
{

};

class UUIDType : public IType
{

};

class ContentHashType : public IType
{

};

class RecordType : public IType
{

};

class TupleType : public IType
{

};

class ListType : public IType
{

};

class InvokeSignature
{

};

////
// ------ Need to add in the signature thing
////
