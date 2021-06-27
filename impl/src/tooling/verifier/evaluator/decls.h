

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <chrono>

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
    ContentHashTag
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


class ConvInfo
{
public:
    const APIModule* apimodule;

    const std::regex re_numberinon;
    const std::regex re_numberinoi;
    const std::regex re_numberinof;

    ConvInfo(const APIModule* apimodule) : apimodule(apimodule) {;}
};

class FuzzInfo
{
public:
    const APIModule* apimodule;
    const NumericFuzzLimits limits;

    std::map<std::string, std::vector<std::pair<std::string, json>>> reuse;

    bool hasConstantsForType(std::string tag) const;
    void addConstantForType(std::string tag, json j);
    json pickConstantForType(std::string tag, RandGenerator& rnd) const;

    bool hasReuseForType(std::string tag) const;
    void addReuseForType(std::string tag, json j);
    json pickReuseForType(std::string tag, RandGenerator& rnd) const;

    bool sampleKnownOpt(std::string tag, RandGenerator& rnd, json& j);

    FuzzInfo(const APIModule* apimodule, NumericFuzzLimits limits) : limits(limits) {;}
};

class ExtractionInfo
{
public:
    const APIModule* apimodule;

    ExtractionInfo(const APIModule* apimodule): apimodule(apimodule) {;}

    z3::func_decl getArgContextConstructor(const z3::model& m, const char* fname, const z3::sort& ressort) const;
    z3::sort getArgContextTokenSort(const z3::model& m) const;

    size_t bvToCardinality(const z3::expr& bv) const;

    json evalToBool(const z3::model& m, const z3::expr& e) const;
    json evalToUnsignedNumber(const z3::model& m, const z3::expr& e) const;
    json evalToSignedNumber(const z3::model& m, const z3::expr& e) const;
};

class ParseInfo
{
public:
    const APIModule* apimodule;
    z3::expr_vector chks;

    const std::regex re_numberinon;
    const std::regex re_numberinoi;
    const std::regex re_numberinof;

    ParseInfo(const APIModule* apimodule, z3::expr_vector chks): apimodule(apimodule), chks(chks),
    re_numberinon("^(+)?(0|[1-9][0-9]*)$"), re_numberinoi("^(+|-)?(0|[1-9][0-9]*)$"), re_numberinof("^(+|-)?(0|[1-9][0-9]*)|([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$")
    {
        ;
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

class IType
{
public:
    const std::string name;

    const bool iskey;
    const std::string smtname;

    IType(std::string name, bool iskey, std::string smtname) : name(name), iskey(iskey), smtname(smtname) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const = 0;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const = 0;
    virtual std::optional<std::string> tobsqarg(const ConvInfo& cinfo, json j) const = 0;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const = 0;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const = 0;
};

class IGroundedType : public IType
{
public:
    const std::string boxfunc;

    IGroundedType(std::string name, bool iskey, std::string smtname, std::string boxfunc): IType(name, iskey, smtname), boxfunc(boxfunc) {;}
    virtual ~IGroundedType() {;}
};

class NoneType : public IGroundedType
{
public:
    NoneType(std::string smtname, std::string boxfunc) : IGroundedType("NSCore::None", true, smtname, boxfunc) {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const;
    virtual std::optional<std::string> tobsqarg(const ConvInfo& cinfo, json j) const;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const;
};

class BoolType : public IGroundedType
{
public:
    BoolType(std::string smtname, std::string boxfunc) : IGroundedType("NSCore::Bool", true, smtname, boxfunc) {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const;
    virtual std::optional<std::string> tobsqarg(const ConvInfo& cinfo, json j) const;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const;
};

class NatType : public IType
{
public:
    NatType() : IType("NSCore::Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class NumberOfType : public IType
{
public:
    const std::string primitive;
    const std::string oftype; //either another numberof or a primitive

    std::optional<std::string> smtinvcall;
    std::optional<std::string> cppinvcall;

    NumberOfType(std::string name, std::string primitive, std::string oftype, std::optional<std::string> smtinvcall, std::optional<std::string> cppinvcall) : IType(name), primitive(primitive), oftype(oftype), smtinvcall(smtinvcall), cppinvcall(cppinvcall) {;}
    virtual ~NumberOfType() {;}

    static NumberOfType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class DataStringType : public IType
{
public:
    const std::string oftype;
    const bool isvalue;

    std::string smtinvcall;
    std::string cppinvcall;

    DataStringType(std::string name, std::string oftype, bool isvalue, std::string smtinvcall, std::string cppinvcall) : IType(name), oftype(oftype), isvalue(isvalue), smtinvcall(smtinvcall), cppinvcall(cppinvcall) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
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

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class ISOTimeType : public IType
{
public:
    ISOTimeType() : IType("NSCore::ISOTime") {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class LogicalTimeType : public IType
{
public:
    LogicalTimeType() : IType("NSCore::LogicalTime") {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class UUIDType : public IType
{
public:
    UUIDType() : IType("NSCore::UUID") {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class ContentHashType : public IType
{
public:
    ContentHashType() : IType("NSCore::ContentHash") {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class TupleType : public IType
{
public:
    const bool isvalue;
    const std::vector<std::string> ttypes;

    TupleType(std::string name, bool isvalue, std::vector<std::string> ttypes) : IType(name), isvalue(isvalue), ttypes(ttypes) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class RecordType : public IType
{
public:
    const bool isvalue;
    const std::vector<std::pair<std::string, std::string>> entries;

    RecordType(std::string name, bool isvalue, std::vector<std::pair<std::string, std::string>> entries) : IType(name), isvalue(isvalue), entries(entries) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class ListType : public IType
{
public:
    const std::string oftype;

    ListType(std::string name, std::string oftype) : IType(name), oftype(oftype) {;}
    virtual ~ListType() {;}

    static ListType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class UnionType : public IType
{
public:
    const bool iskey;
    const std::vector<std::string> opts;

    UnionType(std::string name, bool iskey, std::vector<std::string> opts) : IType(name), iskey(iskey), opts(opts) {;}
    virtual ~UnionType() {;}

    static UnionType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, const z3::expr& ctx) const override final;

    virtual std::optional<std::string> consprint(const ConvInfo& cinfo, json j) const override final;
    virtual std::optional<z3::expr> parseJSON(ParseInfo* pinfo, json j) const override final;
};

class InvokeSignature
{
public:
    const std::string name;
    const IType* resType;
    const std::vector<const IType*> argTypes;

    InvokeSignature(std::string name, const IType* resType, std::vector<const IType*> argTypes): name(name), resType(resType), argTypes(argTypes) {;}
};

class APIModule
{
public:
    const std::map<std::string, const IType*> typemap;
    const std::vector<InvokeSignature*> siglist;

    const size_t bv_width;

    const std::map<std::string, std::vector<std::pair<std::string, json>>> constants;

    APIModule(std::map<std::string, const IType*> typemap, std::vector<InvokeSignature*> siglist, size_t bv_width, std::map<std::string, std::vector<std::pair<std::string, json>>> constants)
    : typemap(typemap), siglist(siglist), bv_width(bv_width), constants(constants)
    {
        ;
    }

    ~APIModule()
    {
        for(auto iter = this->typemap.begin(); iter != this->typemap.end(); ++iter)
        {
            delete iter->second;
        }

        for(auto iter = this->siglist.begin(); iter != this->siglist.end(); ++iter)
        {
            delete *iter;
        }
    }
};
