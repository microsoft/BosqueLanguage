

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

z3::sort getZ3SortFor(const APIModule* apimodule, const IType* tt, z3::context& c);

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

class ExtractionInfo
{
public:
    const APIModule* apimodule;
    const std::string resvar;

    ExtractionInfo(const APIModule* apimodule, std::string resvar): apimodule(apimodule), resvar(resvar) {;}

    z3::func_decl getArgContextConstructor(const z3::model& m, const char* fname, const z3::sort& ressort) const;
    z3::sort getArgContextTokenSort(const z3::model& m) const;
    z3::expr genInitialContext(const z3::model& m) const;
    z3::expr extendContext(const z3::model& m, const z3::expr& ctx, size_t i) const;

    size_t bvToCardinality(const z3::model& m, const z3::expr& bv) const;
    size_t intToCardinality(const z3::model& m, const z3::expr& iv) const;

    json evalToBool(const z3::model& m, const z3::expr& e) const;

    json evalToUnsignedNumber(const z3::model& m, const z3::expr& e) const;
    json evalToSignedNumber(const z3::model& m, const z3::expr& e) const;

    json evalToRealNumber(const z3::model& m, const z3::expr& e) const;
    json evalToDecimalNumber(const z3::model& m, const z3::expr& e) const;

    json evalToString(const z3::model& m, const z3::expr& e) const;

    z3::expr callfunc(std::string fname, const z3::expr_vector& args, const std::vector<const IType*>& argtypes, const IType* restype, z3::context& c) const;
    z3::expr callfunc(std::string fname, const z3::expr& arg, const IType* argtype, const IType* restype, z3::context& c) const;
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

    std::optional<uint64_t> parseToUnsignedNumber(json j) const;
    std::optional<int64_t> parseToSignedNumber(json j) const;

    std::optional<std::string> parseToBigUnsignedNumber(json j) const;
    std::optional<std::string> parseToBigSignedNumber(json j) const;

    std::optional<std::string> parseToRealNumber(json j) const;
    std::optional<std::string> parseToDecimalNumber(json j) const;

    z3::expr callfunc(std::string fname, const z3::expr_vector& args, const std::vector<const IType*>& argtypes, const IType* restype, z3::context& c) const;
    z3::expr callfunc(std::string fname, const z3::expr& arg, const IType* argtype, const IType* restype, z3::context& c) const;
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
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const = 0;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const = 0;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const = 0;
};

class IGroundedType : public IType
{
public:
    const std::string smttypetag;
    const std::string boxfunc;
    const std::string unboxfunc;

    IGroundedType(std::string name, bool iskey, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc): IType(name, iskey, smtname), smttypetag(smttypetag), boxfunc(boxfunc), unboxfunc(unboxfunc) {;}
    virtual ~IGroundedType() {;}
};

class NoneType : public IGroundedType
{
public:
    NoneType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::None", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class BoolType : public IGroundedType
{
public:
    BoolType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Bool", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class NatType : public IGroundedType
{
public:
    NatType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Nat", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class IntType : public IGroundedType
{
public:
    IntType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Int", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class BigNatType : public IGroundedType
{
public:
    BigNatType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::BigNat", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~BigNatType() {;}

    static BigNatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class BigIntType : public IGroundedType
{
public:
    BigIntType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::BigInt", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~BigIntType() {;}

    static BigIntType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class RationalType : public IGroundedType
{
public:
    RationalType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Rational", false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~RationalType() {;}

    static RationalType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class FloatType : public IGroundedType
{
public:
    FloatType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Float", false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~FloatType() {;}

    static FloatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class DecimalType : public IGroundedType
{
public:
    DecimalType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::Decimal", false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~DecimalType() {;}

    static DecimalType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class StringType : public IGroundedType
{
public:
    StringType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::String", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~StringType() {;}

    static StringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class StringOfType : public IGroundedType
{
public:
    const std::string validator;
    const BSQRegex* re_validate;

    StringOfType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string validator, const BSQRegex* re_validate) : IGroundedType(name, true, smtname, smttypetag, boxfunc, unboxfunc), validator(validator), re_validate(re_validate) {;}
    virtual ~StringOfType() {;}

    static StringOfType* jparse(json j);

   virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class NumberOfType : public IGroundedType
{
public:
    const std::string primitive;
    const std::string oftype; //either another numberof or a primitive

    std::optional<std::string> smtinvcall;
    std::optional<std::string> cppinvcall;

    NumberOfType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string primitive, std::string oftype, std::optional<std::string> smtinvcall, std::optional<std::string> cppinvcall) : IGroundedType(name, true, smtname, smttypetag, boxfunc, unboxfunc), primitive(primitive), oftype(oftype), smtinvcall(smtinvcall), cppinvcall(cppinvcall) {;}
    virtual ~NumberOfType() {;}

    static NumberOfType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class DataStringType : public IGroundedType
{
public:
    const std::string oftype;
    const bool isvalue;

    std::string smtinvcall;
    std::string cppinvcall;

    DataStringType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string oftype, bool isvalue, std::string smtinvcall, std::string cppinvcall) : IGroundedType(name, true, smtname, smttypetag, boxfunc, unboxfunc), oftype(oftype), isvalue(isvalue), smtinvcall(smtinvcall), cppinvcall(cppinvcall) {;}
    virtual ~DataStringType() {;}

    static DataStringType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class ByteBufferType : public IGroundedType
{
public:
    ByteBufferType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::ByteBuffer", false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~ByteBufferType() {;}

    static ByteBufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class BufferType : public IGroundedType
{
public:
    BufferType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType(name, false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~BufferType() {;}

    static BufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class DataBufferType : public IGroundedType
{
public:
    DataBufferType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType(name, false, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~DataBufferType() {;}

    static DataBufferType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class ISOTimeType : public IGroundedType
{
public:
    ISOTimeType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::ISOTime", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~ISOTimeType() {;}

    static ISOTimeType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class LogicalTimeType : public IGroundedType
{
public:
    LogicalTimeType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::LogicalTime", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~LogicalTimeType() {;}

    static LogicalTimeType* jparse(json j);

   virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class UUIDType : public IGroundedType
{
public:
    UUIDType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::UUID", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~UUIDType() {;}

    static UUIDType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class ContentHashType : public IGroundedType
{
public:
    ContentHashType(std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc) : IGroundedType("NSCore::ContentHash", true, smtname, smttypetag, boxfunc, unboxfunc) {;}
    virtual ~ContentHashType() {;}

    static ContentHashType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class TupleType : public IGroundedType
{
public:
    const std::string consfunc;
    const bool isvalue;
    const std::vector<std::string> ttypes;

    const std::vector<std::string> smtaccessors;

    TupleType(std::string name, bool iskey, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string consfunc, bool isvalue, std::vector<std::string> ttypes, std::vector<std::string> smtaccessors) : IGroundedType(name, iskey, smtname, smttypetag, boxfunc, unboxfunc), consfunc(consfunc), isvalue(isvalue), ttypes(ttypes), smtaccessors(smtaccessors) {;}
    virtual ~TupleType() {;}

    static TupleType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class RecordType : public IGroundedType
{
public:
    const std::string consfunc;
    const bool isvalue;
    const std::vector<std::string> props;
    const std::vector<std::string> ttypes;

    const std::vector<std::string> smtaccessors;

    RecordType(std::string name, bool iskey, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string consfunc, bool isvalue, std::vector<std::string> props, std::vector<std::string> ttypes, std::vector<std::string> smtaccessors) : IGroundedType(name, iskey, smtname, smttypetag, boxfunc, unboxfunc), consfunc(consfunc), isvalue(isvalue), props(props), ttypes(ttypes), smtaccessors(smtaccessors) {;}
    virtual ~RecordType() {;}

    static RecordType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class ListType : public IGroundedType
{
public:
    const std::string oftype;
    const std::vector<std::string> smtconsfunc_k;
    const std::string smtsizefunc;
    const std::string smtgetfunc;

    ListType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string oftype, std::vector<std::string> smtconsfunc_k, std::string smtsizefunc, std::string smtgetfunc) : IGroundedType(name, false, smtname, smttypetag, boxfunc, unboxfunc), oftype(oftype), smtconsfunc_k(smtconsfunc_k), smtsizefunc(smtsizefunc), smtgetfunc(smtgetfunc) {;}
    virtual ~ListType() {;}

    static ListType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class EnumType : public IGroundedType
{
public:
    const std::string underlying;
    const std::string smttagfunc;
    const std::string smtselectfunc;
    const std::vector<std::pair<std::string, std::string>> enuminvs; //map from full enum names to the invoke values

    EnumType(std::string name, std::string smtname, std::string smttypetag, std::string boxfunc, std::string unboxfunc, std::string underlying, std::string smttagfunc, std::string smtselectfunc, std::vector<std::pair<std::string, std::string>> enuminvs) : IGroundedType(name, false, smtname, smttypetag, boxfunc, unboxfunc), underlying(underlying), smttagfunc(smttagfunc), smtselectfunc(smtselectfunc), enuminvs(enuminvs) {;}
    virtual ~EnumType() {;}

    static EnumType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class UnionType : public IType
{
public:
    const std::vector<std::string> opts;
    const std::string smttypefunc;
    const std::string smtunboxfunc;

    UnionType(std::string name, bool iskey, std::string smtname, std::vector<std::string> opts, std::string smttypefunc, std::string smtunboxfunc) : IType(name, iskey, smtname), opts(opts), smttypefunc(smttypefunc), smtunboxfunc(smtunboxfunc) {;}
    virtual ~UnionType() {;}

    static UnionType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;

    virtual std::optional<z3::expr> toz3arg(ParseInfo& pinfo, json j, z3::context& c) const override final;
    virtual std::optional<std::string> tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const override final;

    virtual json argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const override final;
    virtual json resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const override final;
};

class InvokeSignature
{
public:
    const std::string name;
    const IType* resType;
    const std::vector<std::string> argnames;
    const std::vector<std::string> smtargnames;
    const std::vector<const IType*> argtypes;
    
    InvokeSignature(std::string name, const IType* resType, std::vector<std::string> argnames, std::vector<std::string> smtargnames, std::vector<const IType*> argtypes): name(name), resType(resType), argnames(argnames), smtargnames(smtargnames), argtypes(argtypes) {;}

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
