

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>

#include <optional>
#include <vector>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "json.hpp"
#include "z3++.h"

typedef nlohmann::json json;

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
    uint64_t nat_max;
    int64_t int_min;
    int64_t int_max;
};

class FuzzInfo
{
public:
    const bool small_model_gen;
    const NumericLimits limits;

    std::map<TypeTag, std::vector<std::pair<std::string, json>>> constants;
    std::map<TypeTag, std::vector<std::pair<std::string, json>>> reuse;

    bool hasConstantsForType(TypeTag tag) const;
    void addConstantForType(TypeTag tag, json j);
    json pickConstantForType(TypeTag tag, RandGenerator& rnd) const;

    bool hasReuseForType(TypeTag tag) const;
    void addReuseForType(TypeTag tag, json j);
    json pickReuseForType(TypeTag tag, RandGenerator& rnd) const;

    bool sampleKnownOpt(TypeTag tag, RandGenerator& rnd, json& j);

    FuzzInfo(bool small, NumericLimits limits) : small_model_gen(small), limits(limits) {;}
};

class ExtractionInfo
{
private:
    static void loadConsFuncs(std::map<std::string, std::optional<z3::func_decl>>& consfuncs);

public:
    z3::context* c;
    z3::model* m;
    std::map<std::string, std::optional<z3::func_decl>> consfuncs;

    ExtractionInfo(z3::context* c, z3::model* m) : c(c), m(m)
    {
        ExtractionInfo::loadConsFuncs(this->consfuncs);
    }

    z3::expr evalConsFunc(const char* cf, z3::expr ctx)
    {
        auto valexp = this->consfuncs[cf].value()(ctx);
        auto resexp = this->m->eval(valexp, true);

        return resexp;
    }

    z3::expr advanceCtx(z3::expr ctx)
    {
        z3::concat(ctx, this->consfuncs["MakeStep"].value()(this->c->bv_val(0, 5)));
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

struct BSQRegex
{
    std::string restr;
    bool isAnchorStart;
    bool isAnchorEnd;
    BSQRegexOpt* re;

    std::string generate(RandGenerator& rnd, FuzzInfo& finfo)
    {
        return this->re->generate(rnd, finfo);
    }  
};

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    static IType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const = 0;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const = 0;

    virtual std::string consprint(json j) const = 0;
};

class NoneType : public IType
{
public:
    NoneType() : IType("NSCore::None") {;}
    virtual ~NoneType() {;}

    static NoneType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class BoolType : public IType
{
public:
    BoolType() : IType("NSCore::Bool") {;}
    virtual ~BoolType() {;}

    static BoolType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class NatType : public IType
{
public:
    NatType() : IType("NSCore::Nat") {;}
    virtual ~NatType() {;}

    static NatType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class IntType : public IType
{
public:
    IntType() : IType("NSCore::Int") {;}
    virtual ~IntType() {;}

    static IntType* jparse(json j);

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class BigNatType : public IType
{
public:
    BigNatType() : IType("NSCore::BigNat") {;}
    virtual ~BigNatType() {;}

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class BigIntType : public IType
{
public:
    BigIntType() : IType("NSCore::BigInt") {;}
    virtual ~BigIntType() {;}

    virtual json fuzz(FuzzInfo& finfo, RandGenerator& rnd) const override final;
    virtual json extract(ExtractionInfo* ex, z3::expr ctx) const override final;

    virtual std::string consprint(json j) const override final;
};

class RationalType : public IType
{

};

class FloatType : public IType
{

};

class DecimalType : public IType
{

};

class StringType : public IType
{

};

class StringOfType : public IType
{

};

class NumberOfType : public IType
{

};

class DataStringType : public IType
{

};

class ByteBufferType : public IType
{

};

class BufferType : public IType
{

};

class DataBufferType : public IType
{

};

class ISOType : public IType
{

};

class LogicalType : public IType
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
