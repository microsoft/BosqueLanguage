//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

void ExtractionInfo::loadFuncs()
{
    xxx;
}

size_t ExtractionInfo::bvToNumber(const z3::expr& bv) const
{
    xxxx;
}

json ExtractionInfo::bvToNatJSON(const z3::expr& bv) const
{
    xxxx;
}

json ExtractionInfo::bvToIntJSON(const z3::expr& bv) const
{
    xxxx;
}

json ExtractionInfo::intToBigNatJSON(const z3::expr& iv) const
{
    xxxx;
}

json ExtractionInfo::intToBigIntJSON(const z3::expr& iv) const
{
    xxxx;
}

json ExtractionInfo::realToRationalJSON(const z3::expr& iv) const
{
    xxxx;
}

json ExtractionInfo::realToFloatJSON(const z3::expr& iv) const
{
    xxxx;
}

json ExtractionInfo::realToDecimalJSON(const z3::expr& iv) const
{
    xxxx;
}

json ExtractionInfo::intToLogicalTimeJSON(const z3::expr& iv) const
{
    xxxx;
}

void ParseInfo::loadFuncs()
{
    xxxx;
}

bool FuzzInfo::hasConstantsForType(std::string tag) const
{
    return this->constants.find(tag) != this->constants.cend();
}

void FuzzInfo::addConstantForType(std::string tag, json j)
{
    if(!this->hasConstantsForType(tag))
    {
        this->constants[tag] = {};
    }

    this->constants[tag].push_back({j.dump(), j});
}

json FuzzInfo::pickConstantForType(std::string tag, RandGenerator& rnd) const
{
    auto citer = this->constants.find(tag);

    std::uniform_int_distribution<size_t> cdist(0, citer->second.size() - 1);
    return citer->second.at(cdist(rnd));
}

bool FuzzInfo::hasReuseForType(std::string tag) const
{
    return this->reuse.find(tag) != this->reuse.cend();
}

void FuzzInfo::addReuseForType(std::string tag, json j)
{
    if(!this->hasReuseForType(tag))
    {
        this->reuse[tag] = {};
    }
    std::vector<std::pair<std::string, json>>& tve = this->reuse[tag];

    std::string str = j.dump();
    auto mval = std::find_if(tve.cbegin(), tve.cend(), [&str](const std::pair<std::string, json>& entry) {
        entry.first == str;
    });

    if(mval == tve.cend())
    {
        tve.push_back({j.dump(), j});
    }
}

json FuzzInfo::pickReuseForType(std::string tag, RandGenerator& rnd) const
{
    auto riter = this->reuse.find(tag);

    std::uniform_int_distribution<size_t> rdist(0, riter->second.size() - 1);
    return riter->second.at(rdist(rnd));
}

bool FuzzInfo::sampleKnownOpt(std::string tag, RandGenerator& rnd, json& j)
{
    std::uniform_int_distribution<size_t> fchoice(0, 3);
    auto cval = fchoice(rnd);

    if(cval == 0 || cval == 1)
    {
        return false;
    }
    else if(cval == 2)
    {
        if(!this->hasConstantsForType(tag))
        {
            return false;
        }
        else
        {
            j = this->pickConstantForType(tag, rnd);
            return true;
        }
    }
    else
    {
         if(!this->hasReuseForType(tag))
        {
            return false;
        }
        else
        {
            j = this->pickReuseForType(tag, rnd);
            return true;
        }
    }
}

std::string generateRandomChar(RandGenerator& rnd)
{
    constexpr size_t printascii = 94;
    constexpr size_t nullchar = 1; 
    constexpr size_t smallunicode = 2; 
    constexpr size_t bigunicode = 1; 

    std::uniform_int_distribution<size_t> cchoice(0, printascii + nullchar + smallunicode + bigunicode);
    auto cval = cchoice(rnd);

    uint8_t small_unic[] = {/*£*/ 194, 163, /*µ*/ 194, 181};
    uint8_t emoji[] = {/*🌵*/ 240, 159, 140, 181};
    

    std::string data;
    if(cval <= printascii)
    {
        data.append({ (char)(32 + cval) });
    }
    else if(cval == printascii + nullchar)
    {
        data.append('\0');
    }
    else
    {
        if(cval <= printascii + nullchar + smallunicode)
        {
            size_t pos = 2*(cval - (printascii + nullchar));
            data.append({ (char)small_unic[pos], (char)small_unic[pos + 1] });
        }
        else
        {
            data.append({ (char)emoji[0], (char)emoji[1],  (char)emoji[2],  (char)emoji[3] });
        }
    }

    return data;
}

BSQRegexOpt* BSQRegexOpt::parse(json j)
{
    if(j.is_string())
    {
        return BSQLiteralRe::parse(j);
    }
    else
    {
        auto tag = j["tag"].get<std::string>();
        if(tag == "CharClass")
        {
            return BSQCharClassRe::parse(j);
        }
        else if(tag == "CharRange")
        {
            return BSQCharRangeRe::parse(j);
        }
        else if(tag == "StarRepeat")
        {
            return BSQStarRepeatRe::parse(j);
        }
        else if(tag == "PlusRepeat")
        {
            return BSQPlusRepeatRe::parse(j);
        }
        else if(tag == "RangeRepeat")
        {
            return BSQRangeRepeatRe::parse(j);
        }
        else if(tag == "Optional")
        {
            return BSQOptionalRe::parse(j);
        }
        else if(tag == "Alternation")
        {
            return BSQAlternationRe::parse(j);
        }
        else
        {
            return BSQSequenceRe::parse(j);
        }
    }
}

std::string BSQLiteralRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    return this->litval;
}

BSQLiteralRe* BSQLiteralRe::parse(json j)
{
    return new BSQLiteralRe(j.get<std::string>());
}

std::string BSQCharRangeRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    //
    //TODO: unicode support and escape support
    //
    assert(32 <= low && high < 126);

    std::uniform_int_distribution<uint32_t> distribution(low, high);
    return std::string{(char)distribution(rnd)};
}

BSQCharRangeRe* BSQCharRangeRe::parse(json j)
{
    auto lb = j["lb"].get<uint64_t>();
    auto ub = j["ub"].get<uint64_t>();

    return new BSQCharRangeRe(lb, ub);
}

std::string BSQCharClassRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    //
    //TODO: unicode support and escape support
    //
    if(this->kind == SpecialCharKind::Wildcard)
    {
        return generateRandomChar(rnd);
    }
    else
    {
        char ws_char[] = {' ', '\n', '\r', '\t' };
        std::uniform_int_distribution<uint32_t> chardist(0, sizeof(ws_char) - 1);

        return std::string{ws_char[chardist(rnd)]};
    }
}

BSQCharClassRe* BSQCharClassRe::parse(json j)
{
    auto kind = j["kind"].get<SpecialCharKind>();

    return new BSQCharClassRe(kind);
}

std::string BSQStarRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(0, finfo.limits.re_repeat_max);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQStarRepeatRe* BSQStarRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQStarRepeatRe(repeat);
}

std::string BSQPlusRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(1, finfo.limits.re_repeat_max);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQPlusRepeatRe* BSQPlusRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQPlusRepeatRe(repeat);
}

std::string BSQRangeRepeatRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> ctdist(this->low, this->high);

    auto ct = ctdist(rnd);
    std::string res;
    for(size_t i = 0; i < ct; ++i)
    {
        res.append(this->opt->generate(rnd, finfo));
    }

    return res;
}

BSQRangeRepeatRe* BSQRangeRepeatRe::parse(json j)
{
    auto min = j["min"].get<uint64_t>();
    auto max = j["max"].get<uint64_t>();
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQRangeRepeatRe(min, max, repeat);
}

std::string BSQOptionalRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<uint32_t> ctdist(0, 1);

    auto ct = ctdist(rnd);
    if(ct == 1)
    {
        return this->opt->generate(rnd, finfo);
    }
    else
    {
        return "";
    }
}

BSQOptionalRe* BSQOptionalRe::parse(json j)
{
    auto opt = BSQRegexOpt::parse(j["opt"]);

    return new BSQOptionalRe(opt);
}

std::string BSQAlternationRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::uniform_int_distribution<size_t> idxdist(0, this->opts.size() - 1);
    auto opt = this->opts[idxdist(rnd)];

    return opt->generate(rnd, finfo);   
}

BSQAlternationRe* BSQAlternationRe::parse(json j)
{
    std::vector<const BSQRegexOpt*> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](json arg) {
        return BSQRegexOpt::parse(arg);
    });

    return new BSQAlternationRe(opts);
}

std::string BSQSequenceRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    std::string res;
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        res.append(this->opts[i]->generate(rnd, finfo));
    }

    return res;
}

BSQSequenceRe* BSQSequenceRe::parse(json j)
{
    std::vector<const BSQRegexOpt*> elems;
    auto jelems = j["elems"];
    std::transform(jelems.cbegin(), jelems.cend(), std::back_inserter(elems), [](json arg) {
        return BSQRegexOpt::parse(arg);
    });

    return new BSQSequenceRe(elems);
}

std::string BSQRegex::generate(RandGenerator& rnd, FuzzInfo& finfo)
{
    return this->re->generate(rnd, finfo);
}

BSQRegex* BSQRegex::parse(json j)
{
    auto restr = j["restr"].get<std::string>();
    auto re = BSQRegexOpt::parse(j["re"]);

    return new BSQRegex(restr, re);
}

IType* IType::jparse(json j)
{
    xxxx;
}

NoneType* NoneType::jparse(json j)
{
    return new NoneType();
}

json NoneType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    return nullptr;
}

json NoneType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    return nullptr;
}

std::optional<std::string> NoneType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_null())
    {
        return std::nullopt;
    }
    else
    {
        return std::make_optional("none");
    }
}

std::optional<z3::expr> NoneType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_null())
    {
        return std::nullopt;
    }
    else
    {
        return pinfo->const_none;
    }
}

BoolType* BoolType::jparse(json j)
{
    return new BoolType();
}

json BoolType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<int> distribution(0, 1);
    return distribution(rnd) == 1 ? true : false;
}

json BoolType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_bool() && (v.is_true() || v.is_false()));

    return v.is_true();
}

std::optional<std::string> BoolType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_boolean())
    {
        return std::nullopt;
    }
    else
    {
        return std::make_optional(j.get<bool>() ? "true" : "false");
    }
}

std::optional<z3::expr> BoolType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_boolean())
    {
        return std::nullopt;
    }
    else
    {
        return pinfo->c->bool_val(j.get<bool>());
    }
}

NatType* NatType::jparse(json j)
{
    return new NatType();
}

json NatType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(0, finfo.limits.nat_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json NatType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_bv());

    return ex->bvToNatJSON(v);
}

std::optional<std::string> NatType::consprint(const ConvInfo& cinfo, json j) const
{ 
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = j.get<uint64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinon))
            {
                nval = std::stoull(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(sstr + "n");
    }
}

std::optional<z3::expr> NatType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = j.get<uint64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinon))
            {
                nval = std::stoull(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(pinfo->c->bv_val(sstr.c_str(), pinfo->bv_width));
    }
}

IntType* IntType::jparse(json j)
{
    return new IntType();
}

json IntType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(finfo.limits.int_min, finfo.limits.int_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json IntType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_bv());

    return ex->bvToIntJSON(v);
}

std::optional<std::string> IntType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = j.get<int64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinoi))
            {
                nval = std::stoll(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(sstr + "i");
    }
}

std::optional<z3::expr> IntType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = j.get<int64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinoi))
            {
                nval = std::stoll(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(pinfo->c->bv_val(sstr.c_str(), pinfo->bv_width));
    }
}

BigNatType* BigNatType::jparse(json j)
{
    return new BigNatType();
}

json BigNatType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(0, finfo.limits.nat_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json BigNatType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_int());

    return ex->intToBigNatJSON(v);
}

std::optional<std::string> BigNatType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinon))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(nval.value() + "N") : std::nullopt;
}

std::optional<z3::expr> BigNatType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinon))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(pinfo->c->int_val(nval.value().c_str())) : std::nullopt;
}

BigIntType* BigIntType::jparse(json j)
{
    return new BigIntType();
}

json BigIntType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(finfo.limits.int_min, finfo.limits.int_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json BigIntType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_int());

    return ex->intToBigIntJSON(v);
}

std::optional<std::string> BigIntType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinoi))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(nval.value() + "I") : std::nullopt;
}

std::optional<z3::expr> BigIntType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<uint64_t>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinoi))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(pinfo->c->int_val(nval.value().c_str())) : std::nullopt;
}

RationalType* RationalType::jparse(json j)
{
    return new RationalType();
}

json RationalType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<int64_t> distribution(finfo.limits.int_min, finfo.limits.int_max);
        uint64_t num = distribution(rnd);

        std::uniform_int_distribution<uint64_t> distribution(1, finfo.limits.nat_max);
        uint64_t denom = distribution(rnd);

        res = std::to_string(num) + "/" + std::to_string(denom) + "R";

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json RationalType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc("NSCore::Rational", ctx);
    assert(v.is_real());

    return ex->realToRationalJSON(v);
}

std::optional<std::string> RationalType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    BigIntType numtype;
    NatType denomtype;

    auto num = numtype.consprint(cinfo, j[0]);
    auto denom = denomtype.consprint(cinfo, j[1]);
    if(!num.has_value() || !denom.has_value())
    {
        return std::nullopt;
    }

    return std::make_optional(num.value().substr(0, num.value().size() - 1) + "/" + denom.value().substr(0, denom.value().size() - 1) + "R");
}

std::optional<z3::expr> RationalType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    BigIntType numtype;
    NatType denomtype;

    auto num = numtype.parseJSON(pinfo, j[0]);
    auto denom = denomtype.parseJSON(pinfo, j[1]);
        
    return (num.has_value() && denom.has_value()) ? std::make_optional(z3::to_real(num.value()) / z3::to_real(denom.value())) : std::nullopt;
}

FloatType* FloatType::jparse(json j)
{
    return new FloatType();
}

json FloatType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_real_distribution<double> distribution(finfo.limits.float_min, finfo.limits.float_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json FloatType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_real());

    return ex->realToFloatJSON(v);
}

std::optional<std::string> FloatType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinof))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(nval.value() + "f") : std::nullopt;
}

std::optional<z3::expr> FloatType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinof))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(pinfo->c->real_val(nval.value().c_str())) : std::nullopt;
}

DecimalType* DecimalType::jparse(json j)
{
    return new DecimalType();
}

json DecimalType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_real_distribution<double> distribution(finfo.limits.decimal_min, finfo.limits.decimal_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json DecimalType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_real());

    return ex->realToDecimalJSON(v);
}

std::optional<std::string> DecimalType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinof))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(nval.value() + "d") : std::nullopt;
}

std::optional<z3::expr> DecimalType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinof))
            {
                nval = sstr;
            }
        }
    }

    return nval.has_value() ? std::make_optional(pinfo->c->real_val(nval.value().c_str())) : std::nullopt;
}

StringType* StringType::jparse(json j)
{
    return new StringType();
}

json StringType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<size_t> distribution(0, finfo.limits.strlen_max);
        auto size = distribution(rnd);

        std::string res;
        for(size_t i = 0; i < size; ++i)
        {
            res.append(generateRandomChar(rnd));
        }

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json StringType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_string_value());

    return v.to_string();
}

std::optional<std::string> StringType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    return std::make_optional("\"" + j.get<std::string>() + "\"");
}

std::optional<z3::expr> StringType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    return std::make_optional(pinfo->c->string_val(j.get<std::string>()));
}

StringOfType* StringOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto validator = j["validator"].get<std::string>();
    auto re_validate = BSQRegex::parse(j["re_validate"]);

    return new StringOfType(name, validator, re_validate);
}

json StringOfType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::string res = this->re_validate->re->generate(rnd, finfo);
        while(res.size() > finfo.limits.strlen_max)
        {
            res = this->re_validate->re->generate(rnd, finfo);
        }
        
        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json StringOfType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalResultSuccess(this->name, ex->evalConsFunc(this->name, ctx));
    assert(v.is_string_value());

    return v.to_string();
}

std::optional<std::string> StringOfType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    return std::make_optional("'" + j.get<std::string>() + "'" + " of " + this->validator);
}

std::optional<z3::expr> StringOfType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    auto sof = j.get<std::string>();
    bool ok = std::regex_match(sof, this->re_validate->re_exec);

    return ok ? std::make_optional(pinfo->c->string_val(sof)) : std::nullopt;
}

NumberOfType* NumberOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto primitive = j["primitive"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    std::optional<std::string> smtinvcall = (j["smtinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;
    std::optional<std::string> cppinvcall = (j["cppinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;

    return new NumberOfType(name, primitive, oftype, smtinvcall, cppinvcall);
}

json NumberOfType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        //
        //TODO: register the check 
        //
        assert(!this->smtinvcall.has_value());

        json res = finfo.typemap.find(this->primitive)->second->fuzz(finfo, rnd);
        
        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json NumberOfType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    if(this->primitive == "NSCore::Nat")
    {
        assert(v.is_bv());
        return ex->bvToNatJSON(v);
    }
    else if(this->primitive == "NSCore::Int")
    {
        assert(v.is_bv());
        return ex->bvToIntJSON(v);
    }
    else if(this->primitive == "NSCore::BigNat")
    {
        assert(v.is_int());
        return ex->intToBigNatJSON(v);
    }
    else if(this->primitive == "NSCore::BigInt")
    {
        assert(v.is_int());
        return ex->intToBigIntJSON(v);
    }
    else if(this->primitive == "NSCore::Rational")
    {
        assert(v.is_real());
        return ex->realToRationalJSON(v);
    }
    else if(this->primitive == "NSCore::Float")
    {
        assert(v.is_real());
        return ex->realToFloatJSON(v);
    }
    else 
    {
        assert(v.is_real());
        return ex->realToDecimalJSON(v);
    }
}

std::optional<std::string> NumberOfType::consprint(const ConvInfo& cinfo, json j) const
{
    auto nres = cinfo.typemap.find(this->primitive)->second->consprint(cinfo, j);
    if(!nres.has_value())
    {
        return std::nullopt;
    }

    return std::make_optional(nres.value() + " of " + this->oftype);
}

std::optional<z3::expr> NumberOfType::parseJSON(ParseInfo* pinfo, json j) const
{
    auto nres = pinfo->typemap.find(this->primitive)->second->parseJSON(pinfo, j);
    if(!nres.has_value())
    {
        return std::nullopt;
    }

    //
    //TODO: register the check 
    //
    assert(!this->smtinvcall.has_value());

    return nres;
}

DataStringType* DataStringType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::string smtinvcall = j["smtinvcall"].get<std::string>();
    std::string cppinvcall = j["smtinvcall"].get<std::string>();

    return new DataStringType(name, oftype, isvalue, smtinvcall, cppinvcall);
}

json DataStringType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        //
        //TODO: register the check 
        //
        assert(false);

        std::uniform_int_distribution<size_t> distribution(0, finfo.limits.strlen_max);
        auto size = distribution(rnd);

        std::string res;
        for(size_t i = 0; i < size; ++i)
        {
            res.append(generateRandomChar(rnd));
        }

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json DataStringType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalResultSuccess(this->name, ex->evalConsFunc(this->name, ctx));
    assert(v.is_string_value());

    return v.to_string();
}

std::optional<std::string> DataStringType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    return std::make_optional("'" + j.get<std::string>() + "'" + (this->isvalue ? " # " : " @ ") + this->oftype);
}

std::optional<z3::expr> DataStringType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_string())
    { 
        return std::nullopt;
    }

    //
    //TODO: register the check 
    //
    assert(false);

    auto sof = j.get<std::string>();
    return std::make_optional(pinfo->c->string_val(sof));
}

ByteBufferType* ByteBufferType::jparse(json j)
{
    assert(false);
    return nullptr;
}

json ByteBufferType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

json ByteBufferType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
   assert(false);
   return nullptr;
}

std::optional<std::string> ByteBufferType::consprint(const ConvInfo& cinfo, json j) const
{
    assert(false);
    return "";
}

std::optional<z3::expr> ByteBufferType::parseJSON(ParseInfo* pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

BufferType* BufferType::jparse(json j)
{
    assert(false);
    return nullptr;
}

json BufferType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

json BufferType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
   assert(false);
   return nullptr;
}

std::optional<std::string> BufferType::consprint(const ConvInfo& cinfo, json j) const
{
    assert(false);
    return "";
}

std::optional<z3::expr> BufferType::parseJSON(ParseInfo* pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

DataBufferType* DataBufferType::jparse(json j)
{
    assert(false);
    return nullptr;
}

json DataBufferType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

json DataBufferType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
   assert(false);
   return nullptr;
}

std::optional<std::string> DataBufferType::consprint(const ConvInfo& cinfo, json j) const
{
    assert(false);
    return "";
}

std::optional<z3::expr> DataBufferType::parseJSON(ParseInfo* pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

ISOTimeType* ISOTimeType::jparse(json j)
{
    return new ISOTimeType();
}

json ISOTimeType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(finfo.limits.iso_time_min, finfo.limits.iso_time_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json ISOTimeType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_int());

    std::time_t dval = std::stoull(v.to_string());
    std::time_t tval = dval / 1000;
    uint32_t msval = dval % 1000;

    char mbuff[128];
    char* curr = mbuff;
    auto utctime = std::gmtime(&tval);
    curr += strftime(curr, 96, "%Y-%m-%dT%H:%M:%S", utctime);
    curr += snprintf(curr, 32, ".%03dZ", msval);

    return std::string(mbuff, curr);
}

std::optional<std::string> ISOTimeType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    return std::make_optional("\"" + j.get<std::string>() + "\"");
}

std::optional<z3::expr> ISOTimeType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    assert(false);
    return std::nullopt;
}

LogicalTimeType* LogicalTimeType::jparse(json j)
{
    return new LogicalTimeType();
}

json LogicalTimeType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<uint64_t> distribution(0, finfo.limits.ltime_max);
        res = distribution(rnd);

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

json LogicalTimeType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc(this->name, ctx);
    assert(v.is_int());

    return ex->intToLogicalTimeJSON(v);
}

std::optional<std::string> LogicalTimeType::consprint(const ConvInfo& cinfo, json j) const
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = j.get<uint64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, cinfo.re_numberinon))
            {
                nval = std::stoull(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(sstr + "T");
    }
}

std::optional<z3::expr> LogicalTimeType::parseJSON(ParseInfo* pinfo, json j) const
{
    std::optional<uint64_t> nval = std::nullopt;
    if(j.is_number_unsigned() || j.is_string())
    { 
        if(j.is_number_unsigned())
        {
            nval = j.get<uint64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, pinfo->re_numberinon))
            {
                nval = std::stoull(sstr);
            }
        }
    }

    if(!nval.has_value())
    {
        return std::nullopt;
    }
    else
    {
        auto sstr = std::to_string(nval.value());
        return std::make_optional(pinfo->c->int_val(sstr.c_str()));
    }
}

UUIDType* UUIDType::jparse(json j)
{
    assert(false);
    return nullptr;
}

json UUIDType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

json UUIDType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
   assert(false);
   return nullptr;
}

std::optional<std::string> UUIDType::consprint(const ConvInfo& cinfo, json j) const
{
    assert(false);
    return "";
}

std::optional<z3::expr> UUIDType::parseJSON(ParseInfo* pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

ContentHashType* ContentHashType::jparse(json j)
{
    assert(false);
    return nullptr;
}

json ContentHashType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

json ContentHashType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
   assert(false);
   return nullptr;
}

std::optional<std::string> ContentHashType::consprint(const ConvInfo& cinfo, json j) const
{
    assert(false);
    return "";
}

std::optional<z3::expr> ContentHashType::parseJSON(ParseInfo* pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

TupleType* TupleType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new TupleType(name, isvalue, ttypes);
}

json TupleType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    auto jres = json::array();
    std::transform(this->ttypes.cbegin(), this->ttypes.cend(), std::back_inserter(jres), [&finfo, &rnd](const std::string& tt) {
        auto ttype = finfo.typemap.find(tt)->second;
        return ttype->fuzz(finfo, rnd);
    });
    return jres;
}

json TupleType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto jres = json::array();
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = ex->evalConsFunc(tt, ex->stepContext(ctx, i));

        auto ttype = ex->typemap.find(tt)->second;
        jres.push_back(ttype->extract(ex, idxval));
    }
    return jres;
}

std::optional<std::string> TupleType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_array() || this->ttypes.size() != j.size())
    {
        return std::nullopt;
    }

    std::string bres;
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        if(i != 0)
        {
            bres += ", ";
        }

        auto ttype = cinfo.typemap.find(tt)->second;
        auto pexpr = ttype->consprint(cinfo, j[i]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += pexpr.value();
    }

    return std::make_optional(std::string(this->isvalue ? "#" : "@") + "[" + bres + "]");
}

std::optional<z3::expr> TupleType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_array() || this->ttypes.size() != j.size())
    {
        return std::nullopt;
    }

    z3::expr_vector targs(*(pinfo->c));
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ttype = pinfo->typemap.find(tt)->second;

        auto pexpr = ttype->parseJSON(pinfo, j[i]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        targs.push_back(pexpr.value());
    }

    return pinfo->constuplefuncs[this->name].value()(targs);
}

RecordType* RecordType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::pair<std::string, std::string>> ttypes;
    auto jtypes = j["entries"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return std::make_pair(jv[0].get<std::string>(), jv[1].get<std::string>());
    });

    return new RecordType(name, isvalue, ttypes);
}

json RecordType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->entries.size(); ++i)
    {
        const std::pair<std::string, std::string>& entry = this->entries[i];
        auto ttype = finfo.typemap.find(entry.second)->second;
        return jres[entry.first] = ttype->fuzz(finfo, rnd);
    }
    return jres;
}

json RecordType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->entries.size(); ++i)
    {
        const std::pair<std::string, std::string>& entry = this->entries[i];
        auto idxval = ex->evalConsFunc(entry.second, ex->stepContext(ctx, i));

        auto ttype = ex->typemap.find(entry.second)->second;
        jres[entry.first] = ttype->extract(ex, idxval);
    }
    return jres;
}

std::optional<std::string> RecordType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_object() || this->entries.size() != j.size())
    {
        return std::nullopt;
    }

    std::string bres;
    for(size_t i = 0; i < this->entries.size(); ++i)
    {
        const std::pair<std::string, std::string>& entry = this->entries[i];
        if(i != 0)
        {
            bres += ", ";
        }

        auto ttype = cinfo.typemap.find(entry.second)->second;
        auto pexpr = ttype->consprint(cinfo, j[entry.first]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += entry.first + ": " + pexpr.value();
    }

    return std::make_optional(std::string(this->isvalue ? "#" : "@") + "{" + bres + "}");
}

std::optional<z3::expr> RecordType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_object() || this->entries.size() != j.size())
    {
        return std::nullopt;
    }

    z3::expr_vector targs(*(pinfo->c));
    for(size_t i = 0; i < this->entries.size(); ++i)
    {
        const std::pair<std::string, std::string>& entry = this->entries[i];
        auto ttype = pinfo->typemap.find(entry.second)->second;

        auto pexpr = ttype->parseJSON(pinfo, j[entry.first]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        targs.push_back(pexpr.value());
    }

    return pinfo->consrecordfuncs[this->name].value()(targs);
}

ListType* ListType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();

    return new ListType(name, oftype);
}

json ListType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint64_t> distribution(0, finfo.limits.container_max);
    auto lsize = distribution(rnd);

    auto etype = finfo.typemap.find(this->oftype)->second;
    auto jres = json::array();
    for(size_t i = 0; i < lsize; ++i)
    {
        jres.push_back(etype->fuzz(finfo, rnd));
    }

    return jres;
}

json ListType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto etype = ex->typemap.find(this->oftype)->second;

    auto v = ex->evalConsFunc("ListSize", ctx);
    assert(v.is_bv());
        
    auto len = ex->bvToNumber(v);
    auto jres = json::array();
    for(size_t i = 0; i < len; ++i)
    {
        auto idxval = ex->evalConsFunc(this->oftype, ex->stepContext(ctx, i));
        jres.push_back(etype->extract(ex, idxval));
    }
    return jres;
}

std::optional<std::string> ListType::consprint(const ConvInfo& cinfo, json j) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    auto etype = cinfo.typemap.find(this->oftype)->second;

    std::string bres;
    for(size_t i = 0; i < j.size(); ++i)
    {
        if(i != 0)
        {
            bres += ", ";
        }

        auto pexpr = etype->consprint(cinfo, j[i]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += pexpr.value();
    }

    return std::make_optional(this->name + "@" + "{" + bres + "}");
}

std::optional<z3::expr> ListType::parseJSON(ParseInfo* pinfo, json j) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    auto etype = pinfo->typemap.find(this->oftype)->second;

    z3::expr_vector targs(*(pinfo->c));
    for(size_t i = 0; i < j.size(); ++i)
    {
        auto pexpr = etype->parseJSON(pinfo, j[i]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        targs.push_back(pexpr.value());
    }

    return pinfo->conslistfuncs[this->name].value()(targs);
}

UnionType* UnionType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto iskey = j["iskey"].get<bool>();

    std::vector<std::string> opts;
    auto jtypes = j["opts"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(opts), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new UnionType(name, iskey, opts);
}

json UnionType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint64_t> distribution(0, this->opts.size() - 1);
    auto i = distribution(rnd);

    auto otype = finfo.typemap.find(this->opts[i])->second;
    return otype->fuzz(finfo, rnd);
}

json UnionType::extract(ExtractionInfo* ex, const z3::expr& ctx) const
{
    auto v = ex->evalConsFunc("UnionItem", ctx);
    assert(v.is_bv());
        
    auto idx = ex->bvToNumber(v);
    auto uval = ex->evalConsFunc(this->opts[idx], ex->stepContext(ctx, 0));
    return ex->typemap.find(this->opts[idx])->second->extract(ex, uval);
}

std::optional<std::string> UnionType::consprint(const ConvInfo& cinfo, json j) const
{
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        auto pexpr = cinfo.typemap.find(this->opts[i])->second->consprint(cinfo, j);
        if(pexpr.has_value())
        {
            return pexpr;
        }
    }

    return std::nullopt;
}

std::optional<z3::expr> UnionType::parseJSON(ParseInfo* pinfo, json j) const
{
     for(size_t i = 0; i < this->opts.size(); ++i)
    {
        auto pexpr = pinfo->typemap.find(this->opts[i])->second->parseJSON(pinfo, j);
        if(pexpr.has_value())
        {
            auto boxhops = std::make_pair(this->opts[i], this->name);
            return std::make_optional(pinfo->boxfuncs[boxhops].value()(pexpr.value()));
        }
    }

    return std::nullopt;
}
