//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

#define JSON_MIN_SAFE_NUMBER -9007199254740991
#define JSON_MAX_SAFE_NUMBER 9007199254740991

z3::func_decl ExtractionInfo::getArgContextConstructor(const z3::model& m, const char* fname, const z3::sort& ressort) const
{
    auto ctxsort = this->getArgContextTokenSort(m);
    auto argconsf = m.ctx().function(fname, ctxsort, ressort);

    return argconsf;
}

z3::sort ExtractionInfo::getArgContextTokenSort(const z3::model& m) const
{
    auto bvsort = m.ctx().bv_sort(this->apimodule->bv_width);
    auto seqsort = m.ctx().seq_sort(bvsort);

    return seqsort;
}

z3::expr ExtractionInfo::extendContext(const z3::model& m, const z3::expr& ctx, size_t i) const
{
    auto bvsort = m.ctx().bv_sort(this->apimodule->bv_width);
    auto seqsort = m.ctx().seq_sort(bvsort);
    auto consf = m.ctx().function("Ctx@MakeStep", bvsort, seqsort);

    auto ii = m.ctx().bv_val((uint64_t)i, bvsort);
    return z3::concat(ctx, consf(ii));
}

size_t ExtractionInfo::bvToCardinality(const z3::model& m, const z3::expr& bv) const
{
    auto nstr = m.eval(bv, true).to_string();
    std::string sstr(nstr.cbegin() + 2, nstr.cend());
    return std::stoull(sstr, nullptr, nstr[1] == 'b' ? 2 : 16);
}

size_t ExtractionInfo::intToCardinality(const z3::model& m, const z3::expr& iv) const
{
    auto nstr = m.eval(iv, true).to_string();
    return std::stoull(nstr);
}

json ExtractionInfo::evalToBool(const z3::model& m, const z3::expr& e) const
{
    auto bstr = m.eval(e, true).to_string();
    return bstr == "true";
}

json ExtractionInfo::evalToUnsignedNumber(const z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    auto nstr = nexp.to_string();
    if(nexp.is_int())
    {
        try
        {
            return std::stoull(nstr);
        }
        catch(...)
        {
            ;
        }

        return nstr;
    }
    else
    {
        std::string sstr(nstr.cbegin() + 2, nstr.cend());
        uint64_t res = std::stoull(sstr, nullptr, nstr[1] == 'b' ? 2 : 16);

        if(res <= (uint64_t)JSON_MAX_SAFE_NUMBER)
        {
            return res;
        }  
        else
        {
            return std::to_string(res);
        }
    }
}

json ExtractionInfo::evalToSignedNumber(const z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    auto nstr = nexp.to_string();
    if(nexp.is_int())
    {
        try
        {
            return std::stoll(nstr);
        }
        catch(...)
        {
            ;
        }

        return nstr;
    }
    else
    {
        std::string sstr(nstr.cbegin() + 2, nstr.cend());
        uint64_t res = std::stoull(sstr, nullptr, nstr[1] == 'b' ? 2 : 16);

        int64_t rres = (int64_t)((~res) + 1);
        if(JSON_MIN_SAFE_NUMBER <= rres && rres <= JSON_MAX_SAFE_NUMBER)
        {
            return rres;
        }  
        else
        {
            return std::to_string(rres);
        }
    }
}

json ExtractionInfo::evalToRealNumber(const z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    assert(nexp.is_real());

    auto sstr = nexp.to_string();
    try
    {
        return std::stod(sstr);
    }
    catch(...)
    {
        ;
    }

    return sstr;
}

json ExtractionInfo::evalToDecimalNumber(const z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    assert(nexp.is_real());

    return nexp.to_string();
}

json ExtractionInfo::evalToString(const z3::model& m, const z3::expr& e) const
{
    auto sexp = m.eval(e, true);
    assert(sexp.is_string_value());

    return sexp.to_string();
}

std::optional<uint64_t> ParseInfo::parseToUnsignedNumber(json j) const
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
            if(std::regex_match(sstr, this->re_numberinon))
            {
                try
                {
                    nval = std::stoull(sstr);
                }
                catch(...)
                {
                    ;
                }
            }
        }
    }

    return nval;
}

std::optional<int64_t> ParseInfo::parseToSignedNumber(json j) const
{
    std::optional<int64_t> nval = std::nullopt;
    if(j.is_number_integer() || j.is_string())
    { 
        if(j.is_number_integer())
        {
            nval = j.get<int64_t>();
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, this->re_numberinoi))
            {
                try
                {
                    nval = std::stoll(sstr);
                }
                catch(...)
                {
                    ;
                }
            }
        }
    }

    return nval;
}

std::optional<std::string> ParseInfo::parseToBigUnsignedNumber(json j) const
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
            if(std::regex_match(sstr, this->re_numberinon))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> ParseInfo::parseToBigSignedNumber(json j) const
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
            if(std::regex_match(sstr, this->re_numberinoi))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> ParseInfo::parseToRealNumber(json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_number() || j.is_string())
    { 
        if(j.is_number())
        {
            nval = std::to_string(j.get<double>());
        }
        else
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, this->re_numberinof))
            {
                nval = sstr;
            }
        }
    }

    return nval;
}

std::optional<std::string> ParseInfo::parseToDecimalNumber(json j) const
{
    std::optional<std::string> nval = std::nullopt;
    if(j.is_string())
    { 
        std::string sstr = j.get<std::string>();
        if(std::regex_match(sstr, this->re_numberinof))
        {
            nval = sstr;
        }
    }

    return nval;
}

z3::expr ParseInfo::callfunc(std::string fname, z3::expr_vector& args, const std::vector<std::string>& smtargtypes, const std::string& smtrestype, z3::context& c) const
{
    auto ressort = c.uninterpreted_sort(smtrestype.c_str());

    z3::sort_vector argsorts(c);
    for(size_t i = 0; i < smtargtypes.size(); ++i)
    {
        argsorts.push_back(c.uninterpreted_sort(smtargtypes[i].c_str()));
    }

    auto consf = c.function(fname.c_str(), argsorts, ressort);

    return consf(args);
}

bool FuzzInfo::hasConstantsForType(std::string tag) const
{
    return this->apimodule->constants.find(tag) != this->apimodule->constants.cend();
}

json FuzzInfo::pickConstantForType(std::string tag, RandGenerator& rnd) const
{
    auto citer = this->apimodule->constants.find(tag);

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
    return new NoneType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
}

json NoneType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    return nullptr;
}

 std::optional<z3::expr> NoneType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
 {
     if(!j.is_null())
    {
        return std::nullopt;
    }
    else
    {
        return c.constant("bsq_none", c.uninterpreted_sort(this->smtname.c_str()));
    }
 }

std::optional<std::string> NoneType::tobsqarg(const ParseInfo& pinfo, json j) const
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

json NoneType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    return nullptr;
}

json NoneType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    return nullptr;
}

BoolType* BoolType::jparse(json j)
{
    return new BoolType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
}

json BoolType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<int> distribution(0, 1);
    return distribution(rnd) == 1 ? true : false;
}

 std::optional<z3::expr> BoolType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
 {
     if(!j.is_boolean())
    {
        return std::nullopt;
    }
    else
    {
        return c.bool_val(j.get<bool>());
    }
 }

std::optional<std::string> BoolType::tobsqarg(const ParseInfo& pinfo, json j) const
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

json BoolType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBool@UFCons_API", m.ctx().bool_sort());
    return ex.evalToBool(m, bef(ctx));
}

json BoolType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bool_sort());
    return ex.evalToBool(m, ref);
}

NatType* NatType::jparse(json j)
{
    return new NatType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> NatType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    std::optional<uint64_t> nval = pinfo.parseToUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.bv_val(nval.value(), pinfo.apimodule->bv_width));
}

std::optional<std::string> NatType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    std::optional<uint64_t> nval = pinfo.parseToUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(std::to_string(nval.value()) + "n");
}

json NatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BNat@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    ex.evalToUnsignedNumber(m, bef(ctx));
}

json NatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(m, ref);
}

IntType* IntType::jparse(json j)
{
    return new IntType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> IntType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    std::optional<int64_t> nval = pinfo.parseToSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.bv_val(nval.value(), pinfo.apimodule->bv_width));
}

std::optional<std::string> IntType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    std::optional<int64_t> nval = pinfo.parseToSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(std::to_string(nval.value()) + "i");
}

json IntType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BInt@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    ex.evalToUnsignedNumber(m, bef(ctx));
}

json IntType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToSignedNumber(m, ref);
}

BigNatType* BigNatType::jparse(json j)
{
    return new BigNatType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> BigNatType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.int_val(nval.value().c_str()));
}

std::optional<std::string> BigNatType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "N");
}

json BigNatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBigNat@UFCons_API", m.ctx().int_sort());
    ex.evalToUnsignedNumber(m, bef(ctx));
}

json BigNatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToUnsignedNumber(m, ref);
}

BigIntType* BigIntType::jparse(json j)
{
    return new BigIntType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> BigIntType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.int_val(nval.value().c_str()));
}

std::optional<std::string> BigIntType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    std::optional<std::string> nval = pinfo.parseToBigSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "I");
}

json BigIntType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBigInt@UFCons_API", m.ctx().int_sort());
    ex.evalToSignedNumber(m, bef(ctx));
}

json BigIntType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToSignedNumber(m, ref);
}

RationalType* RationalType::jparse(json j)
{
    return new RationalType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> RationalType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    const BigIntType* numtype = (const BigIntType*)pinfo.apimodule->typemap.find("NSCore::BigInt")->second;
    const NatType* denomtype = (const NatType*)pinfo.apimodule->typemap.find("NSCore::Nat")->second;

    auto num = numtype->toz3arg(pinfo, j[0], c);
    auto denom = denomtype->toz3arg(pinfo, j[1], c);
        
    return (num.has_value() && denom.has_value()) ? std::make_optional(z3::to_real(num.value()) / z3::to_real(denom.value())) : std::nullopt;
}

std::optional<std::string> RationalType::tobsqarg(const ParseInfo& pinfo, json j) const
{
     if(!j.is_array())
    {
        return std::nullopt;
    }

    const BigIntType* numtype = (const BigIntType*)pinfo.apimodule->typemap.find("NSCore::BigInt")->second;
    const NatType* denomtype = (const NatType*)pinfo.apimodule->typemap.find("NSCore::Nat")->second;

    auto num = numtype->tobsqarg(pinfo, j[0]);
    auto denom = denomtype->tobsqarg(pinfo, j[1]);
        
    return (num.has_value() && denom.has_value()) ? std::make_optional(num.value() + "/" + denom.value() + "R") : std::nullopt;
}

json RationalType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json RationalType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
}

FloatType* FloatType::jparse(json j)
{
    return new FloatType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> FloatType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    auto fval = pinfo.parseToRealNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return std::make_optional(c.real_val(fval.value().c_str()));
}

std::optional<std::string> FloatType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    auto fval = pinfo.parseToRealNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return fval.value() + "f";
}

json FloatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BFloat@UFCons_API", m.ctx().real_sort());
    ex.evalToRealNumber(m, bef(ctx));
}

json FloatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().real_sort());
    return ex.evalToRealNumber(m, ref);
}

DecimalType* DecimalType::jparse(json j)
{
    return new DecimalType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> DecimalType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    auto fval = pinfo.parseToDecimalNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return std::make_optional(c.real_val(fval.value().c_str()));
}

std::optional<std::string> DecimalType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    auto fval = pinfo.parseToDecimalNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return fval.value() + "d";
}

json DecimalType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BDecimal@UFCons_API", m.ctx().real_sort());
    ex.evalToDecimalNumber(m, bef(ctx));
}

json DecimalType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().real_sort());
    return ex.evalToDecimalNumber(m, ref);
}

StringType* StringType::jparse(json j)
{
    return new StringType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> StringType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return std::make_optional(c.string_val(j.get<std::string>().c_str()));
}

std::optional<std::string> StringType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return "\"" + j.get<std::string>() + "\"";
}

json StringType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BString@UFCons_API", m.ctx().real_sort());
    ex.evalToString(m, bef(ctx));
}

json StringType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().string_sort());
    return ex.evalToString(m, ref);
}

StringOfType* StringOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto validator = j["validator"].get<std::string>();
    auto re_validate = BSQRegex::parse(j["re_validate"]);

    return new StringOfType(name, j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>(), validator, re_validate);
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

std::optional<z3::expr> StringOfType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.string_val(j.get<std::string>().c_str()));
}

std::optional<std::string> StringOfType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return "\'" + j.get<std::string>() + "\'" + " of " + this->name;
}

json StringOfType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BString@UFCons_API", m.ctx().string_sort());
    ex.evalToString(m, bef(ctx));
}

json StringOfType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().string_sort());
    return ex.evalToString(m, ref);
}

NumberOfType* NumberOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto primitive = j["primitive"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    std::optional<std::string> smtinvcall = (j["smtinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;
    std::optional<std::string> cppinvcall = (j["cppinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;

    return new NumberOfType(name, j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>(), primitive, oftype, smtinvcall, cppinvcall);
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

        json res = finfo.apimodule->typemap.find(this->primitive)->second->fuzz(finfo, rnd);
        
        finfo.addReuseForType(this->name, res);
        return res;
    }
}

std::optional<z3::expr> NumberOfType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    //
    //TODO: register the check 
    //
    assert(!this->smtinvcall.has_value());
    
    return pinfo.apimodule->typemap.find(this->primitive)->second->toz3arg(pinfo, j, c);
}

std::optional<std::string> NumberOfType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    auto pstr = pinfo.apimodule->typemap.find(this->primitive)->second->tobsqarg(pinfo, j);
    if(!pstr.has_value())
    {
        return std::nullopt;
    }
        
    return pstr.value() + " of " + this->name;
}

json NumberOfType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    return ex.apimodule->typemap.find(this->primitive)->second->argextract(ex, ctx, m);
}

json NumberOfType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    return ex.apimodule->typemap.find(this->primitive)->second->resextract(ex, res, m);
}

DataStringType* DataStringType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::string smtinvcall = j["smtinvcall"].get<std::string>();
    std::string cppinvcall = j["smtinvcall"].get<std::string>();

    return new DataStringType(name, j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>(), oftype, isvalue, smtinvcall, cppinvcall);
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

std::optional<z3::expr> DataStringType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> DataStringType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return "\'" + j.get<std::string>() + "\'" + (this->isvalue ? "#" : "@") + this->name;
}

json DataStringType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BString@UFCons_API", m.ctx().string_sort());
    ex.evalToString(m, bef(ctx));
}

json DataStringType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().string_sort());
    return ex.evalToString(m, ref);
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

std::optional<z3::expr> ByteBufferType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> ByteBufferType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

json ByteBufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json ByteBufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
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

std::optional<z3::expr> BufferType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> BufferType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

json BufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json BufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
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

std::optional<z3::expr> DataBufferType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> DataBufferType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

json DataBufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json DataBufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
}

ISOTimeType* ISOTimeType::jparse(json j)
{
    return new ISOTimeType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> ISOTimeType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> ISOTimeType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    return j.get<std::string>();
}

json ISOTimeType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BISOTime@UFCons_API", m.ctx().int_sort());

    std::time_t dval = ex.intToCardinality(m, bef(ctx));
    std::time_t tval = dval / 1000;

    char mbuff[128];
    char* curr = mbuff;
    auto utctime = std::gmtime(&tval);
    curr += strftime(curr, 96, "%Y-%m-%dT%H:%M:%S", utctime);
    curr += snprintf(curr, 32, ".%03dZ", dval % 1000);

    return std::string(mbuff, curr);
}

json ISOTimeType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());

    std::time_t dval = ex.intToCardinality(m, ref);
    std::time_t tval = dval / 1000;

    char mbuff[128];
    char* curr = mbuff;
    auto utctime = std::gmtime(&tval);
    curr += strftime(curr, 96, "%Y-%m-%dT%H:%M:%S", utctime);
    curr += snprintf(curr, 32, ".%03dZ", dval % 1000);

    return std::string(mbuff, curr);
}

LogicalTimeType* LogicalTimeType::jparse(json j)
{
    return new LogicalTimeType(j["smtname"].get<std::string>(), j["boxfunc"].get<std::string>());
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

std::optional<z3::expr> LogicalTimeType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(c.int_val(nval.value().c_str()));
}

std::optional<std::string> LogicalTimeType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "T");
}

json LogicalTimeType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BLogicalTime@UFCons_API", m.ctx().int_sort());
    ex.evalToUnsignedNumber(m, bef(ctx));
}

json LogicalTimeType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToUnsignedNumber(m, ref);
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

std::optional<z3::expr> UUIDType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> UUIDType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

json UUIDType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json UUIDType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
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

std::optional<z3::expr> ContentHashType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    assert(false);
    return std::nullopt;
}

std::optional<std::string> ContentHashType::tobsqarg(const ParseInfo& pinfo, json j) const
{
    assert(false);
    return std::nullopt;
}

json ContentHashType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    assert(false);
    return nullptr;
}

json ContentHashType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    assert(false);
    return nullptr;
}

TupleType* TupleType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto iskey = j["iskey"].get<bool>();
    auto smtname = j["smtname"].get<std::string>();
    auto consfunc = j["consfunc"].get<std::string>();
    auto boxfunc = j["boxfunc"].get<std::string>(); 
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new TupleType(name, iskey, smtname, boxfunc, consfunc, isvalue, ttypes);
}

json TupleType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    auto jres = json::array();
    std::transform(this->ttypes.cbegin(), this->ttypes.cend(), std::back_inserter(jres), [&finfo, &rnd](const std::string& tt) {
        auto ttype = finfo.apimodule->typemap.find(tt)->second;
        return ttype->fuzz(finfo, rnd);
    });
    return jres;
}

std::optional<z3::expr> TupleType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_array() || this->ttypes.size() != j.size())
    {
        return std::nullopt;
    }

    std::vector<std::string> smtargtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ttype = pinfo.apimodule->typemap.find(tt)->second;

        auto pexpr = ttype->toz3arg(pinfo, j[i], c);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        smtargtypes.push_back(ttype->smtname);
        targs.push_back(pexpr.value());
    }

    return pinfo.callfunc(this->consfunc, targs, smtargtypes, this->smtname, c);
}

std::optional<std::string> TupleType::tobsqarg(const ParseInfo& pinfo, json j) const
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

        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->tobsqarg(pinfo, j[i]);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += pexpr.value();
    }

    return std::make_optional(std::string(this->isvalue ? "#" : "@") + "[" + bres + "]");
}

json TupleType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::model& m) const
{
    auto jres = json::array();
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = ex.extendContext(m, ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        jres.push_back(ttype->argextract(ex, idxval, m));
    }
    return jres;
}

json TupleType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::model& m) const
{
    xxxx;
    assert(false);
    return nullptr;
}

RecordType* RecordType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto iskey = j["iskey"].get<bool>();
    auto smtname = j["smtname"].get<std::string>();
    auto boxfunc = j["boxfunc"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::pair<std::string, std::string>> ttypes;
    auto jtypes = j["entries"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return std::make_pair(jv[0].get<std::string>(), jv[1].get<std::string>());
    });

    return new RecordType(name, iskey, smtname, boxfunc, isvalue, ttypes);
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
