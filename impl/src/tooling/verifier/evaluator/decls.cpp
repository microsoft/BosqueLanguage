//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

void ExtractionInfo::loadConsFuncs(std::map<std::string, std::optional<z3::func_decl>>& consfuncs)
{
    xxx;
}

bool FuzzInfo::hasConstantsForType(TypeTag tag) const
{
    return this->constants.find(tag) != this->constants.cend();
}

void FuzzInfo::addConstantForType(TypeTag tag, json j)
{
    if(!this->hasConstantsForType(tag))
    {
        this->constants[tag] = {};
    }

    this->constants[tag].push_back({j.dump(), j});
}

json FuzzInfo::pickConstantForType(TypeTag tag, RandGenerator& rnd) const
{
    auto citer = this->constants.find(tag);

    std::uniform_int_distribution<size_t> cdist(0, citer->second.size() - 1);
    return citer->second.at(cdist(rnd));
}

bool FuzzInfo::hasReuseForType(TypeTag tag) const
{
    return this->reuse.find(tag) != this->reuse.cend();
}

void FuzzInfo::addReuseForType(TypeTag tag, json j)
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

json FuzzInfo::pickReuseForType(TypeTag tag, RandGenerator& rnd) const
{
    auto riter = this->reuse.find(tag);

    std::uniform_int_distribution<size_t> rdist(0, riter->second.size() - 1);
    return riter->second.at(rdist(rnd));
}

bool FuzzInfo::sampleKnownOpt(TypeTag tag, RandGenerator& rnd, json& j)
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
    auto ulimc = finfo.small_model_gen ? 3 : 10;
    std::uniform_int_distribution<size_t> ctdist(0, ulimc);

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
    auto ulimc = finfo.small_model_gen ? 3 : 10;
    std::uniform_int_distribution<size_t> ctdist(1, ulimc);

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

json NoneType::extract(ExtractionInfo* ex, z3::expr ctx) const
{
    return nullptr;
}

std::string NoneType::consprint(json j) const
{
    return "none";
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

json BoolType::extract(ExtractionInfo* ex, z3::expr ctx) const
{
    auto v = ex->evalConsFunc("NSCore::Bool", ctx);
    assert(v.is_bool() && (v.is_true() || v.is_false()));

    return v.is_true();
}

std::string BoolType::consprint(json j) const
{
    return j.get<bool>() ? "true" : "false";
}

NatType* NatType::jparse(json j)
{
    return new NatType();
}

json NatType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(TypeTag::NatTag, rnd, res))
    {
        return res;
    }
    else
    {
        auto ub = finfo.small_model_gen ? 10 : finfo.limits.nat_max;
    
        std::uniform_int_distribution<uint64_t> distribution(0, ub);
        res = std::to_string(distribution(rnd));

        finfo.addReuseForType(TypeTag::NatTag, res);
        return res;
    }
}

json NatType::extract(ExtractionInfo* ex, z3::expr ctx) const
{
    auto v = ex->evalConsFunc("NSCore::Nat", ctx);
    assert(v.is_bv());

    return v.();
}

std::string NatType::consprint(json j) const
{
    return  j.get<std::string>() + "n";
}

IntType* IntType::jparse(json j)
{
    return new IntType();
}

json IntType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    xxxx;
    auto lb = finfo.small_model_gen ? -10 : finfo.limits.int_min;
    auto ub = finfo.small_model_gen ? 10 : finfo.limits.int_max;
    
    std::uniform_int_distribution<uint64_t> distribution(lb, ub);
    return std::to_string(distribution(rnd));
}

json IntType::extract(ExtractionInfo* ex, z3::expr ctx) const
{
    auto v = ex->evalConsFunc("NSCore::Int", ctx);
    assert(v.is_bv());

    return v.();
}

std::string IntType::consprint(json j) const
{
    return j.get<std::string>() + "i";
}