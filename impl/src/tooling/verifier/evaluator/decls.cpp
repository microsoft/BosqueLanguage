//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

#define JSON_MIN_SAFE_NUMBER -9007199254740991
#define JSON_MAX_SAFE_NUMBER 9007199254740991

static std::regex re_numberino_n("^[+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_i("^[-+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_f("^[-+]?(0|[1-9][0-9]*)|([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$");

static std::regex re_bv_binary("^#b([0|1]+)$");
static std::regex re_bv_hex("^#x([0-9a-f]+)$");

int64_t computeBVMinSigned(int64_t bits)
{
    assert(bits <= 24 || bits == 32 || bits == 64);

    if(bits == 64)
    {
        return std::numeric_limits<int64_t>::lowest();
    }
    else if(bits == 32)
    {
        return std::numeric_limits<int32_t>::lowest();
    }
    else
    {
        return std::pow(2, bits) / 2;
    }
}

int64_t computeBVMaxSigned(int64_t bits)
{
    assert(bits <= 24 || bits == 32 || bits == 64);

    if(bits == 64)
    {
        return std::numeric_limits<int64_t>::max();
    }
    else if(bits == 32)
    {
        return std::numeric_limits<int32_t>::max();
    }
    else
    {
        return (std::pow(2, bits) / 2) - 1;
    }
}

uint64_t computeBVMaxUnSigned(uint64_t bits)
{
    assert(bits <= 24 || bits == 32 || bits == 64);

    if(bits == 64)
    {
        return std::numeric_limits<uint64_t>::max();
    }
    else if(bits == 32)
    {
        return std::numeric_limits<uint32_t>::max();
    }
    else
    {
        return std::pow(2, bits) - 1;
    }
}

template <typename T, bool bvsigned>
std::optional<T> bvBinSearch(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, T min, T max)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    T imin = min;
    T imax = max;
    while(imin < imax)
    {
        T imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
        auto imidstr = std::to_string(imid);

        s.push();

        z3::expr_vector chks(s.ctx());
        if constexpr (bvsigned)
        {
            chks.push_back(z3::slt(e, s.ctx().bv_val(imidstr.c_str(), apimodule->bv_width)));
        }
        else
        {
            chks.push_back(z3::ult(e, s.ctx().bv_val(imidstr.c_str(), apimodule->bv_width)));
        }
        auto rr = s.check(chks);

        s.pop();
        
        if(rr == z3::check_result::sat) 
        {
            imax = imid;
        }
        else if(rr == z3::check_result::unsat) 
        {
            imin = imid + 1;
        }
        else
        {
            return std::nullopt;
        }
    }

    return std::make_optional(imin);
}

template <typename T>
std::optional<T> intBinSearch(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, T min, T max)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    T imin = min;
    T imax = max;
    while(imin < imax)
    {
        T imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
        auto imidstr = std::to_string(imid);

        s.push();

        z3::expr_vector chks(s.ctx());
        chks.push_back(e < s.ctx().int_val(imidstr.c_str()));
        auto rr = s.check(chks);

        s.pop();
        
        if(rr == z3::check_result::sat) 
        {
            imax = imid;
        }
        else if(rr == z3::check_result::unsat) 
        {
            imin = imid + 1;
        }
        else
        {
            return std::nullopt;
        }
    }

    return std::make_optional(imin);
}

bool typenameMatches(const IType* tt, const char* prefix)
{
    auto plen = strlen(prefix);
    return tt->name.size() >= plen && std::equal(prefix, prefix + plen, tt->name.cbegin());
}

z3::sort getZ3SortFor(const APIModule* apimodule, const IType* tt, z3::context& c)
{
    if(tt->name == "NSCore::None")
    {
        return c.uninterpreted_sort("bsq_none");
    }
    else if(tt->name == "NSCore::Bool")
    {
        return c.bool_sort();
    }
    else if(tt->name == "NSCore::Nat")
    {
        return c.bv_sort(apimodule->bv_width);
    }
    else if(tt->name == "NSCore::Int")
    {
        return c.bv_sort(apimodule->bv_width);
    }
    else if(tt->name == "NSCore::BigNat")
    {
        return c.int_sort();
    }
    else if(tt->name == "NSCore::BigInt")
    {
        return c.int_sort();
    }
    else if(tt->name == "NSCore::Rational")
    {
        return c.real_sort();
    }
    else if(tt->name == "NSCore::Float")
    {
        return c.real_sort();
    }
    else if(tt->name == "NSCore::Decimal")
    {
        return c.real_sort();
    }
    else if(tt->name == "NSCore::String")
    {
        return c.string_sort();
    }
    else if(tt->name == "NSCore::ISOTime")
    {
        return c.int_sort();
    }
    else if(tt->name == "NSCore::LogicalTime")
    {
        return c.int_sort();
    }
    else if(tt->name == "NSCore::UUID")
    {
        return c.int_sort();
    }
    else if(tt->name == "NSCore::ContentHash")
    {
        return c.int_sort();
    }
    else if(typenameMatches(tt, "NSCore::StringOf") || typenameMatches(tt, "NSCore::DataString"))
    {
        return c.string_sort();
    }
    else if(typenameMatches(tt, "NSCore::NumberOf"))
    {
        return getZ3SortFor(apimodule, apimodule->typemap.find(dynamic_cast<const NumberOfType*>(tt)->primitive)->second, c);
    }
    else if(typenameMatches(tt, "NSCore::ByteBuffer") || typenameMatches(tt, "NSCore::Buffer") || typenameMatches(tt, "NSCore::DataBuffer"))
    {
        z3::sort bv8sort = c.bv_sort(8);
        return c.seq_sort(bv8sort);
    }
    else
    {
        return c.uninterpreted_sort(tt->smtname.c_str());
    }
}

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

z3::expr ExtractionInfo::genInitialContext(const z3::model& m) const
{
    auto bvsort = m.ctx().bv_sort(this->apimodule->bv_width);
    auto seqsort = m.ctx().seq_sort(bvsort);
    auto consf = m.ctx().function("Ctx@MakeStep", bvsort, seqsort);

    auto ii = m.ctx().bv_val((uint64_t)0, this->apimodule->bv_width);
    return consf(ii);
}

z3::expr ExtractionInfo::extendContext(const z3::model& m, const z3::expr& ctx, size_t i) const
{
    auto bvsort = m.ctx().bv_sort(this->apimodule->bv_width);
    auto seqsort = m.ctx().seq_sort(bvsort);
    auto consf = m.ctx().function("Ctx@MakeStep", bvsort, seqsort);

    auto ii = m.ctx().bv_val((uint64_t)i, this->apimodule->bv_width);
    return z3::concat(ctx, consf(ii));
}

std::optional<bool> ExtractionInfo::expBoolAsBool(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    if(strval == "true") 
    {
        s.add(e);
        return std::make_optional(true);
    }
    else if(strval == "false")
    {
        s.add(!e);
        return std::make_optional(false);
    }
    else
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        chks.push_back(e);
        auto rr = s.check(chks);

        s.pop();
        
        if(rr == z3::check_result::unknown)
        {
            return std::nullopt;
        }

        std::optional<bool> res = std::make_optional(rr == z3::check_result::sat);
        if(rr == z3::check_result::sat) 
        {
            s.add(e);
        }
        else
        {
            s.add(!e);
        }

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return res;
    }
}

std::optional<uint64_t> ExtractionInfo::expBVAsUInt(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_bv_binary))
    {
        auto bits = strval.substr(2);
        auto uval = std::stoull(bits, nullptr, 2);
        
        auto ustr = std::to_string(uval);
        s.add(e == s.ctx().bv_val(ustr.c_str(), this->apimodule->bv_width));

        return std::make_optional(uval);
    }
    else if(std::regex_match(strval, re_bv_hex))
    {
        auto bits = strval.substr(2);
        auto uval = std::stoull(bits, nullptr, 16);
        
        auto ustr = std::to_string(uval);
        s.add(e == s.ctx().bv_val(ustr.c_str(), this->apimodule->bv_width));

        return std::make_optional(uval);
    }
    else
    {
        auto uval = bvBinSearch<uint64_t, false>(this->apimodule, s, m, e, 0, computeBVMaxUnSigned(this->apimodule->bv_width));
        if(!uval.has_value())
        {
            return std::nullopt;
        }

        auto ustr = std::to_string(uval.value());
        s.add(e == s.ctx().bv_val(ustr.c_str(), this->apimodule->bv_width));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return uval;
    }
}

std::optional<int64_t> ExtractionInfo::expBVAsInt(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_bv_binary))
    {
        auto bits = strval.substr(2);
        auto ival = std::stoll(bits, nullptr, 2);
        
        auto sbits = (64 - this->apimodule->bv_width);
        int64_t rres = ((int64_t)(ival << sbits)) >> sbits;

        auto istr = std::to_string(rres);
        s.add(e == s.ctx().bv_val(istr.c_str(), this->apimodule->bv_width));

        return std::make_optional(rres);
    }
    else if(std::regex_match(strval, re_bv_hex))
    {
        auto bits = strval.substr(2);
        auto ival = std::stoll(bits, nullptr, 16);
        
        auto sbits = (64 - this->apimodule->bv_width);
        int64_t rres = ((int64_t)(ival << sbits)) >> sbits;

        auto istr = std::to_string(rres);
        s.add(e == s.ctx().bv_val(istr.c_str(), this->apimodule->bv_width));

        return std::make_optional(rres);
    }
    else
    {
        auto ival = bvBinSearch<int64_t, true>(this->apimodule, s, m, e, computeBVMinSigned(this->apimodule->bv_width), computeBVMaxSigned(this->apimodule->bv_width));
        if(!ival.has_value())
        {
            return std::nullopt;
        }

        auto istr = std::to_string(ival.value());
        s.add(e == s.ctx().bv_val(istr.c_str(), this->apimodule->bv_width));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return ival;
    }
}

std::optional<std::string> ExtractionInfo::expIntAsUInt(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_numberino_n))
    {
        s.add(e == s.ctx().int_val(strval.c_str()));

        return std::make_optional(strval);
    }
    else
    {
        //
        //TODO: we are limited here to 64 bit ints -- need to extend to a true big int search when we have the library support 
        //
        auto uval = intBinSearch<uint64_t>(this->apimodule, s, m, e, 0, std::numeric_limits<uint64_t>::max());
        if(!uval.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        auto ustr = std::to_string(uval.value());
        s.add(e == s.ctx().int_val(ustr.c_str()));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return std::make_optional(ustr);
    }
}

std::optional<std::string> ExtractionInfo::expIntAsInt(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_numberino_i))
    {
        s.add(e == s.ctx().int_val(strval.c_str()));

        return std::make_optional(strval);
    }
    else
    {
        //
        //TODO: we are limited here to 64 bit ints -- need to extend to a true big int search when we have the library support 
        //
        auto ival = intBinSearch<int64_t>(this->apimodule, s, m, e, std::numeric_limits<int64_t>::lowest(), std::numeric_limits<int64_t>::max());
        if(!ival.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        auto istr = std::to_string(ival.value());
        s.add(e == s.ctx().int_val(istr.c_str()));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return std::make_optional(istr);
    }
}

std::optional<std::string> ExtractionInfo::evalRealAsFP(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    auto sstr = nexp.to_string();

    std::cmatch match;
    if(std::regex_match(sstr, re_numberino_f))
    {
        s.add(e == s.ctx().real_val(sstr.c_str()));

        return std::make_optional(sstr);
    }
    else
    {
        //TODO: we need to do bin search for FP values as well
        assert(false);

        return std::nullopt;
    }
}

std::optional<size_t> ExtractionInfo::bvToCardinality(z3::solver& s, z3::model& m, const z3::expr& bv) const
{
    return this->expBVAsUInt(s, m, bv);
}

std::optional<size_t> ExtractionInfo::intToCardinality(z3::solver& s, z3::model& m, const z3::expr& iv) const
{
    auto res = this->expIntAsUInt(s, m, iv);
    if(!res.has_value())
    {
        return std::nullopt;
    }

    try
    {
            return std::make_optional(std::stoull(res.value()));
    }
    catch(...)
    {
        ;
    }

    return std::nullopt;
}

std::optional<json> ExtractionInfo::evalToBool(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    return this->expBoolAsBool(s, m, e);
}

std::optional<json> ExtractionInfo::evalToUnsignedNumber(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    if(e.is_int())
    {
        auto nstr = this->expIntAsUInt(s, m, e);
        if(!nstr.has_value())
        {
            return std::nullopt;
        }

        try
        {
            auto res = std::stoull(nstr.value());
            if(res <= (uint64_t)JSON_MAX_SAFE_NUMBER)
            {
                return std::make_optional(res);
            }  
            else
            {
                return nstr;
            }
        }
        catch(...)
        {
            ;
        }

        return nstr;
    }
    else
    {
        auto nval = this->expBVAsUInt(s, m, e);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        if(nval.value() <= (uint64_t)JSON_MAX_SAFE_NUMBER)
        {
            return nval;
        }  
        else
        {
            return std::make_optional(std::to_string(nval.value()));
        }
    }
}

std::optional<json> ExtractionInfo::evalToSignedNumber(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    if(e.is_int())
    {
        auto nstr = this->expIntAsInt(s, m, e);
        if(!nstr.has_value())
        {
            return std::nullopt;
        }

        try
        {
            auto res = std::stoll(nstr.value());
            if((int64_t)JSON_MIN_SAFE_NUMBER <= res && res <= (int64_t)JSON_MAX_SAFE_NUMBER)
            {
                return std::make_optional(res);
            }  
            else
            {
                return nstr;
            }
        }
        catch(...)
        {
            ;
        }

        return nstr;
    }
    else
    {
        auto nval = this->expBVAsInt(s, m, e);
        if(!nval.has_value())
        {
            return std::nullopt;
        }

        if((int64_t)JSON_MIN_SAFE_NUMBER <= nval.value() && nval.value() <= (int64_t)JSON_MAX_SAFE_NUMBER)
        {
            return nval;
        }  
        else
        {
            return std::make_optional(std::to_string(nval.value()));
        }
    }
}

std::optional<json> ExtractionInfo::evalToRealNumber(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto rstr = this->evalRealAsFP(s, m, e);
    if(!rstr.has_value())
    {
        return std::nullopt;
    }

    try
    {
        return std::make_optional(std::stod(rstr.value()));
    }
    catch(...)
    {
        ;
    }

    return rstr;
}

std::optional<json> ExtractionInfo::evalToDecimalNumber(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto rstr = this->evalRealAsFP(s, m, e);
    if(!rstr.has_value())
    {
        return std::nullopt;
    }

    try
    {
        return std::make_optional(std::stod(rstr.value()));
    }
    catch(...)
    {
        ;
    }

    return rstr;
}

std::optional<json> ExtractionInfo::evalToString(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto sexp = m.eval(e, true);
    auto sstr = sexp.to_string();

    if(sstr.length() >= 2 && sstr[0] == '"' && sstr[sstr.length() - 1] == '"')
    {
        s.add(e == s.ctx().string_val(sstr.c_str()));

        return std::make_optional(sstr);
    }
    else
    {
        //TODO: we need to do bin search for FP values as well
        assert(false);

        return std::nullopt;
    }
}

z3::expr ExtractionInfo::callfunc(std::string fname, const z3::expr_vector& args, const std::vector<const IType*>& argtypes, const IType* restype, z3::context& c) const
{
    auto ressort = getZ3SortFor(this->apimodule, restype, c);

    z3::sort_vector argsorts(c);
    for(size_t i = 0; i < argtypes.size(); ++i)
    {
        argsorts.push_back(getZ3SortFor(this->apimodule, argtypes[i], c));
    }

    auto consf = c.function(fname.c_str(), argsorts, ressort);

    return consf(args);
}


z3::expr ExtractionInfo::callfunc(std::string fname, const z3::expr& arg, const IType* argtype, const IType* restype, z3::context& c) const
{
    z3::expr_vector argv(c);
    argv.push_back(arg);

    return this->callfunc(fname, argv, {argtype}, restype, c);
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
            if(std::regex_match(sstr, re_numberino_n))
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
            if(std::regex_match(sstr, re_numberino_i))
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
            if(std::regex_match(sstr, re_numberino_n))
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
            if(std::regex_match(sstr, re_numberino_i))
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
            if(std::regex_match(sstr, re_numberino_f))
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
        if(std::regex_match(sstr, re_numberino_f))
        {
            nval = sstr;
        }
    }

    return nval;
}

z3::expr ParseInfo::callfunc(std::string fname, const z3::expr_vector& args, const std::vector<const IType*>& argtypes, const IType* restype, z3::context& c) const
{
    auto ressort = getZ3SortFor(this->apimodule, restype, c);

    z3::sort_vector argsorts(c);
    for(size_t i = 0; i < argtypes.size(); ++i)
    {
        argsorts.push_back(getZ3SortFor(this->apimodule, argtypes[i], c));
    }

    auto consf = c.function(fname.c_str(), argsorts, ressort);

    return consf(args);
}

z3::expr ParseInfo::callfunc(std::string fname, const z3::expr& arg, const IType* argtype, const IType* restype, z3::context& c) const
{
    z3::expr_vector argv(c);
    argv.push_back(arg);

    return this->callfunc(fname, argv, {argtype}, restype, c);
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
        return entry.first == str;
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
        data.append({ '\0' });
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
    switch(j["tag"].get<TypeTag>())
    {
        case TypeTag::NoneTag:
            return NoneType::jparse(j);
        case TypeTag::BoolTag:
            return BoolType::jparse(j);
        case TypeTag::NatTag:
            return NatType::jparse(j);
        case TypeTag::IntTag:
            return IntType::jparse(j);
        case TypeTag::BigNatTag:
            return BigNatType::jparse(j);
        case TypeTag::BigIntTag:
            return BigIntType::jparse(j);
        case TypeTag::RationalTag:
            return RationalType::jparse(j);
        case TypeTag::FloatTag:
            return FloatType::jparse(j);
        case TypeTag::DecimalTag:
            return DecimalType::jparse(j);
        case TypeTag::StringTag:
            return StringType::jparse(j);
        case TypeTag::StringOfTag:
            return StringOfType::jparse(j);
        case TypeTag::NumberOfTag:
            return NumberOfType::jparse(j);
        case TypeTag::DataStringTag:
            return DataStringType::jparse(j);
        case TypeTag::ByteBufferTag:
            return ByteBufferType::jparse(j);
        case TypeTag::BufferTag:
            return BufferType::jparse(j);
        case TypeTag::DataBufferTag:
            return DataBufferType::jparse(j);
        case TypeTag::ISOTag:
            return ISOTimeType::jparse(j);
        case TypeTag::LogicalTag:
            return LogicalTimeType::jparse(j);
        case TypeTag::UUIDTag:
            return UUIDType::jparse(j);
        case TypeTag::ContentHashTag:
            return ContentHashType::jparse(j);
        case TypeTag::TupleTag:
            return TupleType::jparse(j);
        case TypeTag::RecordTag:
            return RecordType::jparse(j);
        case TypeTag::ListTag:
            return ListType::jparse(j);
        case TypeTag::EnumTag:
            return EnumType::jparse(j);
        case TypeTag::UnionTag:
            return UnionType::jparse(j);
        default: 
        {
            assert(false);
            return nullptr;
        }
    }
}

NoneType* NoneType::jparse(json j)
{
    return new NoneType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> NoneType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
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

std::optional<json> NoneType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return std::make_optional(nullptr);
}

std::optional<json> NoneType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    return std::make_optional(nullptr);
}

BoolType* BoolType::jparse(json j)
{
    return new BoolType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> BoolType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
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

std::optional<json> BoolType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBool@UFCons_API", m.ctx().bool_sort());
    return ex.evalToBool(s, m, bef(ctx));
}

std::optional<json> BoolType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bool_sort());
    return ex.evalToBool(s, m, ref);
}

NatType* NatType::jparse(json j)
{
    return new NatType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> NatType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    std::optional<uint64_t> nval = pinfo.parseToUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(std::to_string(nval.value()) + "n");
}

std::optional<json> NatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BNat@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

std::optional<json> NatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(s, m, ref);
}

IntType* IntType::jparse(json j)
{
    return new IntType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> IntType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    std::optional<int64_t> nval = pinfo.parseToSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(std::to_string(nval.value()) + "i");
}

std::optional<json> IntType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BInt@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

std::optional<json> IntType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToSignedNumber(s, m, ref);
}

BigNatType* BigNatType::jparse(json j)
{
    return new BigNatType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> BigNatType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "N");
}

std::optional<json> BigNatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBigNat@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

std::optional<json> BigNatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, ref);
}

BigIntType* BigIntType::jparse(json j)
{
    return new BigIntType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> BigIntType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    std::optional<std::string> nval = pinfo.parseToBigSignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "I");
}

std::optional<json> BigIntType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BBigInt@UFCons_API", m.ctx().int_sort());
    return ex.evalToSignedNumber(s, m, bef(ctx));
}

std::optional<json> BigIntType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToSignedNumber(s, m, ref);
}

RationalType* RationalType::jparse(json j)
{
    return new RationalType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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
        const BigIntType* numtype = (const BigIntType*)finfo.apimodule->typemap.find("NSCore::BigInt")->second;
        const NatType* denomtype = (const NatType*)finfo.apimodule->typemap.find("NSCore::Nat")->second;

        json num = numtype->fuzz(finfo, rnd);
        json denom = denomtype->fuzz(finfo, rnd);

        res = { num, denom };

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

std::optional<std::string> RationalType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
     if(!j.is_array())
    {
        return std::nullopt;
    }

    const BigIntType* numtype = (const BigIntType*)pinfo.apimodule->typemap.find("NSCore::BigInt")->second;
    const NatType* denomtype = (const NatType*)pinfo.apimodule->typemap.find("NSCore::Nat")->second;

    auto num = numtype->tobsqarg(pinfo, j[0], "");
    auto denom = denomtype->tobsqarg(pinfo, j[1], "");
        
    return (num.has_value() && denom.has_value()) ? std::make_optional(num.value() + "/" + denom.value() + "R") : std::nullopt;
}

std::optional<json> RationalType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> RationalType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

FloatType* FloatType::jparse(json j)
{
    return new FloatType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> FloatType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    auto fval = pinfo.parseToRealNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return fval.value() + "f";
}

std::optional<json> FloatType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BFloat@UFCons_API", m.ctx().real_sort());
    return ex.evalToRealNumber(s, m, bef(ctx));
}

std::optional<json> FloatType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().real_sort());
    return ex.evalToRealNumber(s, m, ref);
}

DecimalType* DecimalType::jparse(json j)
{
    return new DecimalType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> DecimalType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    auto fval = pinfo.parseToDecimalNumber(j);
    if(!fval.has_value())
    {
        return std::nullopt;
    }
        
    return fval.value() + "d";
}

std::optional<json> DecimalType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BDecimal@UFCons_API", m.ctx().real_sort());
    return ex.evalToDecimalNumber(s, m, bef(ctx));
}

std::optional<json> DecimalType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().real_sort());
    return ex.evalToDecimalNumber(s, m, ref);
}

StringType* StringType::jparse(json j)
{
    return new StringType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> StringType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return std::make_optional("\"" + j.get<std::string>() + "\"");
}

std::optional<json> StringType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BString@UFCons_API", m.ctx().real_sort());
    return ex.evalToString(s, m, bef(ctx));
}

std::optional<json> StringType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().string_sort());
    return ex.evalToString(s, m, ref);
}

StringOfType* StringOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto validator = j["validator"].get<std::string>();
    auto re_validate = BSQRegex::parse(j["re_validate"]);

    return new StringOfType(name, j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>(), validator, re_validate);
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
    //Assume check is handled at runtime so the solver can ignore it
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, c);
}

std::optional<std::string> StringOfType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    auto pstr = pinfo.apimodule->typemap.find("NSCore::String")->second->tobsqarg(pinfo, j, indent);
    if(!pstr.has_value())
    {
        return std::nullopt;
    }
        
    return "\'" + pstr.value().substr(1, pstr.value().size() - 2) + "\'" + " of " + this->name;
}

std::optional<json> StringOfType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return ex.apimodule->typemap.find("NSCore::String")->second->argextract(ex, ctx, s, m);
}

std::optional<json> StringOfType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    return ex.apimodule->typemap.find("NSCore::String")->second->resextract(ex, res, s, m);
}

NumberOfType* NumberOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto primitive = j["primitive"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    std::optional<std::string> smtinvcall = (j["smtinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;
    std::optional<std::string> cppinvcall = (j["cppinvcall"] != nullptr) ? std::make_optional(j["smtinvcall"].get<std::string>()) : std::nullopt;

    return new NumberOfType(name, j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>(), primitive, oftype, smtinvcall, cppinvcall);
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
        json res = finfo.apimodule->typemap.find(this->primitive)->second->fuzz(finfo, rnd);
        
        finfo.addReuseForType(this->name, res);
        return res;
    }
}

std::optional<z3::expr> NumberOfType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    //Assume check is handled at runtime so the solver can ignore it
    return pinfo.apimodule->typemap.find(this->primitive)->second->toz3arg(pinfo, j, c);
}

std::optional<std::string> NumberOfType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    auto pstr = pinfo.apimodule->typemap.find(this->primitive)->second->tobsqarg(pinfo, j, indent);
    if(!pstr.has_value())
    {
        return std::nullopt;
    }
        
    return pstr.value() + " of " + this->name;
}

std::optional<json> NumberOfType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return ex.apimodule->typemap.find(this->primitive)->second->argextract(ex, ctx, s, m);
}

std::optional<json> NumberOfType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    return ex.apimodule->typemap.find(this->primitive)->second->resextract(ex, res, s, m);
}

DataStringType* DataStringType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::string smtinvcall = j["smtinvcall"].get<std::string>();
    std::string cppinvcall = j["cppinvcall"].get<std::string>();

    return new DataStringType(name, j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>(), oftype, isvalue, smtinvcall, cppinvcall);
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
    //Assume check is handled at runtime so the solver can ignore it
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, c);
}

std::optional<std::string> DataStringType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    auto pstr = pinfo.apimodule->typemap.find("NSCore::String")->second->tobsqarg(pinfo, j, indent);
    if(!pstr.has_value())
    {
        return std::nullopt;
    }
        
    return "\'" + pstr.value().substr(1, pstr.value().size() - 2) + "\'" + (this->isvalue ? "#" : "@") + this->name;
}

std::optional<json> DataStringType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    //havoc restrictions will ensure that invariant is respected
    return ex.apimodule->typemap.find("NSCore::String")->second->argextract(ex, ctx, s, m);
}

std::optional<json> DataStringType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    //constructor restrictions will ensure that invariant is respected
    return ex.apimodule->typemap.find("NSCore::String")->second->resextract(ex, res, s, m);
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

std::optional<std::string> ByteBufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> ByteBufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> ByteBufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
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

std::optional<std::string> BufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> BufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> BufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
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

std::optional<std::string> DataBufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> DataBufferType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> DataBufferType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

ISOTimeType* ISOTimeType::jparse(json j)
{
    return new ISOTimeType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> ISOTimeType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    return j.get<std::string>();
}

std::optional<json> ISOTimeType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BISOTime@UFCons_API", m.ctx().int_sort());
    auto itime = ex.intToCardinality(s, m, bef(ctx));
    if(!itime.has_value())
    {
        return std::nullopt;
    }

    std::time_t dval = itime.value();
    std::time_t tval = dval / 1000;

    char mbuff[128];
    char* curr = mbuff;
    auto utctime = std::gmtime(&tval);
    curr += strftime(curr, 96, "%Y-%m-%dT%H:%M:%S", utctime);
    curr += snprintf(curr, 32, ".%03dZ", (int)(dval % 1000));

    return std::string(mbuff, curr);
}

std::optional<json> ISOTimeType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    auto itime = ex.intToCardinality(s, m, ref);
    if(!itime.has_value())
    {
        return std::nullopt;
    }

    std::time_t dval = itime.value();
    std::time_t tval = dval / 1000;

    char mbuff[128];
    char* curr = mbuff;
    auto utctime = std::gmtime(&tval);
    curr += strftime(curr, 96, "%Y-%m-%dT%H:%M:%S", utctime);
    curr += snprintf(curr, 32, ".%03dZ", (int)(dval % 1000));

    return std::string(mbuff, curr);
}

LogicalTimeType* LogicalTimeType::jparse(json j)
{
    return new LogicalTimeType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> LogicalTimeType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return std::nullopt;
    }
    
    return std::make_optional(nval.value() + "T");
}

std::optional<json> LogicalTimeType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "BLogicalTime@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

std::optional<json> LogicalTimeType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, ref);
}

UUIDType* UUIDType::jparse(json j)
{
    return new UUIDType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> UUIDType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> UUIDType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> UUIDType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

ContentHashType* ContentHashType::jparse(json j)
{
    return new ContentHashType(j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>());
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

std::optional<std::string> ContentHashType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> ContentHashType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

std::optional<json> ContentHashType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
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
    auto smttypetag = j["smttypetag"].get<std::string>();
    auto boxfunc = j["boxfunc"].get<std::string>();
    auto unboxfunc = j["unboxfunc"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<std::string> smtaccessors;
    auto jaccessors = j["smtaccessors"];
    std::transform(jaccessors.cbegin(), jaccessors.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new TupleType(name, iskey, smtname, smttypetag, boxfunc, unboxfunc, consfunc, isvalue, ttypes, smtaccessors);
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

    std::vector<const IType*> argtypes;
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

        argtypes.push_back(ttype);
        targs.push_back(pexpr.value());
    }

    return pinfo.callfunc(this->consfunc, targs, argtypes, this, c);
}

std::optional<std::string> TupleType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_array() || this->ttypes.size() != j.size())
    {
        return std::nullopt;
    }

    auto iidt = indent + "  ";
    std::string bres;
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        
        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->tobsqarg(pinfo, j[i], iidt);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += '\n' + iidt + pexpr.value();

        if(i != this->ttypes.size() - 1)
        {
            bres += ',' ;
        }
    }

    if(this->ttypes.size() == 0)
    {
        return std::make_optional(indent + std::string(this->isvalue ? "#" : "@") + "[]");
    }
    else
    {
        return std::make_optional(indent + std::string(this->isvalue ? "#" : "@") + "[" + bres + indent + "]");
    }
}

std::optional<json> TupleType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::array();
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = ex.extendContext(m, ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        auto rr = ttype->argextract(ex, idxval, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres.push_back(rr.value());
    }
    return std::make_optional(jres);
}

std::optional<json> TupleType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto jres = json::array();
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ttype = ex.apimodule->typemap.find(tt)->second;

        auto access = ex.callfunc(this->smtaccessors[i], res, this, ttype, m.ctx());
        auto ival = m.eval(access, true);
        auto rr = ttype->resextract(ex, ival, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres.push_back(rr.value());
    }
    return std::make_optional(jres);
}

RecordType* RecordType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto iskey = j["iskey"].get<bool>();
    auto smtname = j["smtname"].get<std::string>();
    auto smttypetag = j["smttypetag"].get<std::string>();
    auto consfunc = j["consfunc"].get<std::string>();
    auto boxfunc = j["boxfunc"].get<std::string>();
    auto unboxfunc = j["unboxfunc"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    std::vector<std::string> props;
    auto jprops = j["props"];
    std::transform(jprops.cbegin(), jprops.cend(), std::back_inserter(props), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<std::string> smtaccessors;
    auto jaccessors = j["smtaccessors"];
    std::transform(jaccessors.cbegin(), jaccessors.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new RecordType(name, iskey, smtname, smttypetag, boxfunc, unboxfunc, consfunc, isvalue, props, ttypes, smtaccessors);
}

json RecordType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        auto ttype = finfo.apimodule->typemap.find(this->ttypes[i])->second;
        return jres[this->ttypes[i]] = ttype->fuzz(finfo, rnd);
    }
    return jres;
}

std::optional<z3::expr> RecordType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_object() || this->props.size() != j.size())
    {
        return std::nullopt;
    }

    auto allprops = std::all_of(this->props.cbegin(), this->props.cend(), [&j](const std::string& prop){
                return j.contains(prop);
            });
    if(!allprops)
    {
        return std::nullopt;
    }

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ttype = pinfo.apimodule->typemap.find(tt)->second;

        auto pexpr = ttype->toz3arg(pinfo, j[i], c);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        argtypes.push_back(ttype);
        targs.push_back(pexpr.value());
    }

    return std::make_optional(pinfo.callfunc(this->consfunc, targs, argtypes, this, c));
}

std::optional<std::string> RecordType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_object() || this->props.size() != j.size())
    {
        return std::nullopt;
    }

    auto allprops = std::all_of(this->props.cbegin(), this->props.cend(), [&j](const std::string& prop){
                return j.contains(prop);
            });
    if(!allprops)
    {
        return std::nullopt;
    }

    auto iidt = indent + "  ";
    std::string bres;
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
       
        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->tobsqarg(pinfo, j[i], iidt);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += '\n' + iidt + this->props[i] + "=" + pexpr.value();

        if(i != this->ttypes.size() - 1)
        {
            bres += ',' ;
        }
    }

    if(this->ttypes.size() == 0)
    {
        return std::make_optional(indent + std::string(this->isvalue ? "#" : "@") + "{}");
    }
    else
    {
        return std::make_optional(indent + std::string(this->isvalue ? "#" : "@") + "{" + bres + indent + "}");
    }
}

std::optional<json> RecordType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = ex.extendContext(m, ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        auto rr = ttype->argextract(ex, idxval, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres[this->props[i]] = rr.value();
    }

    return std::make_optional(jres);
}

std::optional<json> RecordType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ttype = ex.apimodule->typemap.find(tt)->second;

        auto access = ex.callfunc(this->smtaccessors[i], res, this, ttype, m.ctx());
        auto ival = m.eval(access, true);
        auto rr = ttype->resextract(ex, ival, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres[this->props[i]] = rr.value();
    }

    return std::make_optional(jres);
}

ListType* ListType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto smtname = j["smtname"].get<std::string>();
    auto smttypetag = j["smttypetag"].get<std::string>();
    auto boxfunc = j["boxfunc"].get<std::string>();
    auto unboxfunc = j["unboxfunc"].get<std::string>();

    auto oftype = j["oftype"].get<std::string>();
    auto smtsizefunc = j["smtsizefunc"].get<std::string>();
    auto smtgetfunc = j["smtgetfunc"].get<std::string>();

    std::vector<std::string> smtconsfunc_k;
    auto jcons = j["smtconsfunc_k"];
    std::transform(jcons.cbegin(), jcons.cend(), std::back_inserter(smtconsfunc_k), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new ListType(name, smtname, smttypetag, boxfunc, unboxfunc, oftype, smtconsfunc_k, smtsizefunc, smtgetfunc);
}

json ListType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint64_t> distribution(0, finfo.limits.container_max);
    auto lsize = distribution(rnd);

    auto etype = finfo.apimodule->typemap.find(this->oftype)->second;
    auto jres = json::array();
    for(size_t i = 0; i < lsize; ++i)
    {
        jres.push_back(etype->fuzz(finfo, rnd));
    }

    return jres;
}

std::optional<z3::expr> ListType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    auto ttype = pinfo.apimodule->typemap.find(this->oftype)->second;

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < j.size(); ++i)
    {

        auto pexpr = ttype->toz3arg(pinfo, j[i], c);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        argtypes.push_back(ttype);
        targs.push_back(pexpr.value());
    }

    //
    //TODO: we need to add an append function here as well 
    //
    assert(j.size() <= 5);

    if(j.size() == 0)
    {
        return std::make_optional(c.constant(this->smtconsfunc_k[0].c_str(), c.uninterpreted_sort(this->smtname.c_str())));
    }
    else
    {
        return std::make_optional(pinfo.callfunc(this->smtconsfunc_k[j.size()], targs, argtypes, this, c));
    }
}

std::optional<std::string> ListType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_array())
    {
        return std::nullopt;
    }

    auto ttype = pinfo.apimodule->typemap.find(this->oftype)->second;

    auto iidt = indent + "  ";
    std::string bres;
    for(size_t i = 0; i < j.size(); ++i)
    {
        auto pexpr = ttype->tobsqarg(pinfo, j[i], iidt);
        if(!pexpr.has_value())
        {
            return std::nullopt;
        }

        bres += '\n' + iidt + pexpr.value();

        if(i != j.size() - 1)
        {
            bres += ',' ;
        }
    }

    if(j.size() == 0)
    {
        return std::make_optional(indent + this->name + "@" + "{}");
    }
    else
    {
        return std::make_optional(indent + this->name + "@" + "{" + bres + indent + "}");
    }
}

std::optional<json> ListType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::array();

    auto lef = ex.getArgContextConstructor(m, "ListSize@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto lenval = ex.bvToCardinality(s, m, lef(ctx));
    if(!lenval.has_value())
    {
        return std::nullopt;
    }

    auto ttype = ex.apimodule->typemap.find(this->oftype)->second;

    for(size_t i = 0; i < lenval.value(); ++i)
    {
        auto idxval = ex.extendContext(m, ctx, i);
        auto rr = ttype->argextract(ex, idxval, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres.push_back(rr.value());
    }

    return std::make_optional(jres);
}

std::optional<json> ListType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto lef = ex.callfunc(this->smtsizefunc, res, this, ex.apimodule->typemap.find("NSCore::Nat")->second, m.ctx());
    auto lenval = ex.bvToCardinality(s, m, m.eval(lef, true));
    if(!lenval.has_value())
    {
        return std::nullopt;
    }

    auto ttype = ex.apimodule->typemap.find(this->oftype)->second;

    auto jres = json::array();
    for(size_t i = 0; i < lenval.value(); ++i)
    {
        auto access = ex.callfunc(this->smtgetfunc, res, this, ttype, m.ctx());
        auto ival = m.eval(access, true);
        auto rr = ttype->resextract(ex, ival, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres.push_back(rr.value());
    }

    return std::make_optional(jres);
}

EnumType* EnumType::jparse(json j)
{
    std::vector<std::pair<std::string, std::string>> enuminvs;
    auto jenuminvs = j["enuminvs"];
    std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enuminvs), [](const json& jv) {
        return std::make_pair(jv["enum"].get<std::string>(), jv["inv"].get<std::string>());
    });

    return new EnumType(j["name"].get<std::string>(), j["smtname"].get<std::string>(), j["smttypetag"].get<std::string>(), j["boxfunc"].get<std::string>(), j["unboxfunc"].get<std::string>(), j["underlying"].get<std::string>(), j["smttagfunc"].get<std::string>(), j["smtselectfunc"].get<std::string>(), enuminvs);
}

json EnumType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    json res;
    if(finfo.sampleKnownOpt(this->name, rnd, res))
    {
        return res;
    }
    else
    {
        std::uniform_int_distribution<size_t> distribution(0, this->enuminvs.size() - 1);
        auto opt = distribution(rnd);

        res = this->enuminvs[opt].first;

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

std::optional<z3::expr> EnumType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
    
    auto ename = j.get<std::string>();
    auto ii = std::find_if(this->enuminvs.cbegin(), this->enuminvs.cend(), [&ename](const std::pair<std::string, std::string>& entry) {
        return entry.first == ename;
    });

    if(ii == this->enuminvs.cend())
    {
        return std::nullopt;
    }

    return std::make_optional(c.constant(ii->second.c_str(), getZ3SortFor(pinfo.apimodule, this, c)));
}

std::optional<std::string> EnumType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return j.get<std::string>();
}

std::optional<json> EnumType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    //auto bef = ex.getArgContextConstructor(m, "EnumChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    //auto choice = ex.bvToCardinality(m, bef(ctx));

    //
    //TODO: call the select func
    //

    assert(false);
    return nullptr;
}

std::optional<json> EnumType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    auto ref = m.ctx().constant(ex.resvar.c_str(), getZ3SortFor(ex.apimodule, this, m.ctx()));
    auto enumconst = ex.callfunc(this->smttagfunc.c_str(), ref, this, ex.apimodule->typemap.find("NSCore::String")->second, m.ctx()).to_string();

    return enumconst;
}

UnionType* UnionType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto iskey = j["iskey"].get<bool>();

    auto smtname = j["smtname"].get<std::string>();

    std::vector<std::string> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new UnionType(name, iskey, smtname, opts);
}

json UnionType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint64_t> distribution(0, this->opts.size() - 1);
    auto i = distribution(rnd);

    auto otype = finfo.apimodule->typemap.find(this->opts[i])->second;
    return otype->fuzz(finfo, rnd);
}

std::optional<z3::expr> UnionType::toz3arg(ParseInfo& pinfo, json j, z3::context& c) const
{
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        auto ttype = dynamic_cast<const IGroundedType*>(pinfo.apimodule->typemap.find(this->opts[i])->second);
        auto pexpr = ttype->toz3arg(pinfo, j, c);
        if(pexpr.has_value())
        {
            if(this->iskey)
            {
                if(ttype->name == "NSCore::None")
                {
                    return std::make_optional(c.constant("BKey@none", c.uninterpreted_sort("BKey")));
                }
                else
                {
                    auto boxobjfunc = c.function(ttype->boxfunc.c_str(), getZ3SortFor(pinfo.apimodule, ttype, c), c.uninterpreted_sort("bsq_keyobject"));
                    auto boxkeyfunc = c.function("BKey@box", c.uninterpreted_sort("TypeTag"), c.uninterpreted_sort("bsq_keyobject"), c.uninterpreted_sort("BKey"));
                    
                    auto ttag = c.constant(ttype->smttypetag.c_str(), c.uninterpreted_sort("TypeTag"));
                    return std::make_optional(boxkeyfunc(ttag, boxobjfunc(pexpr.value())));
                }
            }
            else
            {
                if(ttype->name == "NSCore::None")
                {
                    return std::make_optional(c.constant("BTerm@none", c.uninterpreted_sort("BTerm")));
                }
                else if(ttype->iskey)
                {
                    auto boxobjfunc = c.function(ttype->boxfunc.c_str(), getZ3SortFor(pinfo.apimodule, ttype, c), c.uninterpreted_sort("bsq_keyobject"));
                    auto boxkeyfunc = c.function("BKey@box", c.uninterpreted_sort("TypeTag"), c.uninterpreted_sort("bsq_keyobject"), c.uninterpreted_sort("BKey"));
                    auto boxkeytermfunc = c.function("BTerm@keybox",c.uninterpreted_sort("BKey"), c.uninterpreted_sort("BTerm"));
                    
                    auto ttag = c.constant(ttype->smttypetag.c_str(), c.uninterpreted_sort("TypeTag"));
                    return std::make_optional(boxkeytermfunc(boxkeyfunc(ttag, boxobjfunc(pexpr.value()))));
                }
                else
                {
                    auto boxobjfunc = c.function(ttype->boxfunc.c_str(), getZ3SortFor(pinfo.apimodule, ttype, c), c.uninterpreted_sort("bsq_object"));
                    auto boxtermfunc = c.function("BTerm@box", c.uninterpreted_sort("TypeTag"), c.uninterpreted_sort("bsq_object"), c.uninterpreted_sort("BTerm"));
                    
                    auto ttag = c.constant(ttype->smttypetag.c_str(), c.uninterpreted_sort("TypeTag"));
                    return std::make_optional(boxtermfunc(ttag, boxobjfunc(pexpr.value())));
                }
            }
        }
    }

    return std::nullopt;
}

std::optional<std::string> UnionType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        auto ttype = dynamic_cast<const IGroundedType*>(pinfo.apimodule->typemap.find(this->opts[i])->second);
        auto pexpr = ttype->tobsqarg(pinfo, j, indent);
        if(pexpr.has_value())
        {
            return pexpr;
        }
    }

    return std::nullopt;
}

std::optional<json> UnionType::argextract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = ex.getArgContextConstructor(m, "UnionChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto choice = ex.bvToCardinality(s, m, bef(ctx));
    if(!choice.has_value())
    {
        return std::nullopt;
    }

    auto ttype = dynamic_cast<const IGroundedType*>(ex.apimodule->typemap.find(this->opts[choice.value()])->second);
    return ttype->argextract(ex, ctx, s, m);
}

std::optional<json> UnionType::resextract(ExtractionInfo& ex, const z3::expr& res, z3::solver& s, z3::model& m) const
{
    z3::context& c = m.ctx();

    auto getkeytagfunc = c.function("GetTypeTag@BKey", c.uninterpreted_sort("BKey"), c.uninterpreted_sort("TypeTag"));
    auto gettermtagfunc = c.function("GetTypeTag@BTerm", c.uninterpreted_sort("BTerm"), c.uninterpreted_sort("TypeTag"));

    std::string tag = m.eval(this->iskey ? getkeytagfunc(res) : gettermtagfunc(res), true).to_string();
    const IGroundedType* ttype = dynamic_cast<const IGroundedType*>(std::find_if(ex.apimodule->typemap.cbegin(), ex.apimodule->typemap.cend(), [&tag](const std::pair<std::string, const IType*>& entry) {
        auto gtype = dynamic_cast<const IGroundedType*>(entry.second);
        return gtype != nullptr && gtype->smttypetag == tag;
    })->second);

    if(this->iskey)
    {
        auto unboxkeyfunc = c.function("BKey_value", c.uninterpreted_sort("BKey"), c.uninterpreted_sort("bsq_keyobject"));
        auto unboxobjfunc = c.function(ttype->unboxfunc.c_str(), c.uninterpreted_sort("bsq_keyobject"), getZ3SortFor(ex.apimodule, ttype, c));
                    
        auto vval = m.eval(unboxobjfunc(unboxkeyfunc(res)), true);
        return ttype->resextract(ex, vval, s, m);
    }
    else
    {
        if(ttype->iskey)
        {
            auto unboxtermfunc = c.function("BTerm_keyvalue", c.uninterpreted_sort("BTerm"), c.uninterpreted_sort("BKey"));
            auto unboxkeyfunc = c.function("BKey_value", c.uninterpreted_sort("BKey"), c.uninterpreted_sort("bsq_keyobject"));
            auto unboxobjfunc = c.function(ttype->unboxfunc.c_str(), c.uninterpreted_sort("bsq_keyobject"), getZ3SortFor(ex.apimodule, ttype, c));

            auto vval = m.eval(unboxobjfunc(unboxkeyfunc(unboxtermfunc(res))), true);
            return ttype->resextract(ex, vval, s, m);
        }
        else
        {
            auto unboxtermfunc = c.function("BTerm_termvalue", c.uninterpreted_sort("BTerm"), c.uninterpreted_sort("bsq_object"));
            auto unboxobjfunc = c.function(ttype->unboxfunc.c_str(), c.uninterpreted_sort("bsq_object"), getZ3SortFor(ex.apimodule, ttype, c));
                    
            auto vval = m.eval(unboxobjfunc(unboxtermfunc(res)), true);
            return ttype->resextract(ex, vval, s, m);
        }
    }
}

InvokeSignature* InvokeSignature::jparse(json j, const std::map<std::string, const IType*>& typemap)
{
    auto name = j["name"].get<std::string>();
    auto resType = typemap.find(j["resType"].get<std::string>())->second;

    std::vector<std::string> argnames;
    auto jargnames = j["argnames"];
    std::transform(jargnames.cbegin(), jargnames.cend(), std::back_inserter(argnames), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<std::string> smtargnames;
    auto jsmtargnames = j["smtargnames"];
    std::transform(jsmtargnames.cbegin(), jsmtargnames.cend(), std::back_inserter(smtargnames), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<const IType*> argtypes;
    auto jargtypes = j["argtypes"];
    std::transform(jargtypes.cbegin(), jargtypes.cend(), std::back_inserter(argtypes), [&typemap](const json& jv) {
        return typemap.find(jv.get<std::string>())->second;
    });

    return new InvokeSignature(name, resType, argnames, smtargnames, argtypes);
}

APIModule* APIModule::jparse(json j)
{
    std::map<std::string, const IType*> typemap;
    auto japitypes = j["apitypes"];
    for (size_t i = 0; i < japitypes.size(); ++i)
    {
        auto val = IType::jparse(japitypes[i]);
        typemap[val->name] = val;
    }

    InvokeSignature* apisig = InvokeSignature::jparse(j["apisig"], typemap);

    std::map<std::string, std::vector<std::pair<std::string, json>>> constants;
    //
    //TODO: load constants
    //

    return new APIModule(typemap, apisig, j["bvwidth"].get<size_t>(), constants);
}