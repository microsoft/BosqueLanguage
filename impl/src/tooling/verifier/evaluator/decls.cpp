//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

#define JSON_MIN_SAFE_NUMBER -9007199254740991
#define JSON_MAX_SAFE_NUMBER 9007199254740991

static std::regex re_numberino_n("^[+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_i("^[-+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_f("^[-+]?([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$");
static std::regex re_fpdiverino("^[(]\\/\\s([-+]?([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?)\\s([-+]?([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?)[)]$");

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

std::optional<uint64_t> bvBinSearchUnsigned(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, uint64_t min, uint64_t max, const std::vector<uint64_t>& copts)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    for(size_t i = 0; i < copts.size(); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string iistr = std::to_string(copts[i]);
        chks.push_back(e == s.ctx().bv_val(iistr.c_str(), apimodule->bv_width));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    uint64_t imin = min;
    uint64_t imax = max;
    while(imin < imax)
    {
        uint64_t imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
        auto imidstr = std::to_string(imid);

        s.push();

        z3::expr_vector chks(s.ctx());
        chks.push_back(z3::ult(e, s.ctx().bv_val(imidstr.c_str(), apimodule->bv_width)));
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

std::optional<int64_t> bvBinSearchSigned(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, int64_t min, int64_t max, const std::vector<int64_t>& copts)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    for(size_t i = 0; i < copts.size(); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string iistr = std::to_string(copts[i]);
        chks.push_back(e == s.ctx().bv_val(iistr.c_str(), apimodule->bv_width));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    int64_t imin = min;
    int64_t imax = max;
    while(imin < imax)
    {
        int64_t imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
        auto imidstr = std::to_string(imid);

        if (imid >= 0)
        {
            s.push();

            z3::expr_vector chks(s.ctx());
            chks.push_back(z3::slt(e, s.ctx().bv_val(imidstr.c_str(), apimodule->bv_width)));
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
        else
        {
            s.push();

            z3::expr_vector chks(s.ctx());
            chks.push_back(z3::sgt(e, s.ctx().bv_val(imidstr.c_str(), apimodule->bv_width)));
            auto rr = s.check(chks);

            s.pop();

            if(rr == z3::check_result::sat)
            {
                imin = imid;
            }
            else if(rr == z3::check_result::unsat)
            {
                imax = imid - 1;
            }
            else
            {
                return std::nullopt;
            }
        }
    }

    return std::make_optional(imin);
}

std::optional<uint64_t> intBinSearchUnsigned(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, uint64_t min, uint64_t max, const std::vector<uint64_t>& copts)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    for(size_t i = 0; i < copts.size(); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string iistr = std::to_string(copts[i]);
        chks.push_back(e == s.ctx().int_val(iistr.c_str()));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    uint64_t imin = min;
    uint64_t imax = max;
    while(imin < imax)
    {
        uint64_t imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
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

std::optional<int64_t> intBinSearchSigned(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, int64_t min, int64_t max, const std::vector<int64_t>& copts)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    for(size_t i = 0; i < copts.size(); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string iistr = std::to_string(copts[i]);
        chks.push_back(e == s.ctx().int_val(iistr.c_str()));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    int64_t imin = min;
    int64_t imax = max;
    while(imin < imax)
    {
        int64_t imid = (imax / 2) + (imin / 2) + (((imax % 2) + (imin % 2)) / 2);
        auto imidstr = std::to_string(imid);

        if (imid >= 0)
        {
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
        else
        {
            s.push();

            z3::expr_vector chks(s.ctx());
            chks.push_back(e > s.ctx().int_val(imidstr.c_str()));
            auto rr = s.check(chks);

            s.pop();

            if(rr == z3::check_result::sat)
            {
                imin = imid;
            }
            else if(rr == z3::check_result::unsat)
            {
                imax = imid - 1;
            }
            else
            {
                return std::nullopt;
            }
        }
    }

    return std::make_optional(imin);
}

std::optional<double> realBinSearch(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, const std::vector<double>& copts)
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    for(size_t i = 0; i < copts.size(); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string rrstr = std::to_string(copts[i]);
        chks.push_back(e == s.ctx().real_val(rrstr.c_str()));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    double epsilon = 0.000000001;
    double rmin = std::numeric_limits<float>::lowest();
    double rmax = std::numeric_limits<float>::max();
    while(epsilon < (rmax - rmin))
    {
        double rmid = (rmax + rmin) / 2.0;
        auto rmidstr = std::to_string(rmid);

        if (rmid >= 0.0)
        {
            s.push();

            z3::expr_vector chks(s.ctx());
            chks.push_back(e < s.ctx().real_val(rmidstr.c_str()));
            auto rr = s.check(chks);

            s.pop();

            if(rr == z3::check_result::sat)
            {
                rmax = rmid;
            }
            else if(rr == z3::check_result::unsat)
            {
                rmin = rmid + 1;
            }
            else
            {
                return std::nullopt;
            }
        }
        else
        {
            s.push();

            z3::expr_vector chks(s.ctx());
            chks.push_back(e > s.ctx().real_val(rmidstr.c_str()));
            auto rr = s.check(chks);

            s.pop();

            if(rr == z3::check_result::sat)
            {
                rmin = rmid;
            }
            else if(rr == z3::check_result::unsat)
            {
                rmax = rmid - 1;
            }
            else
            {
                return std::nullopt;
            }
        }
    }

    return std::make_optional(rmin);
}

z3::func_decl getArgContextConstructor(const APIModule* apimodule, z3::context& c, const char* fname, const z3::sort& ressort)
{
    auto nsort = c.bv_sort(apimodule->bv_width);
    auto ccsort = c.seq_sort(nsort);

    auto argconsf = c.function(fname, ccsort, ressort);

    return argconsf;
}

z3::expr genInitialContextArg(const APIModule* apimodule, z3::context& c)
{
    auto ii = c.bv_val((uint64_t)0, apimodule->bv_width);
    return ii.unit();
}

z3::expr genInitialContextResult(const APIModule* apimodule, z3::context& c)
{
    auto ii = c.bv_val((uint64_t)1, apimodule->bv_width);
    return ii.unit();
}

z3::expr extendContext(const APIModule* apimodule, z3::context& c, const z3::expr& ctx, size_t i)
{
    auto ii = c.bv_val((uint64_t)i, apimodule->bv_width);
    return z3::concat(ctx, ii.unit());
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

std::string hextobin(const std::string& hex)
{
    std::string res;
    for(size_t i = 0; i < hex.size(); ++i)
    {
        switch(hex[i])
        {
        case '0':
            res += "0000";
            break;
        case '1':
            res += "0001";
            break;
        case '2':
            res += "0010";
            break;
        case '3':
            res += "0011";
            break;
        case '4':
            res += "0100";
            break;
        case '5':
            res += "0101";
            break;
        case '6':
            res += "0110";
            break;
        case '7':
            res += "0111";
            break;
        case '8':
            res += "1000";
            break;
        case '9':
            res += "1001";
            break;
        case 'a':
            res += "1010";
            break;
        case 'b':
            res += "1011";
            break;
        case 'c':
            res += "1100";
            break;
        case 'd':
            res += "1101";
            break;
        case 'e':
            res += "1110";
            break;
        case 'f':
            res += "1111";
            break;
        default:
            assert(false);
            break;
        }
    }

    return res;
}

int64_t getsignfactor(const std::string& bits)
{
    return (bits[0] == '1' ? -1 : 0);
}

std::string getmagnitude(const std::string& bits)
{
    return bits.substr(1);
}

int64_t signValue(const std::string& bits)
{
    int64_t factor = getsignfactor(bits);
    int64_t mag = std::exp2(bits.size() - 1);

    return factor * mag;
}

uint64_t magnitudeValue(const std::string& bits)
{
    uint64_t res = bits[bits.size() - 1] == '1' ? 1 : 0;
    uint64_t pow = 2;

    for(int64_t i = bits.size() - 2; i >= 0; --i)
    {
        res += (bits[i] == '1' ? 1 : 0) * pow;
        pow = pow * 2;
    }

    return res;
}

uint64_t bitsToUInt(const std::string& bits)
{
    return magnitudeValue(bits);
}

uint64_t hexToUInt(const std::string& hex)
{
    auto bits = hextobin(hex);
    return bitsToUInt(bits);
}

int64_t bitsToInt(const std::string& bits)
{
    int64_t signv = signValue(bits);
    int64_t magv = (int64_t)magnitudeValue(getmagnitude(bits));

    return signv + magv;
}

int64_t hexToInt(const std::string& hex)
{
    auto bits = hextobin(hex);
    return bitsToInt(bits);
}

std::optional<uint64_t> ExtractionInfo::expBVAsUInt(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto bbval = m.eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_bv_binary))
    {
        auto bits = strval.substr(2);
        auto uval = bitsToUInt(bits);
        
        auto ustr = std::to_string(uval);
        s.add(e == s.ctx().bv_val(ustr.c_str(), this->apimodule->bv_width));

        return std::make_optional(uval);
    }
    else if(std::regex_match(strval, re_bv_hex))
    {
        auto bits = strval.substr(2);
        auto uval = hexToUInt(bits);
        
        auto ustr = std::to_string(uval);
        s.add(e == s.ctx().bv_val(ustr.c_str(), this->apimodule->bv_width));

        return std::make_optional(uval);
    }
    else
    {
        auto uval = bvBinSearchUnsigned(this->apimodule, s, m, e, 0, computeBVMaxUnSigned(this->apimodule->bv_width), {0, 1, 3});
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
        auto ival = bitsToInt(bits);

        auto istr = std::to_string(ival);
        s.add(e == s.ctx().bv_val(istr.c_str(), this->apimodule->bv_width));

        return std::make_optional(ival);
    }
    else if(std::regex_match(strval, re_bv_hex))
    {
        auto bits = strval.substr(2);
        auto ival = hexToInt(bits);

        auto istr = std::to_string(ival);
        s.add(e == s.ctx().bv_val(istr.c_str(), this->apimodule->bv_width));

        return std::make_optional(ival);
    }
    else
    {
        auto ival = bvBinSearchSigned(this->apimodule, s, m, e, computeBVMinSigned(this->apimodule->bv_width), computeBVMaxSigned(this->apimodule->bv_width), {0, 1, 3, -1, -3});
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
        s.add(e == s.ctx().real_val(strval.c_str()));

        return std::make_optional(strval);
    }
    else
    {
        auto ival = intBinSearchUnsigned(this->apimodule, s, m, e, 0, std::numeric_limits<int64_t>::max(), {0, 1, 3});
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
        auto ival = intBinSearchSigned(this->apimodule, s, m, e, std::numeric_limits<int64_t>::lowest(), std::numeric_limits<int64_t>::max(), {0, 1, 3, -1, -3});
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
    else if(std::regex_match(sstr, re_fpdiverino))
    {
        double num = std::stod(match[1].str());
        double denom = std::stod(match[3].str());

        auto sstr = std::to_string(num / denom);
        return std::make_optional(sstr);
    }
    else
    {
        auto rval = realBinSearch(this->apimodule, s, m, e, {0.0, 1.0, 3.0, -1.0, -3.0});
        if(!rval.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        auto rstr = std::to_string(rval.value());
        s.add(e == s.ctx().real_val(rstr.c_str()));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return std::make_optional(rstr);
    }
}

std::optional<std::string> ExtractionInfo::evalStringAsString(z3::solver& s, z3::model& m, const z3::expr& e) const
{
    auto nexp = m.eval(e, true);
    auto sstr = nexp.to_string();

    if(sstr.length() >= 2 && sstr[0] == '"' && sstr[sstr.length() - 1] == '"')
    {
        s.add(e == s.ctx().string_val(sstr.c_str()));

        return std::make_optional(sstr);
    }
    else
    {
        //TODO: need to bin search string
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
    return this->evalStringAsString(s, m, e);
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

    std::uniform_int_distribution<size_t> cchoice(0, printascii + nullchar);
    auto cval = cchoice(rnd);

    std::string data;
    if(cval <= printascii)
    {
        data.append({ (char)(32 + cval) });
    }
    else
    {
        data.append({ '\0' });
    }

    return data;
}

BSQRegexOpt* BSQRegexOpt::parse(json j)
{
    auto tag = j["tag"].get<std::string>();
    if(tag == "Literal")
    {
        return BSQLiteralRe::parse(j);
    }
    else if(tag == "CharClass")
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

std::string BSQLiteralRe::generate(RandGenerator& rnd, FuzzInfo& finfo) const
{
    return this->escstr;
}

BSQLiteralRe* BSQLiteralRe::parse(json j)
{
    auto litstr = j["litstr"].get<std::string>();
    std::vector<uint8_t> utf8;
    std::transform(litstr.cbegin(), litstr.cend(), std::back_inserter(utf8), [](const char cc) {
        return (uint8_t)cc;
    });

    return new BSQLiteralRe(j["restr"].get<std::string>(), j["escstr"].get<std::string>(), utf8);
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
    return new NoneType();
}

json NoneType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    return nullptr;
}

 bool NoneType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
 {
    return j.is_null();
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

std::optional<json> NoneType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return std::make_optional(nullptr);
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

 bool BoolType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
 {
     if(!j.is_boolean())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BBool@UFCons_API", c.bool_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.bool_val(j.get<bool>()));

    return true;
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

std::optional<json> BoolType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBool@UFCons_API", m.ctx().bool_sort());
    return ex.evalToBool(s, m, bef(ctx));
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

bool NatType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    std::optional<uint64_t> nval = pinfo.parseToUnsignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BNat@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(bef(ctx) == c.bv_val(nval.value(), pinfo.apimodule->bv_width));

    return true;
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

std::optional<json> NatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BNat@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
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

bool IntType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    std::optional<int64_t> nval = pinfo.parseToSignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BInt@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(bef(ctx) == c.bv_val(nval.value(), pinfo.apimodule->bv_width));

    return true;
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

std::optional<json> IntType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BInt@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToSignedNumber(s, m, bef(ctx));
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

bool BigNatType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BBigNat@UFCons_API", c.int_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.int_val(nval.value().c_str()));

    return true;
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

std::optional<json> BigNatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBigNat@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
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

bool BigIntType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigSignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BBigInt@UFCons_API", c.int_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.int_val(nval.value().c_str()));

    return true;
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

std::optional<json> BigIntType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBigInt@UFCons_API", m.ctx().int_sort());
    return ex.evalToSignedNumber(s, m, bef(ctx));
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
        const BigIntType* numtype = (const BigIntType*)finfo.apimodule->typemap.find("NSCore::BigInt")->second;
        const NatType* denomtype = (const NatType*)finfo.apimodule->typemap.find("NSCore::Nat")->second;

        json num = numtype->fuzz(finfo, rnd);
        json denom = denomtype->fuzz(finfo, rnd);

        res = { num, denom };

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

bool RationalType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_array())
    {
        return false;
    }

    //const BigIntType* numtype = (const BigIntType*)pinfo.apimodule->typemap.find("NSCore::BigInt")->second;
    //const NatType* denomtype = (const NatType*)pinfo.apimodule->typemap.find("NSCore::Nat")->second;

    assert(false);
    return false;
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

std::optional<json> RationalType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    //const BigIntType* numtype = (const BigIntType*)pinfo.apimodule->typemap.find("NSCore::BigInt")->second;
    //const NatType* denomtype = (const NatType*)pinfo.apimodule->typemap.find("NSCore::Nat")->second;

    assert(false);
    return nullptr;
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

bool FloatType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto fval = pinfo.parseToRealNumber(j);
    if(!fval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BFloat@UFCons_API", c.real_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.real_val(fval.value().c_str()));

    return true;
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

std::optional<json> FloatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BFloat@UFCons_API", m.ctx().real_sort());
    return ex.evalToRealNumber(s, m, bef(ctx));
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

bool DecimalType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto fval = pinfo.parseToDecimalNumber(j);
    if(!fval.has_value())
    {
        return false;
    }
        
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BDecimal@UFCons_API", c.real_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.real_val(fval.value().c_str()));
    
    return true;
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

std::optional<json> DecimalType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BDecimal@UFCons_API", m.ctx().real_sort());
    return ex.evalToDecimalNumber(s, m, bef(ctx));
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

bool StringType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_string())
    {
        return false;
    }
        
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BString@UFCons_API", c.string_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.string_val(j.get<std::string>().c_str()));
    
    return true;
}

std::optional<std::string> StringType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return std::make_optional("\"" + j.get<std::string>() + "\"");
}

std::optional<json> StringType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BString@UFCons_API", m.ctx().string_sort());
    return ex.evalToString(s, m, bef(ctx));
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

bool StringOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, ectx, c);
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

std::optional<json> StringOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find("NSCore::String")->second->z3extract(ex, ectx, s, m);
}

NumberOfType* NumberOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto primitive = j["primitive"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    return new NumberOfType(name, primitive, oftype);
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

bool NumberOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->primitive)->second->toz3arg(pinfo, j, ectx, c);
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

std::optional<json> NumberOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->primitive)->second->z3extract(ex, ectx, s, m);
}

DataStringType* DataStringType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto isvalue = j["isvalue"].get<bool>();

    return new DataStringType(name, oftype, isvalue);
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

bool DataStringType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, ectx, c);
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

std::optional<json> DataStringType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find("NSCore::String")->second->z3extract(ex, ectx, s, m);
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

bool ByteBufferType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<std::string> ByteBufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> ByteBufferType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
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

bool BufferType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<std::string> BufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> BufferType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
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

bool DataBufferType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<std::string> DataBufferType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> DataBufferType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
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

bool ISOTimeType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    //TODO: see std::get_time here I think
    assert(false);
    return false;
}

std::optional<std::string> ISOTimeType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    return j.get<std::string>();
}

std::optional<json> ISOTimeType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BISOTime@UFCons_API", m.ctx().int_sort());
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

bool LogicalTimeType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    std::optional<std::string> nval = pinfo.parseToBigUnsignedNumber(j);
    if(!nval.has_value())
    {
        return false;
    }
    
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BLogicalTime@UFCons_API", c.int_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.int_val(nval.value().c_str()));

    return true;
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

std::optional<json> LogicalTimeType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BLogicalTime@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

UUIDType* UUIDType::jparse(json j)
{
    return new UUIDType();
}

json UUIDType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

bool UUIDType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<std::string> UUIDType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> UUIDType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

ContentHashType* ContentHashType::jparse(json j)
{
    return new ContentHashType();
}

json ContentHashType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    assert(false);
    return nullptr;
}

bool ContentHashType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<std::string> ContentHashType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    assert(false);
    return std::nullopt;
}

std::optional<json> ContentHashType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
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
        auto ttype = finfo.apimodule->typemap.find(tt)->second;
        return ttype->fuzz(finfo, rnd);
    });
    return jres;
}

bool TupleType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_array() || this->ttypes.size() != j.size())
    {
        return false;
    }

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ectx = extendContext(pinfo.apimodule, c, ctx, i);
        
        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->toz3arg(pinfo, j[i], ectx, c);
        if(!pexpr)
        {
            return false;
        }
    }


    return true;
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

std::optional<json> TupleType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::array();
    for(size_t i = 0; i < this->ttypes.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = extendContext(ex.apimodule, m.ctx(), ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        auto rr = ttype->z3extract(ex, idxval, s, m);
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

    return new RecordType(name, isvalue, props, ttypes);
}

json RecordType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        auto ttype = finfo.apimodule->typemap.find(this->ttypes[i])->second;
        return jres[this->props[i]] = ttype->fuzz(finfo, rnd);
    }
    return jres;
}

bool RecordType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_object() || this->props.size() != j.size())
    {
        return false;
    }

    auto allprops = std::all_of(this->props.cbegin(), this->props.cend(), [&j](const std::string& prop){
                return j.contains(prop);
            });
    if(!allprops)
    {
        return false;
    }

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ectx = extendContext(pinfo.apimodule, c, ctx, i);

        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->toz3arg(pinfo, j[this->props[i]], ectx, c);
        if(!pexpr)
        {
            return false;
        }
    }

    return true;
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

std::optional<json> RecordType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->props.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = extendContext(ex.apimodule, m.ctx(), ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        auto rr = ttype->z3extract(ex, idxval, s, m);
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
    auto oftype = j["oftype"].get<std::string>();

    return new ListType(name, oftype);
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

bool ListType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_array())
    {
        return false;
    }

    auto lef = getArgContextConstructor(pinfo.apimodule, c, "ListSize@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(lef(ctx) == c.bv_val((uint64_t)j.size(), pinfo.apimodule->bv_width));

    auto ttype = pinfo.apimodule->typemap.find(this->oftype)->second;

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < j.size(); ++i)
    {
        auto ectx = extendContext(pinfo.apimodule, c, ctx, i);
        auto pexpr = ttype->toz3arg(pinfo, j[i], ectx, c);
        if(!pexpr)
        {
            return false;
        }
    }

    return true;
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

std::optional<json> ListType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::array();

    auto lef = getArgContextConstructor(ex.apimodule, m.ctx(), "ListSize@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto lenval = ex.bvToCardinality(s, m, lef(ctx));
    if(!lenval.has_value())
    {
        return std::nullopt;
    }

    auto ttype = ex.apimodule->typemap.find(this->oftype)->second;

    for(size_t i = 0; i < lenval.value(); ++i)
    {
        auto idxval = extendContext(ex.apimodule, m.ctx(), ctx, i);
        auto rr = ttype->z3extract(ex, idxval, s, m);
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
    std::vector<std::string> enuminvs;
    auto jenuminvs = j["enuminvs"];
    std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enuminvs), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new EnumType(j["name"].get<std::string>(), j["underlying"].get<std::string>(), enuminvs);
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

        res = this->enuminvs[opt];

        finfo.addReuseForType(this->name, res);
        return res;
    }
}

bool EnumType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_string())
    {
        return false;
    }
    
    std::string enumchoice = j.get<std::string>();
    auto pos = std::find_if(this->enuminvs.cbegin(), this->enuminvs.cend(), [&enumchoice](const std::string& cname) {
        return cname == enumchoice;
    });

    if(pos == this->enuminvs.cend())
    {
        return false;
    }
    auto idx = std::distance(pos, this->enuminvs.cend());

    auto lef = getArgContextConstructor(pinfo.apimodule, c, "EnumChoice@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(lef(ctx) == c.bv_val((uint64_t)idx, pinfo.apimodule->bv_width));

    return true;
}

std::optional<std::string> EnumType::tobsqarg(const ParseInfo& pinfo, json j, const std::string& indent) const
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
        
    return j.get<std::string>();
}

std::optional<json> EnumType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto lef = getArgContextConstructor(ex.apimodule, m.ctx(), "EnumChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto lenval = ex.bvToCardinality(s, m, lef(ctx));
    if(!lenval.has_value())
    {
        return std::nullopt;
    }

    if(lenval.value() >= this->enuminvs.size())
    {
        return std::nullopt;
    }

    return std::make_optional(this->enuminvs[lenval.value()]);
}

UnionType* UnionType::jparse(json j)
{
    auto name = j["name"].get<std::string>();

    std::vector<std::string> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new UnionType(name, opts);
}

json UnionType::fuzz(FuzzInfo& finfo, RandGenerator& rnd) const
{
    std::uniform_int_distribution<uint64_t> distribution(0, this->opts.size() - 1);
    auto i = distribution(rnd);

    auto otype = finfo.apimodule->typemap.find(this->opts[i])->second;
    return otype->fuzz(finfo, rnd);
}

bool UnionType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        z3::expr_vector optv(c);
        pinfo.chks.push(&optv);
        auto ttype = dynamic_cast<const IGroundedType*>(pinfo.apimodule->typemap.find(this->opts[i])->second);

        auto ectx = extendContext(pinfo.apimodule, c, ctx, i);
        auto pexpr = ttype->toz3arg(pinfo, j, ectx, c);
        if(pexpr)
        {
            pinfo.chks.pop();
            for(auto iter = optv.begin(); iter != optv.end(); ++iter)
            {
                pinfo.chks.top()->push_back(*iter);
            }

            auto lef = getArgContextConstructor(pinfo.apimodule, c, "EnumChoice@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
            pinfo.chks.top()->push_back(lef(ctx) == c.bv_val((uint64_t)i, pinfo.apimodule->bv_width));

            return true;
        }

        pinfo.chks.pop();
    }

    return false;
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

std::optional<json> UnionType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "UnionChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto choice = ex.bvToCardinality(s, m, bef(ctx));
    if(!choice.has_value())
    {
        return std::nullopt;
    }

    if(choice.value() >= this->opts.size())
    {
        return std::nullopt;
    }

    auto ttype = dynamic_cast<const IGroundedType*>(ex.apimodule->typemap.find(this->opts[choice.value()])->second);
    auto ectx = extendContext(ex.apimodule, m.ctx(), ctx, choice.value());

    return ttype->z3extract(ex, ectx, s, m);
}

InvokeSignature* InvokeSignature::jparse(json j, const std::map<std::string, const IType*>& typemap)
{
    auto name = j["name"].get<std::string>();
    auto restype = typemap.find(j["restype"].get<std::string>())->second;

    std::vector<std::string> argnames;
    auto jargnames = j["argnames"];
    std::transform(jargnames.cbegin(), jargnames.cend(), std::back_inserter(argnames), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<const IType*> argtypes;
    auto jargtypes = j["argtypes"];
    std::transform(jargtypes.cbegin(), jargtypes.cend(), std::back_inserter(argtypes), [&typemap](const json& jv) {
        return typemap.find(jv.get<std::string>())->second;
    });

    return new InvokeSignature(name, restype, argnames, argtypes);
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