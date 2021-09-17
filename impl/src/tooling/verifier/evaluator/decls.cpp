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

std::optional<char> stringBinSearchCharASCII(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, const std::string& str, size_t cidx)
{
    char copts[] = {'z', 'A', '0', ' ', '3', '!', '\0'};

    for(size_t i = 0; i < sizeof(copts); ++i)
    {
        s.push();

        z3::expr_vector chks(s.ctx());
        std::string iistr = str + copts[i];

        chks.push_back(e == s.ctx().string_val(iistr));
        auto rr = s.check(chks);

        s.pop();

        if(rr == z3::check_result::sat)
        {
            return std::make_optional(copts[i]);
        }
    }

    uint64_t cmin = 32;
    uint64_t cmax = 126;
    while(cmin < cmax)
    {
        uint64_t cmid = (cmax / 2) + (cmin / 2) + (((cmax % 2) + (cmin % 2)) / 2);
        std::string imidstr = str + (char)cmid;

        s.push();

        z3::expr_vector chks(s.ctx());
        chks.push_back(e.extract(s.ctx().int_val(0), s.ctx().int_val(cidx + 1)) < s.ctx().string_val(imidstr));
        auto rr = s.check(chks);

        s.pop();
        
        if(rr == z3::check_result::sat) 
        {
            cmax = cmid;
        }
        else if(rr == z3::check_result::unsat) 
        {
            cmin = cmid + 1;
        }
        else
        {
            return std::nullopt;
        }
    }

    return std::make_optional(cmin);
}

std::optional<std::string> stringBinSearchContentsASCII(const APIModule* apimodule, z3::solver& s, const z3::model& m, const z3::expr& e, size_t slen)
{
    if(slen == 0) {
        return std::make_optional(std::string(""));
    }

    std::string rstr("");
    for(size_t i = 0; i < slen; ++i)
    {
        auto nchar = stringBinSearchCharASCII(apimodule, s, m, e, rstr, i);
        if(!nchar.has_value())
        {
            return std::nullopt;
        }

        rstr += nchar.value();
    }

    return std::make_optional(rstr);
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
        s.add(e == s.ctx().string_val(sstr));

        return std::make_optional(sstr);
    }
    else
    {
        auto slen = this->evalToUnsignedNumber(s, m, e.length());
        if(!slen.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        auto rstr = stringBinSearchContentsASCII(this->apimodule, s, m, e, slen.value());
        if(!rstr.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        s.add(e == s.ctx().string_val(rstr.value()));

        auto refinechk = s.check();
        if(refinechk != z3::check_result::sat)
        {
            return std::nullopt;
        }
        m = s.get_model();

        return sstr;
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

IType* IType::jparse(json j)
{
    switch(j["tag"].get<TypeTag>())
    {
        case TypeTag::NoneTag:
            return NoneType::jparse(j);
        case TypeTag::NothingTag:
            return NothingType::jparse(j);
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
        case TypeTag::PrimitiveOfTag:
            return PrimitiveOfType::jparse(j);
        case TypeTag::DataStringTag:
            return DataStringType::jparse(j);
        case TypeTag::ByteBufferTag:
            return ByteBufferType::jparse(j);
        case TypeTag::BufferOfTag:
            return BufferOfType::jparse(j);
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
        case TypeTag::SomethingTag:
            return SomethingType::jparse(j);
        case TypeTag::OkTag:
            return OkType::jparse(j);
        case TypeTag::ErrTag:
            return ErrType::jparse(j);
        case TypeTag::ListTag:
            return ListType::jparse(j);
        case TypeTag::StackTag:
            return StackType::jparse(j);
        case TypeTag::QueueTag:
            return QueueType::jparse(j);
        case TypeTag::SetTag:
            return SetType::jparse(j);
        case TypeTag::MapTag:
            return MapType::jparse(j);
        case TypeTag::EnumTag:
            return EnumType::jparse(j);
        case TypeTag::EntityTag:
            return EntityType::jparse(j);
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

bool NoneType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    return j.is_null();
}

std::optional<json> NoneType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return std::make_optional(nullptr);
}

NothingType* NothingType::jparse(json j)
{
    return new NothingType();
}

bool NothingType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    return j.is_null();
}

std::optional<json> NothingType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    return std::make_optional(nullptr);
}

BoolType* BoolType::jparse(json j)
{
    return new BoolType();
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

std::optional<json> BoolType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBool@UFCons_API", m.ctx().bool_sort());
    return ex.evalToBool(s, m, bef(ctx));
}

NatType* NatType::jparse(json j)
{
    return new NatType();
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

std::optional<json> NatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BNat@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

IntType* IntType::jparse(json j)
{
    return new IntType();
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

std::optional<json> IntType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BInt@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    return ex.evalToSignedNumber(s, m, bef(ctx));
}

BigNatType* BigNatType::jparse(json j)
{
    return new BigNatType();
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

std::optional<json> BigNatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBigNat@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

BigIntType* BigIntType::jparse(json j)
{
    return new BigIntType();
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

std::optional<json> BigIntType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BBigInt@UFCons_API", m.ctx().int_sort());
    return ex.evalToSignedNumber(s, m, bef(ctx));
}

RationalType* RationalType::jparse(json j)
{
    return new RationalType();
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

std::optional<json> RationalType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return std::nullopt;
}

FloatType* FloatType::jparse(json j)
{
    return new FloatType();
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

std::optional<json> FloatType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BFloat@UFCons_API", m.ctx().real_sort());
    return ex.evalToRealNumber(s, m, bef(ctx));
}

DecimalType* DecimalType::jparse(json j)
{
    return new DecimalType();
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

std::optional<json> DecimalType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BDecimal@UFCons_API", m.ctx().real_sort());
    return ex.evalToDecimalNumber(s, m, bef(ctx));
}

StringType* StringType::jparse(json j)
{
    return new StringType();
}

bool StringType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_string())
    {
        return false;
    }
        
    auto bef = getArgContextConstructor(pinfo.apimodule, c, "BString@UFCons_API", c.string_sort());
    pinfo.chks.top()->push_back(bef(ctx) == c.string_val(j.get<std::string>()));
    
    return true;
}

std::optional<json> StringType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BString@UFCons_API", m.ctx().string_sort());
    return ex.evalToString(s, m, bef(ctx));
}

PrimitiveOfType* PrimitiveOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    return new PrimitiveOfType(name, oftype);
}

bool PrimitiveOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->oftype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> PrimitiveOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->oftype)->second->z3extract(ex, ectx, s, m);
}

StringOfType* StringOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto validator = j["validator"].get<std::string>();

    return new StringOfType(name, validator);
}

bool StringOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> StringOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find("NSCore::String")->second->z3extract(ex, ectx, s, m);
}

DataStringType* DataStringType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();

    return new DataStringType(name, oftype);
}

bool DataStringType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find("NSCore::String")->second->toz3arg(pinfo, j, ectx, c);
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

bool ByteBufferType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<json> ByteBufferType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

BufferOfType* BufferOfType::jparse(json j)
{
    assert(false);
    return nullptr;
}

bool BufferOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<json> BufferOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

DataBufferType* DataBufferType::jparse(json j)
{
    assert(false);
    return nullptr;
}

bool DataBufferType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
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

bool ISOTimeType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    //TODO: see std::get_time here I think
    assert(false);
    return false;
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

std::optional<json> LogicalTimeType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "BLogicalTime@UFCons_API", m.ctx().int_sort());
    return ex.evalToUnsignedNumber(s, m, bef(ctx));
}

UUIDType* UUIDType::jparse(json j)
{
    return new UUIDType();
}

bool UUIDType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
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

bool ContentHashType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    assert(false);
    return false;
}

std::optional<json> ContentHashType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    assert(false);
    return nullptr;
}

xxxx;

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