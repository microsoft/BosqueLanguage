//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "args.h"

static std::regex re_numberino_n("^[+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_i("^[-+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_f("^[-+]?([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?$");
static std::regex re_numberino_negf("^[(]- ([0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?[)]$");

std::optional<uint64_t> intBinSearchUnsigned(z3::solver& s, const z3::expr& e, uint64_t min, uint64_t max, const std::vector<uint64_t>& copts)
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

std::optional<int64_t> intBinSearchSigned(z3::solver& s, const z3::expr& e, int64_t min, int64_t max, const std::vector<int64_t>& copts)
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

std::optional<double> realBinSearch(z3::solver& s, const z3::expr& e, const std::vector<double>& copts)
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


std::optional<char> stringBinSearchCharASCII(z3::solver& s, const z3::expr& e, const std::string& str, size_t cidx)
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

    uint16_t cmin = 32;
    uint16_t cmax = 126;
    while(cmin < cmax)
    {
        uint16_t cmid = (cmax / 2) + (cmin / 2) + (((cmax % 2) + (cmin % 2)) / 2);
        std::string imidstr = str + (char)cmid;

        s.push();

        z3::expr_vector chks(s.ctx());
        chks.push_back(e.extract(s.ctx().int_val(0), s.ctx().int_val((uint64_t)cidx + 1)) < s.ctx().string_val(imidstr));
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

    return std::make_optional((char)cmin);
}

std::optional<std::string> stringBinSearchContentsASCII(z3::solver& s, const z3::expr& e, size_t slen)
{
    if(slen == 0) {
        return std::make_optional(std::string(""));
    }

    std::string rstr("");
    for(size_t i = 0; i < slen; ++i)
    {
        auto nchar = stringBinSearchCharASCII(s, e, rstr, i);
        if(!nchar.has_value())
        {
            return std::nullopt;
        }

        rstr += nchar.value();
    }

    return std::make_optional(rstr);
}

std::optional<bool> expBoolAsBool(z3::solver& s, const z3::expr& e)
{
    auto bbval = s.get_model().eval(e, true);
    auto strval = bbval.to_string();

    if(strval == "true") 
    {
        return std::make_optional(true);
    }
    else if(strval == "false")
    {
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

        return res;
    }
}

std::optional<std::string> expIntAsUInt(z3::solver& s, const z3::expr& e)
{
    auto bbval = s.get_model().eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_numberino_n))
    {
        return std::make_optional(strval);
    }
    else
    {
        auto ival = intBinSearchUnsigned(s, e, 0, std::numeric_limits<uint64_t>::max(), {0, 1, 3});
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

        return std::make_optional(istr);
    }
}

std::optional<uint64_t> expIntAsUIntSmall(z3::solver& s, const z3::expr& e)
{
    auto pv = expIntAsUInt(s, e);
    if(!pv.has_value())
    {
        return std::nullopt;
    }
    else
    {
        try
        {
            return std::make_optional(std::stoull(pv.value()));
        }
        catch(...)
        {
            ;
        }

        return std::nullopt;
    }
}

std::optional<std::string> expIntAsInt(z3::solver& s, const z3::expr& e)
{
    auto bbval = s.get_model().eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_numberino_i))
    {
        return std::make_optional(strval);
    }
    else
    {
        //
        //TODO: we are limited here to 64 bit ints -- need to extend to a true big int search when we have the library support 
        //
        auto ival = intBinSearchSigned(s, e, std::numeric_limits<int64_t>::lowest(), std::numeric_limits<int64_t>::max(), {0, 1, 3, -1, -3});
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

        return std::make_optional(istr);
    }
}

std::optional<std::string> expFloatAsFloat(z3::solver& s, const z3::expr& e)
{
    auto bbval = s.get_model().eval(e, true);
    auto strval = bbval.to_string();

    std::cmatch match;
    if(std::regex_match(strval, re_numberino_f))
    {
        return std::make_optional(strval);
    }
    else if(std::regex_match(strval, re_numberino_negf))
    {
        return std::make_optional("-" + strval.substr(3, strval.size() - 4));
    }
    else
    {
        //We seem to have a bug here where asserting == on the real values is not coming back unsat when the formula is unsat
        assert(false);

        auto ival = realBinSearch(s, e, {0.0, 1.0, 3.0, -1.0, -3.0});
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

        return std::make_optional(istr);
    }
}

std::optional<int64_t> expIntAsIntSmall(z3::solver& s, const z3::expr& e)
{
    auto pv = expIntAsInt(s, e);
    if(!pv.has_value())
    {
        return std::nullopt;
    }
    else
    {
        try
        {
            return std::make_optional(std::stoll(pv.value()));
        }
        catch(...)
        {
            ;
        }

        return std::nullopt;
    }
}

std::optional<std::string> evalStringAsString(z3::solver& s, const z3::expr& e)
{
    auto nexp = s.get_model().eval(e, true);
    auto sstr = nexp.to_string();

    if(sstr.length() >= 2 && sstr[0] == '"' && sstr[sstr.length() - 1] == '"')
    {
        return std::make_optional(sstr);
    }
    else
    {
        auto slenstropt = expIntAsUInt(s, e.length());
        if(!slenstropt.has_value())
        {
            assert(false);
            return std::nullopt;
        }

        auto slenstr = slenstropt.value();
        auto slen = std::stoull(slenstr);
        auto rstr = stringBinSearchContentsASCII(s, e, slen);
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

        return sstr;
    }
}

z3::expr extendContext(z3::context& c, const z3::expr& ctx, size_t i)
{
    auto ii = c.int_val((uint64_t)i);
    return z3::concat(ctx, ii.unit());
}

z3::func_decl getArgContextConstructor(z3::context& c, const char* fname, const z3::sort& ressort)
{
    auto isort = c.int_sort();
    auto hsort = c.seq_sort(isort);
    auto argconsf = c.function(fname, hsort, ressort);

    return argconsf;
}

bool SMTParseJSON::checkInvokeOk(const std::string& checkinvoke, z3::expr value, z3::solver& ctx)
{
    ; //the call to the check is already set by the Havoc initializer
    return true;
}

bool SMTParseJSON::parseNoneImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //location is aleady zero initialized
    return true;
}

bool SMTParseJSON::parseNothingImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //location is aleady zero initialized
    return true;
}

bool SMTParseJSON::parseBoolImpl(const APIModule* apimodule, const IType* itype, bool b, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBool@UFCons_API", ctx.ctx().bool_sort());
    ctx.add(bef(value) == ctx.ctx().bool_val(b));

    return true;
}

bool SMTParseJSON::parseNatImpl(const APIModule* apimodule, const IType* itype, uint64_t n, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(n));

    return true;
}

bool SMTParseJSON::parseIntImpl(const APIModule* apimodule, const IType* itype, int64_t i, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BInt@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(i));

    return true;
}

bool SMTParseJSON::parseBigNatImpl(const APIModule* apimodule, const IType* itype, std::string n, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBigNat@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(n.c_str()));

    return true;
}

bool SMTParseJSON::parseBigIntImpl(const APIModule* apimodule, const IType* itype, std::string i, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBigNat@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(i.c_str()));

    return true;
}

bool SMTParseJSON::parseFloatImpl(const APIModule* apimodule, const IType* itype, std::string f, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BFloat@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    ctx.add(bef(value) == ctx.ctx().real_val(f.c_str()));

    return true;
}

bool SMTParseJSON::parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BDecimal@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    ctx.add(bef(value) == ctx.ctx().real_val(d.c_str()));

    return true;
}

bool SMTParseJSON::parseRationalImpl(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, z3::expr value, z3::solver& ctx)
{
    std::string rstr = "";
    if(n == "0")
    {
        rstr = "0.0";
    }
    else if(n == "1")
    {
        rstr = "1.0";
    }
    else
    {
        rstr = n + "/" + std::to_string(d);
    }

    auto bef = getArgContextConstructor(ctx.ctx(), "BRational@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    ctx.add(bef(value) == ctx.ctx().real_val(rstr.c_str()));

    return true;
}

bool SMTParseJSON::parseStringImpl(const APIModule* apimodule, const IType* itype, std::string s, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BString@UFCons_API", ctx.ctx().string_sort());
    ctx.add(bef(value) == ctx.ctx().string_val(s));

    return true;
}

bool SMTParseJSON::parseByteBufferImpl(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, z3::expr value, z3::solver& ctx)
{
    auto bytesort = ctx.ctx().bv_sort(8);

    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());
    auto bbf = getArgContextConstructor(ctx.ctx(), "BByteBuffer@UFCons_API", ctx.ctx().seq_sort(bytesort));

    auto ectxcc = extendContext(ctx.ctx(), value, 0);
    ctx.add(bef(ectxcc) == ctx.ctx().int_val(compress));

    auto ectxff = extendContext(ctx.ctx(), value, 1);
    ctx.add(bef(ectxff) == ctx.ctx().int_val(format));

    auto ectxbb = extendContext(ctx.ctx(), value, 2);
    ctx.add(bbf(ectxbb).length() == ctx.ctx().int_val((uint64_t)data.size()));
    for(size_t i = 0; i < data.size(); ++i)
    {
        ctx.add(bbf(ectxbb).at(ctx.ctx().int_val((uint64_t)i)) == ctx.ctx().bv_val((int)data[i], 8));
    }

    return true;
}

bool SMTParseJSON::parseDateTimeImpl(const APIModule* apimodule, const IType* itype, APIDateTime t, z3::expr value, z3::solver& ctx)
{
    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    ctx.add(byearf(value) == ctx.ctx().int_val(t.year));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bmonthf(value) == ctx.ctx().int_val(t.month));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bdayf(value) == ctx.ctx().int_val(t.day));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bhourf(value) == ctx.ctx().int_val(t.hour));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bminutef(value) == ctx.ctx().int_val(t.min));

    auto btzf = getArgContextConstructor(ctx.ctx(), "BDateTZName@UFCons_API", ctx.ctx().string_sort());
    ctx.add(btzf(value) == ctx.ctx().string_val(t.tzdata));

    return true;
}

bool SMTParseJSON::parseUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, APIUTCDateTime t, z3::expr value, z3::solver& ctx)
{
    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    ctx.add(byearf(value) == ctx.ctx().int_val(t.year));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bmonthf(value) == ctx.ctx().int_val(t.month));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bdayf(value) == ctx.ctx().int_val(t.day));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bhourf(value) == ctx.ctx().int_val(t.hour));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bminutef(value) == ctx.ctx().int_val(t.min));

    return true;
}

bool SMTParseJSON::parseCalendarDateImpl(const APIModule* apimodule, const IType* itype, APICalendarDate t, z3::expr value, z3::solver& ctx)
{
    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    ctx.add(byearf(value) == ctx.ctx().int_val(t.year));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bmonthf(value) == ctx.ctx().int_val(t.month));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bdayf(value) == ctx.ctx().int_val(t.day));

    return true;
}

bool SMTParseJSON::parseRelativeTimeImpl(const APIModule* apimodule, const IType* itype, APIRelativeTime t, z3::expr value, z3::solver& ctx)
{
    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bhourf(value) == ctx.ctx().int_val(t.hour));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bminutef(value) == ctx.ctx().int_val(t.min));

    return true;
}

bool SMTParseJSON::parseTickTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t t, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BTickTime@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(t));

    return true;
}

bool SMTParseJSON::parseLogicalTimeImpl(const APIModule* apimodule, const IType* itype, uint64_t j, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BLogicalTime@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(j));

    return true;
}

bool SMTParseJSON::parseISOTimeStampImpl(const APIModule* apimodule, const IType* itype, APIISOTimeStamp t, z3::expr value, z3::solver& ctx)
{
    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    ctx.add(byearf(value) == ctx.ctx().int_val(t.year));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bmonthf(value) == ctx.ctx().int_val(t.month));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bdayf(value) == ctx.ctx().int_val(t.day));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bhourf(value) == ctx.ctx().int_val(t.hour));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bminutef(value) == ctx.ctx().int_val(t.min));

    auto bsecondf = getArgContextConstructor(ctx.ctx(), "BDateSecond@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bsecondf(value) == ctx.ctx().int_val(t.min));

    auto bmillif = getArgContextConstructor(ctx.ctx(), "BDateMillis@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bmillif(value) == ctx.ctx().int_val(t.min));

    return true;
}

bool SMTParseJSON::parseUUID4Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().string_sort());

    unsigned int bb4 = (unsigned int)(*reinterpret_cast<const uint32_t*>(&v[0]));
    unsigned int bb2_1 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[4]));
    unsigned int bb2_2 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[6]));
    unsigned int bb2_3 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[8]));
    unsigned int bb6 = (unsigned int)(*reinterpret_cast<const uint64_t*>(&v[10]) & 0xFFFFFFFFFFFF);
    
    char sstrt[64] = {0};
    auto len = sprintf(sstrt, "%06x%04x%04x%04x%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + len);

    ctx.add(bbf(value).length() == ctx.ctx().string_const(res.c_str()));
    
    return true;
}

bool SMTParseJSON::parseUUID7Impl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().string_sort());

    unsigned int bb4 = (unsigned int)(*reinterpret_cast<const uint32_t*>(&v[0]));
    unsigned int bb2_1 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[4]));
    unsigned int bb2_2 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[6]));
    unsigned int bb2_3 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&v[8]));
    unsigned int bb6 = (unsigned int)(*reinterpret_cast<const uint64_t*>(&v[10]) & 0xFFFFFFFFFFFF);
    
    char sstrt[64] = {0};
    auto len = sprintf(sstrt, "%06x%04x%04x%04x%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + len);

    ctx.add(bbf(value).length() == ctx.ctx().string_const(res.c_str()));

    return true;
}

bool SMTParseJSON::parseSHAContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx)
{
    auto hashsort = ctx.ctx().bv_sort(16);
    auto bbf = getArgContextConstructor(ctx.ctx(), "BContentHash@UFCons_API", hashsort);

    auto hhpos = std::find_if(this->hashhash.cbegin(), this->hashhash.cend(), [&v](const std::vector<uint8_t>& hh) {
        return std::equal(hh.cbegin(), hh.cend(), v.cbegin());
    });

    uint16_t hhi = 0;
    if(hhpos != this->hashhash.cend())
    {
        hhi = (uint16_t)std::distance(this->hashhash.cbegin(), hhpos);
    }
    else
    {
        hhi = this->hashhash.size();
        this->hashhash.push_back(v);
    }

    ctx.add(bbf(value) == ctx.ctx().bv_val((int)hhi + 1, 16));

    return true;
}
    
bool SMTParseJSON::parseLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, float latitude, float longitude, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BFloat@UFCons_API", ctx.ctx().real_sort());

    auto latctx = extendContext(ctx.ctx(), value, 0);
    char latstr[16] = {0};
    auto lenlat = sprintf(latstr, "%1.9d", latitude);
    std::string latres(latstr, latstr + lenlat);
    ctx.add(bbf(latctx) == ctx.ctx().real_const(latres.c_str()));

    auto longctx = extendContext(ctx.ctx(), value, 1);
    char longstr[16] = {0};
    auto lenlong = sprintf(longstr, "%1.9d", longitude);
    std::string longres(longstr, longstr + lenlong);
    ctx.add(bbf(value) == ctx.ctx().real_const(longres.c_str()));
    
    return true;
}

void SMTParseJSON::prepareParseTuple(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::getValueForTupleIndex(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

void SMTParseJSON::completeParseTuple(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

void SMTParseJSON::prepareParseRecord(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::getValueForRecordProperty(const APIModule* apimodule, const IType* itype, z3::expr value, std::string pname, z3::solver& ctx)
{
    auto rtype = dynamic_cast<const RecordType*>(itype);
    auto ppos = std::find(rtype->props.cbegin(), rtype->props.cend(), pname);

    return extendContext(ctx.ctx(), value, std::distance(rtype->props.cbegin(), ppos));
}

void SMTParseJSON::completeParseRecord(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

void SMTParseJSON::prepareParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, size_t count, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "ContainerSize@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val((uint64_t)count));
}

z3::expr SMTParseJSON::getValueForContainerElementParse_T(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

std::pair<z3::expr, z3::expr> SMTParseJSON::getValueForContainerElementParse_KV(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    xxxx;
    return extendContext(ctx.ctx(), value, i);
}

void SMTParseJSON::completeParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

void SMTParseJSON::prepareParseEntity(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

void SMTParseJSON::prepareParseEntityMask(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::getValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::pair<std::string, std::string> fnamefkey, z3::solver& ctx)
{
    auto ootype = dynamic_cast<const EntityType*>(itype);
    auto ppos = std::find(ootype->consfields.cbegin(), ootype->consfields.cend(), fnamefkey);

    return extendContext(ctx.ctx(), extendContext(ctx.ctx(), value, 0), std::distance(ootype->consfields.cbegin(), ppos));
}

void SMTParseJSON::completeParseEntity(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ; //check calls are automatically introduced in the havoc call
}

void SMTParseJSON::setMaskFlag(const APIModule* apimodule, z3::expr flagloc, size_t i, bool flag, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBool@UFCons_API", ctx.ctx().bool_sort());
    return ctx.add(bef(extendContext(ctx.ctx(), extendContext(ctx.ctx(), flagloc, 1), i)) == ctx.ctx().bool_val(flag));
}

z3::expr SMTParseJSON::parseUnionChoice(const APIModule* apimodule, const IType* itype, z3::expr value, size_t pick, const IType* picktype, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "UnionChoice@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val((uint64_t)pick));

    return extendContext(ctx.ctx(), value, pick);
}

std::optional<bool> SMTParseJSON::extractBoolImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBool@UFCons_API", ctx.ctx().bool_sort());
    return expBoolAsBool(ctx, bef(value));
}

std::optional<uint64_t> SMTParseJSON::extractNatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}

std::optional<int64_t> SMTParseJSON::extractIntImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BInt@UFCons_API", ctx.ctx().int_sort());
    return expIntAsIntSmall(ctx, bef(value));
}

std::optional<std::string> SMTParseJSON::extractBigNatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBigNat@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUInt(ctx, bef(value));
}

std::optional<std::string> SMTParseJSON::extractBigIntImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BBigInt@UFCons_API", ctx.ctx().int_sort());
    return expIntAsInt(ctx, bef(value));
}

std::optional<std::string> SMTParseJSON::extractFloatImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BFloat@UFCons_API", ctx.ctx().real_sort());
    return expFloatAsFloat(ctx, bef(value));
}

std::optional<std::string> SMTParseJSON::extractDecimalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BDecimal@UFCons_API", ctx.ctx().real_sort());
    return expFloatAsFloat(ctx, bef(value));
}

std::optional<std::pair<std::string, uint64_t>> SMTParseJSON::extractRationalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //
    // TODO: need to convert to rational here
    //
    
    auto bef = getArgContextConstructor(ctx.ctx(), "BRational@UFCons_API", ctx.ctx().real_sort());
    return std::make_optional(std::make_pair("[RationalValue]", 1));
}

std::optional<std::string> SMTParseJSON::extractStringImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BString@UFCons_API", ctx.ctx().string_sort());
    return evalStringAsString(ctx, bef(value));
}

std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> SMTParseJSON::extractByteBufferImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bytesort = ctx.ctx().bv_sort(8);
    
    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());
    auto bbf = getArgContextConstructor(ctx.ctx(), "BByteBuffer@UFCons_API", ctx.ctx().seq_sort(bytesort));

    auto ectxcc = extendContext(ctx.ctx(), value, 0);
    auto compress = expIntAsUIntSmall(ctx, bef(ectxcc));

    auto ectxff = extendContext(ctx.ctx(), value, 1);
    auto format = expIntAsUIntSmall(ctx, bef(ectxff));

    auto ectxbb = extendContext(ctx.ctx(), value, 2);
    auto size = expIntAsUIntSmall(ctx, bbf(ectxbb).length());

    if(!compress.has_value() || !format.has_value() || !size.has_value())
    {
        return std::nullopt;
    }

    auto pprops = std::make_pair((uint8_t)compress.value(), (uint8_t)format.value());

    std::vector<uint8_t> bytes;
    bytes.reserve(size.value());

    for(size_t i = 0; i < size.value(); ++i)
    {
        auto vv = expIntAsUIntSmall(ctx, bbf(ectxbb).at(ctx.ctx().int_val((uint64_t)i)));
        if(!vv.has_value())
        {
            return std::nullopt;
        }

        bytes.push_back((uint8_t)vv.value());
    }

    return std::make_optional(std::make_pair(bytes, pprops));
}

std::optional<APIDateTime> SMTParseJSON::extractDateTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    APIDateTime dt;

    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    auto y = expIntAsUIntSmall(ctx, byearf(value));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    auto m = expIntAsUIntSmall(ctx, bmonthf(value));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    auto d = expIntAsUIntSmall(ctx, bdayf(value));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    auto h = expIntAsUIntSmall(ctx, bhourf(value));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    auto mm = expIntAsUIntSmall(ctx, bminutef(value));
        
    if(!y.has_value() || !m.has_value() || !d.has_value() || !h.has_value() || !mm.has_value())
    {
        return std::nullopt;
    }

    dt.year = (uint16_t)y.value();
    dt.month = (uint8_t)m.value();
    dt.day = (uint8_t)d.value();
    dt.hour = (uint8_t)h.value();
    dt.min = (uint8_t)mm.value();

    auto btzf = getArgContextConstructor(ctx.ctx(), "BDateTZName@UFCons_API", ctx.ctx().string_sort());
    auto tzo = evalStringAsString(ctx, btzf(value));
    
    if(!tzo.has_value())
    {
        return std::nullopt;
    }

    auto rpp = APIModule::s_tzdata.insert(tzo.value()).first;
    dt.tzdata = rpp->c_str();

    return std::make_optional(dt);
}

std::optional<APIUTCDateTime> SMTParseJSON::extractUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    APIUTCDateTime dt;

    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    auto y = expIntAsUIntSmall(ctx, byearf(value));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    auto m = expIntAsUIntSmall(ctx, bmonthf(value));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    auto d = expIntAsUIntSmall(ctx, bdayf(value));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    auto h = expIntAsUIntSmall(ctx, bhourf(value));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    auto mm = expIntAsUIntSmall(ctx, bminutef(value));
        
    if(!y.has_value() || !m.has_value() || !d.has_value() || !h.has_value() || !mm.has_value())
    {
        return std::nullopt;
    }

    dt.year = (uint16_t)y.value();
    dt.month = (uint8_t)m.value();
    dt.day = (uint8_t)d.value();
    dt.hour = (uint8_t)h.value();
    dt.min = (uint8_t)mm.value();

    return std::make_optional(dt);
}

std::optional<APICalendarDate> SMTParseJSON::extractCalendarDateImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    APICalendarDate dt;

    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    auto y = expIntAsUIntSmall(ctx, byearf(value));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    auto m = expIntAsUIntSmall(ctx, bmonthf(value));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    auto d = expIntAsUIntSmall(ctx, bdayf(value));
        
    if(!y.has_value() || !m.has_value() || !d.has_value())
    {
        return std::nullopt;
    }

    dt.year = (uint16_t)y.value();
    dt.month = (uint8_t)m.value();
    dt.day = (uint8_t)d.value();


    return std::make_optional(dt);
}

std::optional<APIRelativeTime> SMTParseJSON::extractRelativeTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    APIRelativeTime dt;

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    auto h = expIntAsUIntSmall(ctx, bhourf(value));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    auto mm = expIntAsUIntSmall(ctx, bminutef(value));
        
    if(!h.has_value() || !mm.has_value())
    {
        return std::nullopt;
    }

    dt.hour = (uint8_t)h.value();
    dt.min = (uint8_t)mm.value();

    return std::make_optional(dt);
}

std::optional<uint64_t> SMTParseJSON::extractTickTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BTickTime@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}

std::optional<uint64_t> SMTParseJSON::extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BLogicalTime@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}


std::optional<APIISOTimeStamp> SMTParseJSON::extractISOTimeStampImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    APIISOTimeStamp dt;

    auto byearf = getArgContextConstructor(ctx.ctx(), "BDateYear@UFCons_API", ctx.ctx().int_sort());
    auto y = expIntAsUIntSmall(ctx, byearf(value));

    auto bmonthf = getArgContextConstructor(ctx.ctx(), "BDateMonth@UFCons_API", ctx.ctx().int_sort());
    auto m = expIntAsUIntSmall(ctx, bmonthf(value));

    auto bdayf = getArgContextConstructor(ctx.ctx(), "BDateDay@UFCons_API", ctx.ctx().int_sort());
    auto d = expIntAsUIntSmall(ctx, bdayf(value));

    auto bhourf = getArgContextConstructor(ctx.ctx(), "BDateHour@UFCons_API", ctx.ctx().int_sort());
    auto h = expIntAsUIntSmall(ctx, bhourf(value));

    auto bminutef = getArgContextConstructor(ctx.ctx(), "BDateMinute@UFCons_API", ctx.ctx().int_sort());
    auto mm = expIntAsUIntSmall(ctx, bminutef(value));

    auto bsecf = getArgContextConstructor(ctx.ctx(), "BDateSecond@UFCons_API", ctx.ctx().int_sort());
    auto ss = expIntAsUIntSmall(ctx, bsecf(value));

    auto bmillisf = getArgContextConstructor(ctx.ctx(), "BDateMillis@UFCons_API", ctx.ctx().int_sort());
    auto millis = expIntAsUIntSmall(ctx, bmillisf(value));
        
    if(!y.has_value() || !m.has_value() || !d.has_value() || !h.has_value() || !mm.has_value() || !ss.has_value() || !millis.has_value())
    {
        return std::nullopt;
    }

    dt.year = (uint16_t)y.value();
    dt.month = (uint8_t)m.value();
    dt.day = (uint8_t)d.value();
    dt.hour = (uint8_t)h.value();
    dt.min = (uint8_t)mm.value();
    dt.sec = (uint8_t)ss.value();
    dt.millis = (uint16_t)millis.value();

    return std::make_optional(dt);
}

std::optional<std::vector<uint8_t>> SMTParseJSON::extractUUID4Impl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().string_sort());
    auto strval = evalStringAsString(ctx, bbf(value));

    if(!strval.has_value())
    {
        return std::nullopt;
    }

    std::vector<uint8_t> bytes;
    auto vstr = strval.value();

    auto iter = vstr.cbegin();
    while(iter != vstr.cend())
    {
        std::string sstr = {*iter, *(iter + 1)};
        uint8_t bv = std::stoi(sstr, nullptr, 16);
        
        bytes.push_back(bv);
        iter += 2;
    }

    return std::make_optional(bytes);
}

std::optional<std::vector<uint8_t>> SMTParseJSON::extractUUID7Impl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().string_sort());
    auto strval = evalStringAsString(ctx, bbf(value));

    if(!strval.has_value())
    {
        return std::nullopt;
    }

    std::vector<uint8_t> bytes;
    auto vstr = strval.value();

    auto iter = vstr.cbegin();
    while(iter != vstr.cend())
    {
        std::string sstr = {*iter, *(iter + 1)};
        uint8_t bv = std::stoi(sstr, nullptr, 16);
        
        bytes.push_back(bv);
        iter += 2;
    }

    return std::make_optional(bytes);
}

std::optional<std::vector<uint8_t>> SMTParseJSON::extractSHAContentHashImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //
    // TODO: may want to do some reversing of perfect hash and other analysis here
    //

    auto hashsort = ctx.ctx().bv_sort(16);
    auto bbf = getArgContextConstructor(ctx.ctx(), "BContentHash@UFCons_API", hashsort);

    auto bbval = ctx.get_model().eval(bbf(value), true);
    auto strval = bbval.to_string();

    std::vector<uint8_t> vv = {
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1
        };

    if(strval.length() == 3)
    {
        vv[62] = (uint8_t)strval[1];
        vv[63] = (uint8_t)strval[2];
    }

    return std::make_optional(vv);
}

std::optional<std::pair<float, float>> SMTParseJSON::extractLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bbf = getArgContextConstructor(ctx.ctx(), "BFloat@UFCons_API", ctx.ctx().real_sort());

    auto latctx = extendContext(ctx.ctx(), value, 0);
    auto vlat = expFloatAsFloat(ctx, bbf(latctx));

    auto longctx = extendContext(ctx.ctx(), value, 1);
    auto vlong = expFloatAsFloat(ctx, bbf(longctx));

    if(!vlat.has_value() || !vlong.has_value())
    {
        return std::nullopt;
    }

    return std::make_pair(std::stof(vlat.value()), std::stof(vlong.value()));
}

z3::expr SMTParseJSON::extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

z3::expr SMTParseJSON::extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, z3::expr value, std::string pname, z3::solver& ctx)
{
    auto rtype = dynamic_cast<const RecordType*>(itype);
    auto ppos = std::find(rtype->props.cbegin(), rtype->props.cend(), pname);

    return extendContext(ctx.ctx(), value, std::distance(rtype->props.cbegin(), ppos));
}

z3::expr SMTParseJSON::extractValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::pair<std::string, std::string> fnamefkey, z3::solver& ctx)
{
    auto ootype = dynamic_cast<const EntityType*>(itype);
    auto ppos = std::find(ootype->consfields.cbegin(), ootype->consfields.cend(), fnamefkey);

    return extendContext(ctx.ctx(), extendContext(ctx.ctx(), value, 0), std::distance(ootype->consfields.cbegin(), ppos));
}

void SMTParseJSON::prepareExtractContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

std::optional<size_t> SMTParseJSON::extractLengthForContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "ContainerSize@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}

z3::expr SMTParseJSON::extractValueForContainer_T(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

std::pair<z3::expr, z3::expr> SMTParseJSON::extractValueForContainer_KV(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    xxxx;
    return extendContext(ctx.ctx(), value, i);
}

void SMTParseJSON::completeExtractContainer(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

std::optional<size_t> SMTParseJSON::extractUnionChoice(const APIModule* apimodule, const IType* itype, const std::vector<const IType*>& opttypes, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "UnionChoice@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}

z3::expr SMTParseJSON::extractUnionValue(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    return value;
}
