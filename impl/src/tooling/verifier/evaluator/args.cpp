//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "args.h"

static std::regex re_numberino_n("^[+]?(0|[1-9][0-9]*)$");
static std::regex re_numberino_i("^[-+]?(0|[1-9][0-9]*)$");

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
        s.add(e == s.ctx().int_val(strval.c_str()));

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
        s.add(e == s.ctx().int_val(strval.c_str()));

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
   return std::make_optional("[FloatValue]");
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
        s.add(e == s.ctx().string_val(sstr));

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
    auto ii = c.int_val(i);
    return z3::concat(ctx, ii.unit());
}

z3::func_decl getArgContextConstructor(z3::context& c, const char* fname, const z3::sort& ressort)
{
    auto isort = c.int_sort();
    auto hsort = c.seq_sort(isort);
    auto argconsf = c.function(fname, hsort, ressort);

    return argconsf;
}

z3::func_decl getFloatValueConstConstructor(z3::context& c)
{
    auto floatsort = c.uninterpreted_sort("FloatValue");
    auto argconsf = c.function("FloatValue@const", c.string_sort(), floatsort);

    return argconsf;
}

bool SMTParseJSON::checkInvokeOk(const std::string& checkinvoke, z3::expr value)
{
    xxxx;
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
    auto fcc = getFloatValueConstConstructor(ctx.ctx());
    ctx.add(bef(value) == fcc(ctx.ctx().string_val(f.c_str())));

    return true;
}

bool SMTParseJSON::parseDecimalImpl(const APIModule* apimodule, const IType* itype, std::string d, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BDecimal@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    auto fcc = getFloatValueConstConstructor(ctx.ctx());
    ctx.add(bef(value) == fcc(ctx.ctx().string_val(d.c_str())));

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
    auto fcc = getFloatValueConstConstructor(ctx.ctx());
    ctx.add(bef(value) == fcc(ctx.ctx().string_val(rstr.c_str())));

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
    ctx.add(bbf(ectxbb).length() == ctx.ctx().int_val(data.size()));
    for(size_t i = 0; i < data.size(); ++i)
    {
        ctx.add(bbf(ectxbb).at(ctx.ctx().int_val(i)) == ctx.ctx().bv_val((int)data[i], 8));
    }

    return true;
}

bool SMTParseJSON::parseDateTimeImpl(const APIModule* apimodule, const IType* itype, DateTime t, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());

    auto etime = extendContext(ctx.ctx(), value, 0);
    auto etzo = extendContext(ctx.ctx(), value, 1);
    auto etzn = extendContext(ctx.ctx(), value, 2);

    {
        auto elocaly = extendContext(ctx.ctx(), etime, 0);
        ctx.add(bef(elocaly) == ctx.ctx().int_val(t.year));

        auto elocalm = extendContext(ctx.ctx(), etime, 1);
        ctx.add(bef(elocalm) == ctx.ctx().int_val(t.month));

        auto elocald = extendContext(ctx.ctx(), etime, 2);
        ctx.add(bef(elocald) == ctx.ctx().int_val(t.day));

        auto elocalh = extendContext(ctx.ctx(), etime, 3);
        ctx.add(bef(elocalh) == ctx.ctx().int_val(t.hour));

        auto elocalmm = extendContext(ctx.ctx(), etime, 4);
        ctx.add(bef(elocalmm) == ctx.ctx().int_val(t.min));
    }

    ctx.add(bef(etzo) == ctx.ctx().int_val(t.tzoffset));

    auto bes = getArgContextConstructor(ctx.ctx(), "BString@UFCons_API", ctx.ctx().string_sort());
    ctx.add(bes(etzn) == ctx.ctx().string_val(t.tzname));
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

bool SMTParseJSON::parseUUIDImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx)
{
    auto bytesort = ctx.ctx().bv_sort(8);
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().seq_sort(bytesort));

    ctx.add(bbf(value).length() == ctx.ctx().int_val(16));
    for(size_t i = 0; i < 16; ++i)
    {
        ctx.add(bbf(value).at(ctx.ctx().int_val(i)) == ctx.ctx().bv_val((int)v[i], 8));
    }

    return true;
}

bool SMTParseJSON::parseContentHashImpl(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, z3::expr value, z3::solver& ctx)
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
    ctx.add(bef(value) == ctx.ctx().int_val(count));
}

z3::expr SMTParseJSON::getValueForContainerElementParse(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

void SMTParseJSON::completeParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::prepareParseEntity(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::prepareParseEntityMask(const APIModule* apimodule, const IType* itype, z3::solver& ctx)
{
    ;
}

z3::expr SMTParseJSON::getValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::string fname, z3::solver& ctx)
{
xxxx;
}

void SMTParseJSON::completeParseEntity(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
xxxx;
}

void SMTParseJSON::setMaskFlag(const APIModule* apimodule, z3::expr flagloc, size_t i, bool flag)
{
xxxx;
}

z3::expr SMTParseJSON::parseUnionChoice(const APIModule* apimodule, const IType* itype, z3::expr value, size_t pick, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "UnionChoice@UFCons_API", ctx.ctx().int_sort());
    ctx.add(bef(value) == ctx.ctx().int_val(pick));
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
    //
    // TODO: may want to do some analysis on equality and order requirements with other floats here
    //

    auto bef = getArgContextConstructor(ctx.ctx(), "BFloat@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    return expFloatAsFloat(ctx, bef(value));
}

std::optional<std::string> SMTParseJSON::extractDecimalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //
    // TODO: may want to do some analysis on equality and order requirements with other floats here
    //

    auto bef = getArgContextConstructor(ctx.ctx(), "BDecimal@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
    return expFloatAsFloat(ctx, bef(value));
}

std::optional<std::pair<std::string, uint64_t>> SMTParseJSON::extractRationalImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    //
    // TODO: may want to do some analysis on equality and order requirements with other floats here
    //
    
    auto bef = getArgContextConstructor(ctx.ctx(), "BRational@UFCons_API", ctx.ctx().uninterpreted_sort("FloatValue"));
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
        auto vv = expIntAsUIntSmall(ctx, bbf(ectxbb).at(ctx.ctx().int_val(i)));
        if(!vv.has_value())
        {
            return std::nullopt;
        }

        bytes.push_back((uint8_t)vv.value());
    }

    return std::make_optional(std::make_pair(bytes, pprops));
}

std::optional<DateTime> SMTParseJSON::extractDateTimeImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    DateTime dt;

    auto bef = getArgContextConstructor(ctx.ctx(), "BNat@UFCons_API", ctx.ctx().int_sort());

    auto etime = extendContext(ctx.ctx(), value, 0);
    auto etzo = extendContext(ctx.ctx(), value, 1);
    auto etzn = extendContext(ctx.ctx(), value, 2);

    {
        auto elocaly = extendContext(ctx.ctx(), etime, 0);
        auto y = expIntAsUIntSmall(ctx, bef(elocaly));

        auto elocalm = extendContext(ctx.ctx(), etime, 1);
        auto m = expIntAsUIntSmall(ctx, bef(elocalm));

        auto elocald = extendContext(ctx.ctx(), etime, 2);
        auto d = expIntAsUIntSmall(ctx, bef(elocald));

        auto elocalh = extendContext(ctx.ctx(), etime, 3);
        auto h = expIntAsUIntSmall(ctx, bef(elocalh));

        auto elocalmm = extendContext(ctx.ctx(), etime, 4);
        auto mm = expIntAsUIntSmall(ctx, bef(elocalmm));
        
        if(!y.has_value() || !m.has_value() || !d.has_value() || !h.has_value() || !mm.has_value())
        {
            return std::nullopt;
        }

        dt.year = (uint16_t)y.value();
        dt.month = (uint8_t)m.value();
        dt.day = (uint8_t)d.value();
        dt.hour = (uint8_t)h.value();
        dt.min = (uint8_t)mm.value();
    }

    auto bes = getArgContextConstructor(ctx.ctx(), "BString@UFCons_API", ctx.ctx().string_sort());

    auto tzo = expIntAsUIntSmall(ctx, bef(etzo));
    auto tzn = evalStringAsString(ctx, bes(etzn));
    
    if(!tzo.has_value() || !tzn.has_value())
    {
        return std::nullopt;
    }

    dt.tzoffset = tzo.value();
    dt.tzname = tzn.value();

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

std::optional<std::vector<uint8_t>> SMTParseJSON::extractUUIDImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bytesort = ctx.ctx().bv_sort(8);
    auto bbf = getArgContextConstructor(ctx.ctx(), "BUUID@UFCons_API", ctx.ctx().seq_sort(bytesort));

    std::vector<uint8_t> bytes;
    for(size_t i = 0; i < 16; ++i)
    {
        auto vv = expIntAsUIntSmall(ctx, bbf(value).at(ctx.ctx().int_val(i)));
        if(!vv.has_value())
        {
            return std::nullopt;
        }

        bytes.push_back((uint8_t)vv.value());
    }

    return std::make_optional(bytes);
}

std::optional<std::vector<uint8_t>> SMTParseJSON::extractContentHashImpl(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
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

z3::expr SMTParseJSON::extractValueForEntityField(const APIModule* apimodule, const IType* itype, z3::expr value, std::string pname, z3::solver& ctx)
{
xxxx;
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

z3::expr SMTParseJSON::extractValueForContainer(const APIModule* apimodule, const IType* itype, z3::expr value, size_t i, z3::solver& ctx)
{
    return extendContext(ctx.ctx(), value, i);
}

void SMTParseJSON::completeParseContainer(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    ;
}

std::optional<size_t> SMTParseJSON::extractUnionChoice(const APIModule* apimodule, const IType* itype, z3::expr value, z3::solver& ctx)
{
    auto bef = getArgContextConstructor(ctx.ctx(), "UnionChoice@UFCons_API", ctx.ctx().int_sort());
    return expIntAsUIntSmall(ctx, bef(value));
}
