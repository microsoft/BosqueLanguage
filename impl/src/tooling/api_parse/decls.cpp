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

static std::regex re_numberino_r("^[-+]?(0|[1-9][0-9]*)/([1-9][0-9]*)$");

static std::regex re_bv_binary("^#b([0|1]+)$");
static std::regex re_bv_hex("^#x([0-9a-f]+)$");

static std::regex re_utcisotime("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$");
static std::regex re_lclisotime("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(+|-)[0-9]{2}(:?[0-9]{2})?$");

static std::regex re_ticktime("^T(0|[1-9][0-9]*)ns$");

static std::regex re_uuid("^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$");
static std::regex re_hash("^0x[0-9a-f]{128}$");

std::optional<uint64_t> JSONParseHelper::parseToUnsignedNumber(json j)
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

std::optional<int64_t> JSONParseHelper::parseToSignedNumber(json j)
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

std::optional<std::string> JSONParseHelper::parseToBigUnsignedNumber(json j)
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

std::optional<std::string> JSONParseHelper::parseToBigSignedNumber(json j)
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

std::optional<std::string> JSONParseHelper::parseToRealNumber(json j)
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

std::optional<std::string> JSONParseHelper::parseToDecimalNumber(json j)
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

std::optional<std::pair<std::string, uint64_t>> JSONParseHelper::parseToRationalNumber(json j)
{
    std::optional<std::string> nval = std::nullopt;
    std::optional<uint64_t> dval = std::nullopt;
    if(j.is_number_integer() || j.is_string() || (j.is_array() && j.size() == 2))
    {
        if(j.is_number_integer())
        {
            nval = std::to_string(j.get<uint64_t>());
            dval = 1;
        }
        else if(j.is_string())
        {
            std::string sstr = j.get<std::string>();
            if(std::regex_match(sstr, re_numberino_i))
            {
                nval = sstr;
                dval = 1;
            }
            else if(std::regex_match(sstr, re_numberino_r))
            {
                auto sidx = sstr.find('/');
                json num = sstr.substr(0, sidx);
                json denom = sstr.substr(sidx + 1, std::string::npos);

                nval = JSONParseHelper::parseToBigSignedNumber(num);
                dval = JSONParseHelper::parseToUnsignedNumber(denom);
            }
            else
            {
                ;
            }
        }
        else
        {
            nval = JSONParseHelper::parseToBigSignedNumber(j[0]);
            dval = JSONParseHelper::parseToUnsignedNumber(j[1]);
        }
    }

    if(nval.has_value() && dval.has_value())
    {
        return std::make_optional(std::make_pair(nval.value(), dval.value()));
    }
    else
    {
        return std::nullopt;
    }
}

bool parseToDateTimeRaw(json j, uint16_t& y, uint8_t& m, uint8_t& d, uint8_t& hh, uint8_t& mm)
{
    if(!j.is_string())
    {
        return false;
    }

    std::string sstr = j.get<std::string>();
    bool isutctime = std::regex_match(sstr, re_utcisotime);
    bool islocaltime = std::regex_match(sstr, re_lclisotime);

    if(!isutctime && !islocaltime)
    {
        return false;
    }

    uint16_t yy = std::strtol(&sstr[0], nullptr, 10);
    if(yy < 1900)
    {
        return false;
    }
    y = yy - 1900;

    m = std::strtol(&sstr[5], nullptr, 10) - 1;
    if(m > 11)
    {
        return false;
    }

    d = std::strtol(&sstr[8], nullptr, 10);
    if(d == 0 || d > 31)
    {
        return false;
    }

    hh = std::strtol(&sstr[11], nullptr, 10);
    if(hh > 23)
    {
        return false;
    }

    mm = std::strtol(&sstr[14], nullptr, 10);
    if(mm > 59)
    {
        return false;
    }
    
    return true;
}

std::optional<int32_t> parseToDateTimeTZ(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    std::string sstr = j.get<std::string>();
    if(std::regex_match(sstr, re_utcisotime))
    {
        return std::make_optional(0);
    }

    if(!std::regex_match(sstr, re_lclisotime))
    {
        return std::nullopt;
    }

    std::string tstr = sstr.substr(19);
    std::string hhstr = tstr.substr(0, 3);
    std::string mmstr;
    if(tstr.length() > 3)
    {
        if(tstr[3] == ':')
        {
            mmstr = tstr.substr(4);
        }
        else
        {
            mmstr = tstr.substr(3);
        }
    }

    int32_t hh = std::strtol(&hhstr[0], nullptr, 10);
    if(hh > 24)
    {
        return std::nullopt;
    }

    int32_t mm = 0;
    if(!mmstr.empty())
    {
        mm = std::strtol(&mmstr[0], nullptr, 10);
    }

    if(mm > 59) {
        return std::nullopt;
    }
    
    int32_t mmoffset = mm + (60 * hh);
    if(mmoffset < (-12 * 60) || (14 * 60) < mmoffset) {
        return std::nullopt;
    }

    return std::make_optional(mmoffset);
}

std::optional<DateTime> JSONParseHelper::parseToDateTime(json j)
{
    if(j.is_string())
    {
        DateTime tinfo = {0, 0, 0, 0, 0, 0, ""};
        auto ok = parseToDateTimeRaw(j, tinfo.year, tinfo.month, tinfo.day, tinfo.hour, tinfo.min);
        if(!ok)
        {
            return std::nullopt;
        }

        auto tzo = parseToDateTimeTZ(j);
        if(!tzo.has_value())
        {
            return std::nullopt;
        }
        tinfo.tzoffset = tzo.value();

        return std::make_optional(tinfo);
    }
    else
    {
        if(!j.is_array() || j.size() > 2)
        {
            return std::nullopt;
        }

        if(j.size() == 2 && !j[2].is_string())
        {
            return std::nullopt;
        }

        DateTime tinfo = {0, 0, 0, 0, 0, 0, j[2].get<std::string>()};
        auto ok = parseToDateTimeRaw(j[0], tinfo.year, tinfo.month, tinfo.day, tinfo.hour, tinfo.min);
        if(!ok)
        {
            return std::nullopt;
        }

        auto tzo = parseToDateTimeTZ(j[0]);
        if(!tzo.has_value())
        {
            return std::nullopt;
        }
        tinfo.tzoffset = tzo.value();

        return std::make_optional(tinfo);
    }
}

std::optional<uint64_t> JSONParseHelper::parseToTickTime(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
    
    std::string sstr = j.get<std::string>();
    if(!std::regex_match(sstr, re_ticktime))
    {
        return std::nullopt;
    }

    std::optional<uint64_t> nval = std::nullopt;
    try
    {
        nval = std::stoull(sstr);
    }
    catch(...)
    {
        ;
    }

    return nval;
}

std::optional<std::vector<uint8_t>> JSONParseHelper::parseUUID(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    std::string sstr = j.get<std::string>();
    if(!std::regex_match(sstr, re_uuid))
    {
        return std::nullopt;
    }

    std::vector<uint8_t> vv;
    auto iter = sstr.cbegin();
    while(iter != sstr.cend())
    {
        if(*iter == '-')
        {
            iter++;
        }

        std::string sstr = {*iter, *(iter + 1)};
        uint8_t bv = std::stoi(sstr, nullptr, 16);
        
        vv.push_back(bv);
        iter += 2;
    }

    return std::make_optional(vv);
}

std::optional<std::vector<uint8_t>> JSONParseHelper::parseContentHash(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    std::string sstr = j.get<std::string>();
    if(!std::regex_match(sstr, re_hash))
    {
        return std::nullopt;
    }

    std::vector<uint8_t> vv;
    auto iter = sstr.cbegin() + 2;
    while(iter != sstr.cend())
    {
        std::string sstr = {*iter, *(iter + 1)};
        uint8_t bv = std::stoi(sstr, nullptr, 16);
        
        vv.push_back(bv);
        iter += 2;
    }

    return std::make_optional(vv);
}

std::optional<json> JSONParseHelper::emitUnsignedNumber(uint64_t n)
{
    if(n <= 9007199254740991)
    {
        return std::make_optional(n);
    }
    else
    {
        return std::make_optional(std::to_string(n));
    }
}

std::optional<json> JSONParseHelper::emitSignedNumber(int64_t i)
{
    if(-9007199254740991 <= i && i <= 9007199254740991)
    {
        return std::make_optional(i);
    }
    else
    {
        return std::make_optional(std::to_string(i));
    }
}

std::optional<json> JSONParseHelper::emitBigUnsignedNumber(std::string s)
{
    std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitBigSignedNumber(std::string s)
{
    std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitRealNumber(std::string s)
{
    std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitDecimalNumber(std::string s)
{
    std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitRationalNumber(std::pair<std::string, uint64_t> rv)
{
    std::make_optional(rv.first + "/" + std::to_string(rv.second));
}

std::string emitDateTimeRaw(uint16_t y, uint8_t m, uint8_t d, uint8_t hh, uint8_t mm)
{
    struct tm dt = {0};
    dt.tm_year = y + 1900;
    dt.tm_mon = m;
    dt.tm_mday = d;
    dt.tm_hour = hh;
    dt.tm_min = mm;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%dT%H:%M", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

std::optional<json> JSONParseHelper::emitDateTime(DateTime t)
{
    if(t.tzoffset == 0)
    {
        auto tstr = emitDateTimeRaw(t.year, t.month, t.day, t.hour, t.min) + "Z"; 
        return std::make_optional(tstr);
    }
    else
    {
        auto hh = t.tzoffset / 60;
        auto mm = std::abs(t.tzoffset) % 60;
        char sstrt[10] = {0};
        sprintf_s(sstrt, 10, "%+02d:%0d", hh, mm);
        std::string tzstr(sstrt, sstrt + 10);

        auto tstr = emitDateTimeRaw(t.year, t.month, t.day, t.hour, t.min) + tzstr;

        if(t.tzname.empty())
        {
            return std::make_optional(tstr);
        }
        else
        {
            auto jobj = json::array();
            jobj[0] = tstr;
            jobj[1] = t.tzname;

            return std::make_optional(jobj);
        }
    }
}

std::optional<json> JSONParseHelper::emitTickTime(uint64_t t)
{
    return "T" + std::to_string(t) + "ns";
}

std::optional<json> JSONParseHelper::emitUUID(std::vector<uint8_t> uuid)
{
    std::string res;

    uint32_t bb4 = *reinterpret_cast<const uint32_t*>(&uuid[0]);
    uint16_t bb2_1 = *reinterpret_cast<const uint16_t*>(&uuid[4]);
    uint16_t bb2_2 = *reinterpret_cast<const uint16_t*>(&uuid[6]);
    uint16_t bb2_3 = *reinterpret_cast<const uint16_t*>(&uuid[8]);
    uint64_t bb6 = *reinterpret_cast<const uint64_t*>(&uuid[10]) & 0xFFFFFFFFFFFF;
    
    char sstrt[36] = {0};
    sprintf_s(sstrt, 36, "%06x-%04x-%04x-%04x-%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + 36);

    return res;
}

std::optional<json> JSONParseHelper::emitHash(std::vector<uint8_t> hash)
{
    std::string rr = "0x";
    for(auto iter = hash.cbegin(); iter < hash.cend(); ++iter)
    {
        char sstrt[2] = {0};
        sprintf_s(sstrt, 2, "%02x", *iter);

        std::string ss(sstrt, sstrt + 2);
        rr += ss;
    }

    return rr;
}

std::optional<std::pair<std::string, std::string>> JSONParseHelper::checkEnumName(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    auto sstr = j.get<std::string>();
    auto qidx = sstr.find("::");
    if(qidx == std::string::npos)
    {
        return std::nullopt;
    }

    auto tstr = sstr.substr(0, qidx);
    auto nstr = sstr.substr(qidx + 2);

    if(tstr.empty() || nstr.empty())
    {
        return std::nullopt;
    }

    return std::make_optional(std::make_pair(tstr, nstr));
}

InvokeSignature* InvokeSignature::jparse(json j, const std::map<std::string, const IType*>& typemap)
{
    auto name = j["name"].get<std::string>();
    auto rtname = j["restype"].get<std::string>();
    auto restype = typemap.find(rtname)->second;

    std::vector<std::string> argnames;
    auto jargnames = j["argnames"];
    std::transform(jargnames.cbegin(), jargnames.cend(), std::back_inserter(argnames), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<const IType*> argtypes;
    auto jargtypes = j["argtypes"];
    std::transform(jargtypes.cbegin(), jargtypes.cend(), std::back_inserter(argtypes), [&typemap](const json& jv) {
        auto tname = jv.get<std::string>();
        return typemap.find(tname)->second;
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

    std::map<std::string, std::string> typedeclmap;
    auto japitypedecls = j["typedecls"];
    for (size_t i = 0; i < japitypedecls.size(); ++i)
    {
        auto key = japitypedecls[i]["name"].get<std::string>();
        auto val = japitypedecls[i]["type"].get<std::string>();
        typedeclmap[key] = val;
    }

    std::map<std::string, std::string> namespacemap;
    auto jnamespaceremap = j["namespacemap"];
    for (size_t i = 0; i < japitypedecls.size(); ++i)
    {
        auto key = jnamespaceremap[i]["name"].get<std::string>();
        auto val = jnamespaceremap[i]["into"].get<std::string>();
        namespacemap[key] = val;
    }

    std::vector<InvokeSignature*> apisig;
    auto japisig = j["apisig"];
    for (size_t i = 0; i < japisig.size(); ++i)
    {
        auto val = InvokeSignature::jparse(japisig[i], typemap);
        apisig.push_back(val);
    }

    return new APIModule(typemap, apisig, typedeclmap, namespacemap);
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
        case TypeTag::DataStringTag:
            return DataStringType::jparse(j);
        case TypeTag::ByteBufferTag:
            return ByteBufferType::jparse(j);
        case TypeTag::DateTimeTag:
            return DateTimeType::jparse(j);
        case TypeTag::TickTimeTag:
            return TickTimeType::jparse(j);
        case TypeTag::LogicalTimeTag:
            return LogicalTimeType::jparse(j);
        case TypeTag::UUIDTag:
            return UUIDType::jparse(j);
        case TypeTag::ContentHashTag:
            return ContentHashType::jparse(j);
        case TypeTag::ConstructableOfType:
            return ConstructableOfType::jparse(j);
        case TypeTag::TupleTag:
            return TupleType::jparse(j);
        case TypeTag::RecordTag:
            return RecordType::jparse(j);
        case TypeTag::ContainerTag:
            return ContainerType::jparse(j);
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
