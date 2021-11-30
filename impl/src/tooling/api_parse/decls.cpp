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

static std::regex re_isotime("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(.[0-9]{3})?Z$");
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

std::optional<TimeData> JSONParseHelper::parseToTimeData(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    std::string sstr = j.get<std::string>();
    if(!std::regex_match(sstr, re_isotime))
    {
        return std::nullopt;
    }

    TimeData t;
    t.millis = std::strtol(&sstr[20], nullptr, 10);
    if(t.millis > 999)
    {
        return std::nullopt;
    }
    
    uint16_t yy = std::strtol(&sstr[0], nullptr, 10);
    if(yy < 1900)
    {
        return std::nullopt;
    }
    t.year = yy - 1900;

    t.month = std::strtol(&sstr[5], nullptr, 10) - 1;
    if(t.month > 11)
    {
        return std::nullopt;
    }

    t.day = std::strtol(&sstr[8], nullptr, 10);
    if(t.day == 0 || t.day > 31)
    {
        return std::nullopt;
    }

    t.hour = std::strtol(&sstr[11], nullptr, 10);
    if(t.hour > 23)
    {
        return std::nullopt;
    }

    t.min = std::strtol(&sstr[14], nullptr, 10);
    if(t.min > 59)
    {
        return std::nullopt;
    }

    t.sec = std::strtol(&sstr[17], nullptr, 10);
    if(t.sec > 60)
    {
        return std::nullopt;
    }
    
    return std::make_optional(t);
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

std::optional<json> JSONParseHelper::emitTimeData(TimeData t)
{
    tm utctime;
    utctime.tm_year = t.year;
    utctime.tm_mon = t.month;
    utctime.tm_mday = t.day;
    utctime.tm_hour = t.hour;
    utctime.tm_min = t.min;
    utctime.tm_sec = t.sec;

    char sstrt[20] = {0};
    strftime(sstrt, 20, "%Y-%m-%dT%H:%M:%S", &utctime);
    std::string res(sstrt, sstrt + 20);

    char sstrz[5] = {0};
    sprintf_s(sstrz, ".%03uZ", t.millis);
    std::string zstr(sstrz, sstrz + 5);

    return res + zstr;
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

    auto japitypedecls = j["typedecls"];
    for (size_t i = 0; i < japitypedecls.size(); ++i)
    {
        auto key = japitypedecls[i]["name"].get<std::string>();
        auto val = japitypedecls[i]["type"].get<std::string>();
        typemap[key] = typemap.find(val)->second;
    }

    std::vector<InvokeSignature*> apisig;
    auto japisig = j["apisig"];
    for (size_t i = 0; i < japisig.size(); ++i)
    {
        auto val = InvokeSignature::jparse(japisig[i], typemap);
        apisig.push_back(val);
    }

    return new APIModule(typemap, apisig);
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
        case TypeTag::ISOTimeTag:
            return ISOTimeType::jparse(j);
        case TypeTag::LogicalTimeTag:
            return LogicalTimeType::jparse(j);
        case TypeTag::UUIDTag:
            return UUIDType::jparse(j);
        case TypeTag::ContentHashTag:
            return ContentHashType::jparse(j);
        case TypeTag::PrimitiveOfTag:
            return PrimitiveOfType::jparse(j);
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
