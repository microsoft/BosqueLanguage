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

static std::regex re_apidatetime_TZ("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}z[a-zA-Z_/]*$");
static std::regex re_apidatetime_UTC("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}Z$");
static std::regex re_apidate("^[0-9]{4}-[0-9]{2}-[0-9]{2}$");
static std::regex re_apitime("^[0-9]{2}:[0-9]{2}$");
static std::regex re_isotimestamp("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$");

static std::regex re_ticktime("^T(0|[1-9][0-9]*)ns$");

static std::regex re_uuid("^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$");
static std::regex re_hash("^0x[0-9a-f]{128}$");

std::set<std::string> APIModule::s_tzdata;

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
            nval = std::to_string(j.get<int64_t>());
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

bool parseToDateTimeRaw(json j, uint16_t& y, uint8_t& m, uint8_t& d, uint8_t& hh, uint8_t& mm, bool tzok)
{
    if(!j.is_string())
    {
        return false;
    }

    std::string sstr = j.get<std::string>();
    bool isutctime = std::regex_match(sstr, re_apidatetime_UTC);
    bool islocaltime = std::regex_match(sstr, re_apidatetime_TZ);

    if(!isutctime && !islocaltime)
    {
        return false;
    }

    if(!tzok && islocaltime)
    {
        return false;
    }

    y = std::strtol(&sstr[0], nullptr, 10);
    if(y < 1900)
    {
        return false;
    }

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

bool parseToCalendarDateRaw(json j, uint16_t& y, uint8_t& m, uint8_t& d)
{
    if(!j.is_string())
    {
        return false;
    }

    std::string sstr = j.get<std::string>();
    bool isdate = std::regex_match(sstr, re_apidate);

    if(!isdate)
    {
        return false;
    }

    y = std::strtol(&sstr[0], nullptr, 10);
    if(y < 1900)
    {
        return false;
    }

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
    
    return true;
}

bool parseToISOTimeStampRaw(json j, uint16_t& y, uint8_t& m, uint8_t& d, uint8_t& hh, uint8_t& mm, uint8_t& ss, uint16_t& millis)
{
    if(!j.is_string())
    {
        return false;
    }

    std::string sstr = j.get<std::string>();
    bool ists = std::regex_match(sstr, re_isotimestamp);

    if(!ists)
    {
        return false;
    }

    y = std::strtol(&sstr[0], nullptr, 10);
    if(y < 1900)
    {
        return false;
    }

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

    ss = std::strtol(&sstr[17], nullptr, 10);
    if(ss > 60)
    {
        return false;
    }

    millis = std::strtol(&sstr[20], nullptr, 10);
    if(millis > 999)
    {
        return false;
    }
    
    return true;
}

std::optional<const char*> parseToDateTimeTZ(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }

    std::string sstr = j.get<std::string>();
    std::string tzstr = "UTC";

    if(std::regex_match(sstr, re_apidatetime_UTC))
    {
        ;
    }
    else if(std::regex_match(sstr, re_apidatetime_TZ))
    {
        tzstr = sstr.substr(17);
    }
    else
    {
        return std::nullopt;
    }

    //TODO: we should actually validate that this is a valid tzdata name
    auto tz = APIModule::s_tzdata.insert(tzstr).first;
    return std::make_optional(tz->c_str());
}

std::optional<APIDateTime> JSONParseHelper::parseToDateTime(json j)
{
    if(!j.is_string()) {
        return std::nullopt;
    }
    
    APIDateTime tinfo = {0, 0, 0, 0, 0, nullptr};
    auto ok = parseToDateTimeRaw(j, tinfo.year, tinfo.month, tinfo.day, tinfo.hour, tinfo.min, true);
    if(!ok)
    {
        return std::nullopt;
    }

    auto tzo = parseToDateTimeTZ(j);
    if(!tzo.has_value())
    {
        return std::nullopt;
    }
    tinfo.tzdata = tzo.value();

    return std::make_optional(tinfo);
}

std::optional<APIUTCDateTime> JSONParseHelper::parseToUTCDateTime(json j)
{
    if(!j.is_string()) {
        return std::nullopt;
    }
    
    APIUTCDateTime tinfo = {0, 0, 0, 0, 0};
    auto ok = parseToDateTimeRaw(j, tinfo.year, tinfo.month, tinfo.day, tinfo.hour, tinfo.min, false);
    if(!ok)
    {
        return std::nullopt;
    }

    return std::make_optional(tinfo);
}

std::optional<APICalendarDate> JSONParseHelper::parseToCalendarDate(json j)
{
    if(!j.is_string()) {
        return std::nullopt;
    }
    
    APICalendarDate tinfo = {0, 0, 0};
    auto ok = parseToCalendarDateRaw(j, tinfo.year, tinfo.month, tinfo.day);
    if(!ok)
    {
        return std::nullopt;
    }

    return std::make_optional(tinfo);
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

std::optional<uint64_t> JSONParseHelper::parseToLogicalTime(json j)
{
    if(!j.is_string())
    {
        return std::nullopt;
    }
    
    std::string sstr = j.get<std::string>();
    if(!std::regex_match(sstr, re_numberino_n))
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

std::optional<APIISOTimeStamp> JSONParseHelper::parseToISOTimeStamp(json j)
{
    if(!j.is_string()) {
        return std::nullopt;
    }
    
    APIISOTimeStamp tinfo = {0, 0, 0, 0, 0, 0, 0};
    auto ok = parseToISOTimeStampRaw(j, tinfo.year, tinfo.month, tinfo.day, tinfo.hour, tinfo.min, tinfo.sec, tinfo.millis);
    if(!ok)
    {
        return std::nullopt;
    }

    return std::make_optional(tinfo);
}

std::optional<std::vector<uint8_t>> JSONParseHelper::parseUUID4(json j)
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

std::optional<std::vector<uint8_t>> JSONParseHelper::parseUUID7(json j)
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

std::optional<std::vector<uint8_t>> JSONParseHelper::parseSHAContentHash(json j)
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

std::optional<std::pair<float, float>> JSONParseHelper::parseLatLongCoordinate(json j)
{
    if(!j.is_array() || j.size() != 2)
    {
        return std::nullopt;
    }

    if(!j[0].is_number_float() || !j[1].is_number_float())
    {
        return std::nullopt;
    }

    float latitude = j[0].get<float>();
    float longitude = j[1].get<float>();

    return std::make_optional(std::make_pair(latitude, longitude));
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
    return std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitBigSignedNumber(std::string s)
{
    return std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitRealNumber(std::string s)
{
    return std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitDecimalNumber(std::string s)
{
    return std::make_optional(s);
}

std::optional<json> JSONParseHelper::emitRationalNumber(std::pair<std::string, uint64_t> rv)
{
    return std::make_optional(rv.first + "/" + std::to_string(rv.second));
}

std::string emitDateTimeRaw_d(uint16_t y, uint8_t m, uint8_t d, uint8_t hh, uint8_t mm)
{
    struct tm dt = tm();
    dt.tm_year = y;
    dt.tm_mon = m;
    dt.tm_mday = d;
    dt.tm_hour = hh;
    dt.tm_min = mm;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%dT%H:%M", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

std::string emitCalendarDateRaw_d(uint16_t y, uint8_t m, uint8_t d)
{
    struct tm dt = tm();
    dt.tm_year = y;
    dt.tm_mon = m;
    dt.tm_mday = d;

    char sstrt[20] = {0};
    size_t dtlen = strftime(sstrt, 20, "%Y-%m-%d", &dt);
    std::string res(sstrt, sstrt + dtlen);

    return res;
}

std::string emitISOTimeStampRaw_d(uint16_t y, uint8_t m, uint8_t d, uint8_t hh, uint8_t mm, uint8_t ss, uint16_t millis)
{
    struct tm dt = tm();
    dt.tm_year = y;
    dt.tm_mon = m;
    dt.tm_mday = d;
    dt.tm_hour = hh;
    dt.tm_min = mm;
    dt.tm_sec = ss;

    char sstrt[30] = {0};
    size_t dtlen = strftime(sstrt, 30, "%Y-%m-%dT%H:%M:%S", &dt);
    std::string res(sstrt, sstrt + dtlen);

    char strmillis[8] = {0};
    size_t mtlen = sprintf(strmillis, ".%.3u", millis);
    std::string ms(strmillis, strmillis + mtlen);

    return res + ms;
}

std::optional<json> JSONParseHelper::emitDateTime(APIDateTime t)
{
    auto tzstr = std::string(t.tzdata);
    if(tzstr == "UTC")
    {
        auto tstr = emitDateTimeRaw_d(t.year, t.month, t.day, t.hour, t.min) + "Z"; 
        return std::make_optional(tstr);
    }
    else
    {
        auto tstr = emitDateTimeRaw_d(t.year, t.month, t.day, t.hour, t.min) + "z" + tzstr;
        return std::make_optional(tstr);
    }
}

std::optional<json> JSONParseHelper::emitUTCDateTime(APIUTCDateTime t)
{
    auto tstr = emitDateTimeRaw_d(t.year, t.month, t.day, t.hour, t.min) + "Z"; 
    return std::make_optional(tstr);
}

std::optional<json> JSONParseHelper::emitCalendarDate(APICalendarDate t)
{
    auto tstr = emitCalendarDateRaw_d(t.year, t.month, t.day); 
    return std::make_optional(tstr);
}

std::optional<json> JSONParseHelper::emitTickTime(uint64_t t)
{
    return "T" + std::to_string(t) + "ns";
}

std::optional<json> JSONParseHelper::emitLogicalTime(uint64_t t)
{
    return "L" + std::to_string(t);
}

std::optional<json> JSONParseHelper::emitISOTimeStamp(APIISOTimeStamp t)
{
    auto tstr = emitISOTimeStampRaw_d(t.year, t.month, t.day, t.hour, t.min, t.sec, t.millis) + "Z"; 
    return std::make_optional(tstr);
}

std::optional<json> JSONParseHelper::emitUUID4(std::vector<uint8_t> uuid)
{
    unsigned int bb4 = (unsigned int)(*reinterpret_cast<const uint32_t*>(&uuid[0]));
    unsigned int bb2_1 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[4]));
    unsigned int bb2_2 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[6]));
    unsigned int bb2_3 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[8]));
    unsigned int bb6 = (unsigned int)(*reinterpret_cast<const uint64_t*>(&uuid[10]) & 0xFFFFFFFFFFFF);
    
    char sstrt[64] = {0};
    sprintf(sstrt, "%06x-%04x-%04x-%04x-%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + 36);

    return res;
}

std::optional<json> JSONParseHelper::emitUUID7(std::vector<uint8_t> uuid)
{
    unsigned int bb4 = (unsigned int)(*reinterpret_cast<const uint32_t*>(&uuid[0]));
    unsigned int bb2_1 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[4]));
    unsigned int bb2_2 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[6]));
    unsigned int bb2_3 = (unsigned int)(*reinterpret_cast<const uint16_t*>(&uuid[8]));
    unsigned int bb6 = (unsigned int)(*reinterpret_cast<const uint64_t*>(&uuid[10]) & 0xFFFFFFFFFFFF);
    
    char sstrt[64] = {0};
    sprintf(sstrt, "%06x-%04x-%04x-%04x-%08x", bb4, bb2_1, bb2_2, bb2_3, bb6);
    std::string res(sstrt, sstrt + 36);

    return res;
}

std::optional<json> JSONParseHelper::emitSHAHash(std::vector<uint8_t> hash)
{
    std::string rr = "0x";
    for(auto iter = hash.cbegin(); iter < hash.cend(); ++iter)
    {
        char sstrt[8] = {0};
        sprintf(sstrt, "%02x", *iter);

        std::string ss(sstrt, sstrt + 2);
        rr += ss;
    }

    return rr;
}

std::optional<json> JSONParseHelper::emitLatLongCoordinate(std::pair<float, float> llcoord)
{
    auto jres = json::array();
    jres.push_back(llcoord.first);
    jres.push_back(llcoord.second);

    return std::make_optional(jres);
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

APIModule::~APIModule()
{
    for(auto iter = this->typemap.begin(); iter != this->typemap.end(); ++iter)
    {
        delete iter->second;
    }

    for(auto iter = this->api.begin(); iter != this->api.end(); ++iter)
    {
        delete *iter;
    }
}

std::vector<const IType*> APIModule::getAllTypesInUnion(const UnionType* tt) const
{
    std::vector<const IType*> res;
    std::for_each(tt->opts.cbegin(), tt->opts.cend(), [this, &res](const std::string& ttname) {
        const IType* opttt = this->typemap.find(ttname)->second;
        assert(!opttt->isUnion());

        res.push_back(opttt);
    });

    return res;
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
    for (size_t i = 0; i < jnamespaceremap.size(); ++i)
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
        case TypeTag::DataBufferTag:
            return DataBufferType::jparse(j);
        case TypeTag::DateTimeTag:
            return DateTimeType::jparse(j);
        case TypeTag::UTCDateTimeTag:
            return UTCDateTimeType::jparse(j);
        case TypeTag::CalendarDateTag:
            return CalendarDateType::jparse(j);
        case TypeTag::TickTimeTag:
            return TickTimeType::jparse(j);
        case TypeTag::LogicalTimeTag:
            return LogicalTimeType::jparse(j);
        case TypeTag::ISOTimeStampTag:
            return ISOTimeStampType::jparse(j);
        case TypeTag::UUID4Tag:
            return UUID4Type::jparse(j);
        case TypeTag::UUID7Tag:
            return UUID7Type::jparse(j);
        case TypeTag::SHAContentHashTag:
            return SHAContentHashType::jparse(j);
        case TypeTag::LatLongCoordinateTag:
            return LatLongCoordinateType::jparse(j);
        case TypeTag::ConstructableOfType:
            return ConstructableOfType::jparse(j);
        case TypeTag::TupleTag:
            return TupleType::jparse(j);
        case TypeTag::RecordTag:
            return RecordType::jparse(j);
        case TypeTag::ContainerTTag:
            return ContainerTType::jparse(j);
        case TypeTag::ContainerKVTag:
            return ContainerKVType::jparse(j);
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

