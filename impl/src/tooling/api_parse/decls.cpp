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

static std::regex re_iso("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(.[0-9]{3})?Z$");

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
    if(std::regex_match(sstr, re_iso))
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
        case TypeTag::DataBufferTag:
            return DataBufferType::jparse(j);
        case TypeTag::ISOTimeTag:
            return ISOTimeType::jparse(j);
        case TypeTag::LogicalTimeTag:
            return LogicalTimeType::jparse(j);
        case TypeTag::UUIDTag:
            return UUIDType::jparse(j);
        case TypeTag::ContentHashTag:
            return ContentHashType::jparse(j);

        xxxx

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
        case TypeTag::ConceptTag:
            return ConceptType::jparse(j);
        default: 
        {
            assert(false);
            return nullptr;
        }
    }
}
