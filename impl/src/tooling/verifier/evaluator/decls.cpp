//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"


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
        case TypeTag::ConstructableOfType:
            return ConstructableOfType::jparse(j);
        case TypeTag::DataStringTag:
            return DataStringType::jparse(j);
        case TypeTag::ByteBufferTag:
            return ByteBufferType::jparse(j);
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
        case TypeTag::ConceptTag:
            return ConceptType::jparse(j);
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

ConstructableOfType* ConstructableOfType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto validatefunc = j["validatefunc"].get<std::string>();
    
    return new ConstructableOfType(name, oftype, validatefunc);
}

bool ConstructableOfType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->oftype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> ConstructableOfType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
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
    return new ByteBufferType();
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

TupleType* TupleType::jparse(json j)
{
    auto name = j["name"].get<std::string>();

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new TupleType(name, ttypes);
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

    return new RecordType(name, props, ttypes);
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

SomethingType* SomethingType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    return new SomethingType(name, oftype);
}

bool SomethingType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->oftype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> SomethingType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->oftype)->second->z3extract(ex, ectx, s, m);
}

OkType* OkType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    return new OkType(name, oftype);
}

bool OkType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->oftype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> OkType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->oftype)->second->z3extract(ex, ectx, s, m);
}

ErrType* ErrType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    
    return new ErrType(name, oftype);
}

bool ErrType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->oftype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> ErrType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->oftype)->second->z3extract(ex, ectx, s, m);
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

StackType* StackType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto ultype = j["ultype"].get<std::string>();
    
    return new StackType(name, oftype, ultype);
}

bool StackType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->ultype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> StackType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->ultype)->second->z3extract(ex, ectx, s, m);
}

QueueType* QueueType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto ultype = j["ultype"].get<std::string>();
    
    return new QueueType(name, oftype, ultype);
}

bool QueueType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->ultype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> QueueType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->ultype)->second->z3extract(ex, ectx, s, m);
}

SetType* SetType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto ultype = j["ultype"].get<std::string>();
    auto unqchkinv = j["unqchkinv"].get<std::string>();
    auto unqconvinv = j["unqconvinv"].get<std::string>();
    
    return new SetType(name, oftype, ultype, unqchkinv, unqconvinv);
}

bool SetType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->ultype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> SetType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->ultype)->second->z3extract(ex, ectx, s, m);
}

MapType* MapType::jparse(json j)
{
    auto name = j["name"].get<std::string>();
    auto oftype = j["oftype"].get<std::string>();
    auto ultype = j["ultype"].get<std::string>();
    auto unqchkinv = j["unqchkinv"].get<std::string>();
    
    return new MapType(name, oftype, ultype, unqchkinv);
}

bool MapType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(this->ultype)->second->toz3arg(pinfo, j, ectx, c);
}

std::optional<json> MapType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto ectx = extendContext(ex.apimodule, s.ctx(), ctx, 0);
    return ex.apimodule->typemap.find(this->ultype)->second->z3extract(ex, ectx, s, m);
}

EnumType* EnumType::jparse(json j)
{
    std::vector<std::pair<std::string, uint32_t>> enums;
    auto jenuminvs = j["enums"];
    std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enums), [](const json& jv) {
        return std::make_pair(jv["ename"].get<std::string>(), jv["value"].get<uint32_t>());
    });

    return new EnumType(j["name"].get<std::string>(), enums);
}

bool EnumType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_string())
    {
        return false;
    }
    
    std::string enumchoice = j.get<std::string>();
    if(enumchoice.length() <= this->name.length() + 2)
    {
        return false;
    }

    std::string scopestr(enumchoice.cbegin(), enumchoice.cbegin() + this->name.length());
    auto scopeok = this->name == scopestr;
    if(!scopeok)
    {
        return false;
    }

    std::string namestr(enumchoice.cbegin() + this->name.length() + 2, enumchoice.cend());
    auto pos = std::find_if(this->enums.cbegin(), this->enums.cend(), [&namestr](const std::pair<std::string, uint32_t>& entry) {
        return entry.first == namestr;
    });

    if(pos == this->enums.cend())
    {
        return false;
    }

    auto lef = getArgContextConstructor(pinfo.apimodule, c, "EnumChoice@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(lef(ctx) == c.bv_val(pos->second, pinfo.apimodule->bv_width));

    return true;
}

std::optional<json> EnumType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto lef = getArgContextConstructor(ex.apimodule, m.ctx(), "EnumChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
    auto lenval = ex.bvToCardinality(s, m, lef(ctx));
    if(!lenval.has_value())
    {
        return std::nullopt;
    }

    if(lenval.value() >= this->enums.size())
    {
        return std::nullopt;
    }

    std::string rres = this->name + "::" + this->enums[lenval.value()].first;
    return std::make_optional(rres);
}

EntityType* EntityType::jparse(json j)
{
    auto name = j["name"].get<std::string>();

    std::vector<std::string> fields;
    auto jprops = j["fields"];
    std::transform(jprops.cbegin(), jprops.cend(), std::back_inserter(fields), [](const json& jv) {
        return jv.get<std::string>();
    });

    std::vector<std::string> ttypes;
    auto jtypes = j["ttypes"];
    std::transform(jtypes.cbegin(), jtypes.cend(), std::back_inserter(ttypes), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new EntityType(name, fields, ttypes);
}

bool EntityType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    if(!j.is_object() || this->fields.size() != j.size())
    {
        return false;
    }

    auto allprops = std::all_of(this->fields.cbegin(), this->fields.cend(), [&j](const std::string& prop){
                return j.contains(prop);
            });
    if(!allprops)
    {
        return false;
    }

    std::vector<const IType*> argtypes;
    z3::expr_vector targs(c);
    for(size_t i = 0; i < this->fields.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto ectx = extendContext(pinfo.apimodule, c, ctx, i);

        auto ttype = pinfo.apimodule->typemap.find(tt)->second;
        auto pexpr = ttype->toz3arg(pinfo, j[this->fields[i]], ectx, c);
        if(!pexpr)
        {
            return false;
        }
    }

    return true;
}

std::optional<json> EntityType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto jres = json::object();
    for(size_t i = 0; i < this->fields.size(); ++i)
    {
        const std::string& tt = this->ttypes[i];
        auto idxval = extendContext(ex.apimodule, m.ctx(), ctx, i);

        auto ttype = ex.apimodule->typemap.find(tt)->second;
        auto rr = ttype->z3extract(ex, idxval, s, m);
        if(!rr.has_value())
        {
            return std::nullopt;
        }

        jres[this->fields[i]] = rr.value();
    }

    return std::make_optional(jres);
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

ConceptType* ConceptType::jparse(json j)
{
    auto name = j["name"].get<std::string>();

    std::vector<std::string> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](const json& jv) {
        return jv.get<std::string>();
    });

    return new ConceptType(name, opts);
}

bool ConceptType::toz3arg(ParseInfo& pinfo, json j, const z3::expr& ctx, z3::context& c) const
{
    auto jname = j["tag"].get<std::string>();
    auto jvalue = j["value"];

    auto ii = std::find(this->opts.cbegin(), this->opts.cend(), jname);
    auto idx = std::distance(this->opts.cbegin(), ii);

    auto lef = getArgContextConstructor(pinfo.apimodule, c, "ConceptChoice@UFCons_API", c.bv_sort(pinfo.apimodule->bv_width));
    pinfo.chks.top()->push_back(lef(ctx) == c.bv_val((uint64_t)idx, pinfo.apimodule->bv_width));

    auto ectx = extendContext(pinfo.apimodule, c, ctx, 0);
    return pinfo.apimodule->typemap.find(jname)->second->toz3arg(pinfo, jvalue, ectx, c);
}

std::optional<json> ConceptType::z3extract(ExtractionInfo& ex, const z3::expr& ctx, z3::solver& s, z3::model& m) const
{
    auto bef = getArgContextConstructor(ex.apimodule, m.ctx(), "ConceptChoice@UFCons_API", m.ctx().bv_sort(ex.apimodule->bv_width));
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

    auto jj = ttype->z3extract(ex, ectx, s, m);
    if(!jj.has_value())
    {
        return std::nullopt;
    }

    auto jres = json::object();
    jres["tag"] = this->name;
    jres["value"] = jj.value();

    return jres;
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