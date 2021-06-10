//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqassembly.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

boost::json::value jsonGet(boost::json::value val, const char* prop)
{
    assert(val.is_object());
    return val.as_object().at(prop);
}

template <typename T>
T jsonGetAsUInt(boost::json::value val, const char* prop)
{
    return (T)jsonGet(val, prop).as_uint64();
}

SourceInfo jsonParse_SourceInfo(boost::json::value val)
{
    return SourceInfo{ jsonGetAsUInt<uint32_t>(val, "line"), jsonGetAsUInt<uint32_t>(val, "column") };
}

SourceInfo j_sinfo(boost::json::value val)
{
    return jsonParse_SourceInfo(jsonGet(val, "sinfo"));
}

RefMask jsonLoadHeapMask(boost::json::value val)
{
    if(val.is_null())
    {
        return nullptr;
    }
    else
    {
        auto mstr = std::string(val.as_string().cbegin(), val.as_string().cend());
        if (Environment::g_stringmaskToDeclMap.find(mstr) == Environment::g_stringmaskToDeclMap.cend())
        {
            Environment::g_stringmaskToDeclMap[mstr] = mstr.c_str();
        }

        return Environment::g_stringmaskToDeclMap.find(mstr)->second;
    }
}

BSQTypeSizeInfo jsonLoadTypeSizeInfo(boost::json::value val)
{
    return BSQTypeSizeInfo{
        jsonGetAsUInt<uint64_t>(val, "heapsize"),
        jsonGetAsUInt<uint64_t>(val, "inlinedatasize"),
        jsonGetAsUInt<uint64_t>(val, "assigndatasize"),
        jsonLoadHeapMask(jsonGet(val, "heapmask")),
        jsonLoadHeapMask(jsonGet(val, "inlinedmask"))
    };
}

BSQTypeID j_tkey(boost::json::value v)
{
    auto tstr = std::string(v.as_object().at("tkey").as_string().cbegin(), v.as_object().at("tkey").as_string().cend());
    return Environment::g_typenameToIDMap[tstr];
}

std::string j_name(boost::json::value v)
{
    return std::string(v.as_object().at("tkey").as_string().cbegin(), v.as_object().at("tkey").as_string().cend());
}

BSQTypeKind j_tkind(boost::json::value v)
{
    return (BSQTypeKind)v.as_object().at("tkind").as_uint64();
}

bool j_iskey(boost::json::value v)
{
    return v.as_object().at("iskey").as_bool();
}

BSQTypeSizeInfo j_allocinfo(boost::json::value v)
{
    return jsonLoadTypeSizeInfo(v.as_object().at("allocinfo"));
}

void j_vtable(std::map<BSQVirtualInvokeID, BSQInvokeID>& vtable, boost::json::value v)
{
    auto varray = v.as_object().at("vtable").as_array();
    for(size_t i = 0; i < varray.size(); ++i)
    {
        auto ventry = varray.at(i).as_object();

        auto vstr = std::string(ventry.at("vcall").as_string().cbegin(), ventry.at("vcall").as_string().cend());
        auto istr = std::string(ventry.at("inv").as_string().cbegin(), ventry.at("inv").as_string().cend());
        
        vtable[Environment::g_vinvokenameToIDMap[vstr]] = Environment::g_invokenameToIDMap[istr];
    }
}

const BSQType* jsonLoadValidatorType(boost::json::value v)
{
    auto re = bsqRegexJSONParse_impl(v.as_object().at("regex"));
    return new BSQValidatorType(j_tkey(v), j_name(v), re);
}

const BSQType* jsonLoadStringOfType(boost::json::value v)
{
    auto vname = std::string(v.as_object().at("validator").as_string().cbegin(), v.as_object().at("validator").as_string().cend());
    auto vtid = Environment::g_typenameToIDMap[vname];

    return new BSQStringOfType(j_tkey(v), j_name(v), vtid);
}

const BSQType* jsonLoadDataStringType(boost::json::value v)
{
    auto iname = std::string(v.as_object().at("chkinv").as_string().cbegin(), v.as_object().at("chkinv").as_string().cend());
    auto inv = Environment::g_invokenameToIDMap[iname];

    return new BSQDataStringType(j_tkey(v), j_name(v), inv);
}

const BSQType* jsonLoadTypedNumberType(boost::json::value v)
{
    auto primitivename = std::string(v.as_object().at("primitive").as_string().cbegin(), v.as_object().at("primitive").as_string().cend());
    auto primitive = Environment::g_typenameToIDMap[primitivename];

    auto underlyingname = std::string(v.as_object().at("underlying").as_string().cbegin(), v.as_object().at("underlying").as_string().cend());
    auto underlying = Environment::g_typenameToIDMap[underlyingname];

    switch(primitive)
    {
    case BSQ_TYPE_ID_BOOL:
        return new BSQTypedNumberType<BSQBool>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_NAT:
        return new BSQTypedNumberType<BSQNat>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_INT:
        return new BSQTypedNumberType<BSQInt>(j_tkey(v), j_name(v), underlying);
    case BSQ_TYPE_ID_BIGNAT:
        return new BSQTypedBigNumberType<BSQBigNat>(j_tkey(v), j_name(v), underlying);
    case BSQ_TYPE_ID_BIGINT:
        return new BSQTypedBigNumberType<BSQBigInt>(j_tkey(v), j_name(v), underlying);
    case BSQ_TYPE_ID_FLOAT:
        return new BSQTypedNumberType<BSQFloat>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_DECIMAL:
        return new BSQTypedNumberType<BSQDecimal>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_RATIONAL:
        return new BSQTypedNumberType<BSQRational>(j_tkey(v), j_name(v), underlying);
    case BSQ_TYPE_ID_ISOTIME:
        return new BSQTypedNumberType<BSQISOTime>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_LOGICALTIME:
        return new BSQTypedNumberType<BSQLogicalTime>(j_tkey(v), j_name(v), underlying); 
    case BSQ_TYPE_ID_UUID:
        return new BSQTypedUUIDNumberType(j_tkey(v), j_name(v)); 
    case BSQ_TYPE_ID_CONTENTHASH:
        return new BSQTypedContentHashType(j_tkey(v), j_name(v));
    default: {
        assert(false);
        return nullptr;
    }
    }
}

const BSQType* jsonLoadListType(boost::json::value v)
{
    xxxx;
}

const BSQType* jsonLoadTupleType(boost::json::value v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    BSQTupleIndex maxIndex = (BSQTupleIndex)v.as_object().at("maxIndex").as_uint64();

    std::vector<BSQTypeID> ttypes;
    std::transform(v.as_object().at("ttypes").as_array().cbegin(), v.as_object().at("ttypes").as_array().cend(), std::back_inserter(ttypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().cbegin(), ttype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    std::vector<size_t> idxoffsets;
    std::transform(v.as_object().at("idxoffsets").as_array().cbegin(), v.as_object().at("idxoffsets").as_array().cend(), std::back_inserter(idxoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_uint64();
    });

    if(tkind == BSQTypeKind::Ref) 
    {
        return new BSQTupleRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), maxIndex, ttypes, idxoffsets);
    }
    else 
    {
        return new BSQTupleStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), maxIndex, ttypes, idxoffsets);
    }
}

const BSQType* jsonLoadRecordType(boost::json::value v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    std::vector<BSQRecordPropertyID> propertynames;
    std::transform(v.as_object().at("propertynames").as_array().cbegin(), v.as_object().at("propertynames").as_array().cend(), std::back_inserter(propertynames), [](boost::json::value prop) {
        auto pstr = std::string(prop.as_string().cbegin(), prop.as_string().cend());
        return Environment::g_propertynameToIDMap[pstr];
    });

    std::vector<BSQTypeID> propertytypes;
    std::transform(v.as_object().at("propertytypes").as_array().cbegin(), v.as_object().at("propertytypes").as_array().cend(), std::back_inserter(propertytypes), [](boost::json::value rtype) {
        auto tstr = std::string(rtype.as_string().cbegin(), rtype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    std::vector<size_t> propertyoffsets;
    std::transform(v.as_object().at("propertyoffsets").as_array().cbegin(), v.as_object().at("propertyoffsets").as_array().cend(), std::back_inserter(propertyoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_uint64();
    });

    if(tkind == BSQTypeKind::Ref) 
    {
        return new BSQRecordRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), propertynames, propertytypes, propertyoffsets);
    }
    else 
    {
        return new BSQRecordStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), propertynames, propertytypes, propertyoffsets);
    }
}

const BSQType* jsonLoadEntityType(boost::json::value v)
{
    xxxx;
}

const BSQType* jsonLoadEphemeralListType(boost::json::value v)
{
    xxxx;
}

const BSQType* jsonLoadInlineUnionType(boost::json::value v)
{
    xxxx;
}

const BSQType* jsonLoadRefUnionType(boost::json::value v)
{
    xxxx;
}

void BSQTypeDecl::jsonLoad(boost::json::value v)
{
    xxxx;
}