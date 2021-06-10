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

BSQType* jsonLoadTupleType(boost::json::value v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);
    KeyFunctorSet keyops = j_iskey(v) ? KeyFunctorSet{tupleEqual_impl, tupleLessThan_impl} : EMPTY_KEY_FUNCTOR_SET;

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
        return new BSQTupleRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, keyops, j_name(v), maxIndex, ttypes, idxoffsets);
    }
    else 
    {
        return new BSQTupleStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, keyops, j_name(v), maxIndex, ttypes, idxoffsets);
    }
}

BSQType* jsonLoadRecordType(boost::json::value v)
{
    xxxx;
}

BSQType* jsonLoadEntityType(boost::json::value v)
{
    xxxx;
}

BSQType* jsonLoadEphemeralListType(boost::json::value v)
{
    xxxx;
}

BSQType* jsonLoadInlineUnionType(boost::json::value v)
{
    xxxx;
}

BSQType* jsonLoadRefUnionType(boost::json::value v)
{
    xxxx;
}

void BSQTypeDecl::jsonLoad(boost::json::value v)
{
    xxxx;
}