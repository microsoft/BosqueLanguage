//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqassembly.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

RefMask jsonLoadRefMask(boost::json::value val)
{
    if(val.is_null())
    {
        return nullptr;
    }
    else
    {
        auto mstr = std::string(val.as_string().c_str());
        if (Environment::g_stringmaskToDeclMap.find(mstr) == Environment::g_stringmaskToDeclMap.cend())
        {
            auto rstr = (char*)malloc(mstr.size() + 1);
            GC_MEM_COPY(rstr, mstr.c_str(), mstr.size());
            rstr[mstr.size()] = '\0';

            Environment::g_stringmaskToDeclMap[mstr] = rstr;
        }

        return Environment::g_stringmaskToDeclMap.find(mstr)->second;
    }
}

BSQTypeSizeInfo jsonLoadTypeSizeInfo(boost::json::value val)
{
    uint64_t heapsize = jsonGetAsUInt<uint64_t>(val, "heapsize");
    uint64_t inlinedatasize = jsonGetAsUInt<uint64_t>(val, "inlinedatasize");
    uint64_t assigndatasize = jsonGetAsUInt<uint64_t>(val, "assigndatasize");

    RefMask hmask = jsonLoadRefMask(jsonGet(val, "heapmask"));
    RefMask imask = jsonLoadRefMask(jsonGet(val, "inlinedmask"));

    return BSQTypeSizeInfo{heapsize, inlinedatasize, assigndatasize, hmask, imask};
}

BSQTypeID j_tkey(boost::json::value v)
{
    auto tstr = jsonGetAsString(v, "tkey");
    return Environment::g_typenameToIDMap[tstr].first;
}

std::string j_name(boost::json::value v)
{
    return jsonGetAsString(v, "name");
}

BSQTypeKind j_tkind(boost::json::value v)
{
    return (BSQTypeKind)v.as_object().at("tkind").as_int64();
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
        auto ventry = varray.at(i);

        auto vstr = jsonGetAsString(ventry, "vcall");
        auto istr = jsonGetAsString(ventry, "inv");
        
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
    auto vname = jsonGetAsString(v, "validator");
    auto vtid = Environment::g_typenameToIDMap[vname].first;

    return new BSQStringOfType(j_tkey(v), j_name(v), vtid);
}

const BSQType* jsonLoadDataStringType(boost::json::value v)
{
    auto iname = jsonGetAsString(v, "chkinv");
    auto inv = Environment::g_invokenameToIDMap[iname];

    return new BSQDataStringType(j_tkey(v), j_name(v), inv);
}

const BSQType* jsonLoadTypedNumberType(boost::json::value v)
{
    auto primitive = Environment::g_typenameToIDMap[jsonGetAsString(v, "primitive")].first;
    auto underlying = Environment::g_typenameToIDMap[jsonGetAsString(v, "underlying")].first;

    switch(primitive)
    {
    case BSQ_TYPE_ID_BOOL:
        return new BSQTypedNumberType<BSQBool>(j_tkey(v), j_name(v), underlying, BSQType::g_typeBool); 
    case BSQ_TYPE_ID_NAT:
        return new BSQTypedNumberType<BSQNat>(j_tkey(v), j_name(v), underlying, BSQType::g_typeNat); 
    case BSQ_TYPE_ID_INT:
        return new BSQTypedNumberType<BSQInt>(j_tkey(v), j_name(v), underlying, BSQType::g_typeInt);
    case BSQ_TYPE_ID_BIGNAT:
        return new BSQTypedBigNumberType<BSQBigNat>(j_tkey(v), j_name(v), underlying, BSQType::g_typeBigNat);
    case BSQ_TYPE_ID_BIGINT:
        return new BSQTypedBigNumberType<BSQBigInt>(j_tkey(v), j_name(v), underlying, BSQType::g_typeBigInt);
    case BSQ_TYPE_ID_FLOAT:
        return new BSQTypedNumberType<BSQFloat>(j_tkey(v), j_name(v), underlying, BSQType::g_typeFloat); 
    case BSQ_TYPE_ID_DECIMAL:
        return new BSQTypedNumberType<BSQDecimal>(j_tkey(v), j_name(v), underlying, BSQType::g_typeDecimal); 
    case BSQ_TYPE_ID_RATIONAL:
        return new BSQTypedNumberType<BSQRational>(j_tkey(v), j_name(v), underlying, BSQType::g_typeRational);
    case BSQ_TYPE_ID_ISOTIME:
        return new BSQTypedNumberType<BSQISOTime>(j_tkey(v), j_name(v), underlying, BSQType::g_typeISOTime); 
    case BSQ_TYPE_ID_LOGICALTIME:
        return new BSQTypedNumberType<BSQLogicalTime>(j_tkey(v), j_name(v), underlying, BSQType::g_typeLogicalTime); 
    default: {
        assert(false);
        return nullptr;
    }
    }
}

const BSQType* jsonLoadEnumType(boost::json::value v)
{
    auto underlying = Environment::g_typenameToIDMap[jsonGetAsString(v, "underlying")].first;

    std::vector<std::pair<std::string, uint32_t>> enuminvs;
    auto jenuminvs = v.as_object().at("enuminvs").as_array(); 
    std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enuminvs), [](boost::json::value arg) {
        return std::make_pair(jsonGetAsString(arg, "enum"), jsonGetAsUInt<uint32_t>(arg, "offset"));
    });

    switch(underlying)
    {
    case BSQ_TYPE_ID_BOOL:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeBool, enuminvs); 
    case BSQ_TYPE_ID_NAT:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeNat, enuminvs); 
    case BSQ_TYPE_ID_INT:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeInt, enuminvs);
    case BSQ_TYPE_ID_BIGNAT:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeBigNat, enuminvs);
    case BSQ_TYPE_ID_BIGINT:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeBigInt, enuminvs);
    case BSQ_TYPE_ID_STRING:
        return new BSQEnumType(j_tkey(v), j_name(v), BSQType::g_typeRational, enuminvs);
    default: {
        assert(false);
        return nullptr;
    }
    }
}

const BSQType* jsonLoadListType(boost::json::value v)
{
    BSQTypeID etype = Environment::g_typenameToIDMap[jsonGetAsString(v, "etype")].first;

    uint64_t esize = jsonGetAsUInt<uint64_t>(v, "esize");
    RefMask emask = jsonLoadRefMask(v.as_object().at("emask"));

    BSQListFlatKType<4>* list4 = new BSQListFlatKType<4>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons4", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list4->name + std::string("]")] = {list4->tid, list4};

    BSQListFlatKType<8>* list8 = new BSQListFlatKType<8>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons8", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list8->name + std::string("]")] = {list8->tid, list8};

    BSQListFlatKType<12>* list12 = new BSQListFlatKType<12>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons12", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list12->name + std::string("]")] = {list12->tid, list12};

    BSQListFlatKType<16>* list16 = new BSQListFlatKType<16>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons16", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list16->name + std::string("]")] = {list16->tid, list16};

    BSQListFlatKType<24>* list24 = new BSQListFlatKType<24>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons24", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list24->name + std::string("]")] = {list24->tid, list24};

    BSQListFlatKType<32>* list32 = new BSQListFlatKType<32>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons32", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list32->name + std::string("]")] = {list32->tid, list32};

    BSQListFlatKType<40>* list40 = new BSQListFlatKType<40>((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_cons40", esize, emask);
    Environment::g_typenameToIDMap[std::string("[") + list40->name + std::string("]")] = {list40->tid, list40};

    BSQListSliceType* slice = new BSQListSliceType((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_consslice");
    Environment::g_typenameToIDMap[std::string("[") + slice->name + std::string("]")] = {slice->tid, slice};

    BSQListConcatType* concat = new BSQListConcatType((BSQTypeID)Environment::g_typenameToIDMap.size(), j_name(v) + "_consconcat");
    Environment::g_typenameToIDMap[std::string("[") + concat->name + std::string("]")] = {concat->tid, concat};

    BSQListType* ltype = new BSQListType(j_tkey(v), j_name(v), esize, etype);

    BSQListType::g_listTypeMap[j_tkey(v)] = ListTypeConstructorInfo{
        ltype, 
        list4, list8, list12, list16, list24, list32, list40,
        slice, concat,
        {{4, list4}, {8, list8}, {12, list12}, {16, list16}, {24, list24}, {32, list32}, {40, list40}}
    };

    return ltype;
}

const BSQType* jsonLoadTupleType(boost::json::value v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    BSQTupleIndex maxIndex = (BSQTupleIndex)v.as_object().at("maxIndex").as_int64();

    std::vector<BSQTypeID> ttypes;
    auto ttlist = v.as_object().at("ttypes").as_array();
    std::transform(ttlist.cbegin(), ttlist.cend(), std::back_inserter(ttypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    std::vector<size_t> idxoffsets;
    auto idxlist = v.as_object().at("idxoffsets").as_array();
    std::transform(idxlist.cbegin(), idxlist.cend(), std::back_inserter(idxoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_int64();
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
    auto pnlist = v.as_object().at("propertynames").as_array();
    std::transform(pnlist.cbegin(), pnlist.cend(), std::back_inserter(propertynames), [](boost::json::value prop) {
        auto pstr = std::string(prop.as_string().c_str());
        return Environment::g_propertynameToIDMap[pstr];
    });

    std::vector<BSQTypeID> propertytypes;
    auto ptlist = v.as_object().at("propertytypes").as_array();
    std::transform(ptlist.cbegin(), ptlist.cend(), std::back_inserter(propertytypes), [](boost::json::value rtype) {
        auto tstr = std::string(rtype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    std::vector<size_t> propertyoffsets;
    auto polist = v.as_object().at("propertyoffsets").as_array();
    std::transform(polist.cbegin(), polist.cend(), std::back_inserter(propertyoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_int64();
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
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    std::vector<BSQFieldID> fieldnames;
    auto fnlist = v.as_object().at("fieldnames").as_array();
    std::transform(fnlist.cbegin(), fnlist.cend(), std::back_inserter(fieldnames), [](boost::json::value prop) {
        auto pstr = std::string(prop.as_string().c_str());
        return Environment::g_fieldnameToIDMap[pstr];
    });

    std::vector<BSQTypeID> fieldtypes;
    auto ftlist = v.as_object().at("fieldtypes").as_array();
    std::transform(ftlist.cbegin(), ftlist.cend(), std::back_inserter(fieldtypes), [](boost::json::value rtype) {
        auto tstr = std::string(rtype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    std::vector<size_t> fieldoffsets;
    auto folist = v.as_object().at("fieldoffsets").as_array();
    std::transform(folist.cbegin(), folist.cend(), std::back_inserter(fieldoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_int64();
    });

    if(tkind == BSQTypeKind::Ref) 
    {
        return new BSQEntityRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), fieldnames, fieldtypes, fieldoffsets);
    }
    else 
    {
        return new BSQEntityStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), fieldnames, fieldtypes, fieldoffsets);
    }
}

const BSQType* jsonLoadEphemeralListType(boost::json::value v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> etypes;
    auto etlist = v.as_object().at("etypes").as_array();
    std::transform(etlist.cbegin(), etlist.cend(), std::back_inserter(etypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    std::vector<size_t> idxoffsets;
    auto eolist = v.as_object().at("idxoffsets").as_array();
    std::transform(eolist.cbegin(), eolist.cend(), std::back_inserter(idxoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_int64();
    });

    return new BSQEphemeralListType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), etypes, idxoffsets);
}

const BSQType* jsonLoadInlineUnionType(boost::json::value v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> subtypes;
    auto stlist = v.as_object().at("subtypes").as_array();
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    return new BSQUnionInlineType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), subtypes);
}

const BSQType* jsonLoadRefUnionType(boost::json::value v)
{
    std::vector<BSQTypeID> subtypes;
    auto stlist = v.as_object().at("subtypes").as_array();
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().c_str());
        return Environment::g_typenameToIDMap[tstr].first;
    });

    return new BSQUnionRefType(j_tkey(v), j_name(v), subtypes);
}

enum class ICPPParseTag
{
    BuiltinTag = 0x0,
    ValidatorTag,
    StringOfTag,
    DataStringTag,
    TypedNumberTag,
    VectorTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    TupleTag,
    RecordTag,
    EntityTag,
    EphemeralListTag,
    EnumTag,
    InlineUnionTag,
    RefUnionTag
};

void jsonLoadBSQTypeDecl(boost::json::value v)
{
    const BSQType* ttype = nullptr;

    ICPPParseTag ptag = (ICPPParseTag)v.as_object().at("ptag").as_int64();
    switch(ptag)
    {
    case ICPPParseTag::ValidatorTag:
        ttype = jsonLoadValidatorType(v);
        break;
    case ICPPParseTag::StringOfTag:
        ttype = jsonLoadStringOfType(v);
        break;
    case ICPPParseTag::DataStringTag:
        ttype = jsonLoadDataStringType(v);
        break;
    case ICPPParseTag::TypedNumberTag:
        ttype = jsonLoadTypedNumberType(v);
        break;
    case ICPPParseTag::EnumTag:
        ttype = jsonLoadEnumType(v);
        break;
    case ICPPParseTag::ListTag:
        ttype = jsonLoadListType(v);
        break;
    case ICPPParseTag::TupleTag:
        ttype = jsonLoadTupleType(v);
        break;
    case ICPPParseTag::RecordTag:
        ttype = jsonLoadRecordType(v);
        break;
    case ICPPParseTag::EntityTag:
        ttype = jsonLoadEntityType(v);
        break;
    case ICPPParseTag::EphemeralListTag:
        ttype = jsonLoadEphemeralListType(v);
        break;
    case ICPPParseTag::InlineUnionTag:
        ttype = jsonLoadInlineUnionType(v);
        break;
    case ICPPParseTag::RefUnionTag:
        ttype = jsonLoadRefUnionType(v);
        break;
    default:
        assert(false);
        break;
    }

    BSQType::g_typetable[ttype->tid] = ttype;
}

void jsonLoadBSQLiteralDecl(boost::json::value v, size_t& storageOffset, const BSQType*& gtype, std::string& lval)
{
    storageOffset = jsonGetAsUInt<size_t>(v, "offset");
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[jsonGetAsString(v, "storage")].first];
    lval = jsonGetAsString(v, "value");
}

void jsonLoadBSQConstantDecl(boost::json::value v, size_t& storageOffset, BSQInvokeID& ikey, const BSQType*& gtype)
{
    storageOffset = jsonGetAsUInt<size_t>(v, "storageOffset");
    ikey = Environment::g_invokenameToIDMap[jsonGetAsString(v, "valueInvoke")];
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[jsonGetAsString(v, "ctype")].first];
}

void BSQInvokeDecl::jsonLoad(boost::json::value v)
{
    BSQInvokeDecl* dcl = nullptr;
    if(jsonGetAsBool(v, "isbuiltin"))
    {
        dcl = BSQInvokePrimitiveDecl::jsonLoad(v);
    }
    else
    {
        dcl = BSQInvokeBodyDecl::jsonLoad(v);
    }

    Environment::g_invokes[dcl->ikey] = dcl;
}

BSQInvokeBodyDecl* BSQInvokeBodyDecl::jsonLoad(boost::json::value v)
{
    auto ikey = Environment::g_invokenameToIDMap[jsonGetAsString(v, "ikey")];
    auto srcfile =  jsonGetAsString(v, "srcFile");
    auto recursive = jsonGetAsBool(v, "recursive");

    std::vector<BSQFunctionParameter> params;
    std::transform(v.as_object().at("params").as_array().cbegin(), v.as_object().at("params").as_array().cend(), std::back_inserter(params), [](boost::json::value param) {
        auto tstr =  jsonGetAsString(param, "ptype");
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr].first];

        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[jsonGetAsString(v, "resultType")].first];

    Argument resultArg = {(ArgumentTag)v.as_object().at("resultArg").as_object().at("kind").as_int64(), (uint32_t)v.as_object().at("resultArg").as_object().at("location").as_int64()}; 
    const RefMask mask = jsonLoadRefMask(v.as_object().at("mixedStackMask"));

    std::vector<InterpOp*> body;
    std::transform(v.as_object().at("body").as_array().cbegin(), v.as_object().at("body").as_array().cend(), std::back_inserter(body), [](boost::json::value jop) {
        return InterpOp::jparse(jop);
    });

    return new BSQInvokeBodyDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, resultArg, (size_t)v.as_object().at("scalarStackBytes").as_int64(), (size_t)v.as_object().at("mixedStackBytes").as_int64(), mask, (uint32_t)v.as_object().at("maskSlots").as_int64(), body, (uint32_t)v.as_object().at("argmaskSize").as_int64());
}

BSQInvokePrimitiveDecl* BSQInvokePrimitiveDecl::jsonLoad(boost::json::value v)
{
    auto implkeyname = jsonGetAsString(v, "ikey");
    auto ikey = Environment::g_invokenameToIDMap[implkeyname];
    auto srcfile = jsonGetAsString(v, "srcFile");
    auto recursive = jsonGetAsBool(v, "recursive");

    std::vector<BSQFunctionParameter> params;
    std::transform(v.as_object().at("params").as_array().cbegin(), v.as_object().at("params").as_array().cend(), std::back_inserter(params), [](boost::json::value param) {
        auto tstr = jsonGetAsString(param, "ptype");
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr].first];

        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[jsonGetAsString(v, "resultType")].first];

    const RefMask mask = jsonLoadRefMask(v.as_object().at("mixedStackMask"));

    const BSQType* enclosingtype = nullptr;
    if(v.as_object().at("enclosingtype").is_string())
    {
       enclosingtype = BSQType::g_typetable[Environment::g_typenameToIDMap[jsonGetAsString(v, "enclosingtype")].first];
    }

    BSQPrimitiveImplTag implkey = Environment::g_primitiveinvokenameToIDMap[jsonGetAsString(v, "implkeyname")];
    
    std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap;
    std::for_each(v.as_object().at("scalaroffsetMap").as_array().cbegin(), v.as_object().at("scalaroffsetMap").as_array().cend(), [&scalaroffsetMap](boost::json::value so) {
        auto name = jsonGetAsString(so, "name");
        auto offset = (uint32_t)so.as_object().at("info").as_array().at(0).as_int64();

        auto tstr = std::string(so.as_object().at("info").as_array().at(1).as_string().c_str());
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr].first];

        scalaroffsetMap[name] = {offset, otype};
    });

    std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap;
    std::for_each(v.as_object().at("scalaroffsetMap").as_array().cbegin(), v.as_object().at("scalaroffsetMap").as_array().cend(), [&mixedoffsetMap](boost::json::value mo) {
        auto name = jsonGetAsString(mo, "name");
        auto offset = (uint32_t)mo.as_object().at("info").as_array().at(0).as_int64();

        auto tstr = std::string(mo.as_object().at("info").as_array().at(1).as_string().c_str());
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr].first];

        mixedoffsetMap[name] = {offset, otype};
    });

    std::map<std::string, const BSQType*> binds;
    std::for_each(v.as_object().at("binds").as_array().cbegin(), v.as_object().at("binds").as_array().cend(), [&binds](boost::json::value b) {
        auto name = jsonGetAsString(b, "name");

        auto tstr = jsonGetAsString(b, "ttype");
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr].first];

        binds[name] = otype;
    });

    std::map<std::string, BSQPCode*> pcodes;
    std::for_each(v.as_object().at("pcodes").as_array().cbegin(), v.as_object().at("pcodes").as_array().cend(), [&pcodes](boost::json::value pcode) {
        auto name = jsonGetAsString(pcode, "name");

        auto pc = pcode.at("pc").as_object();
        auto code = Environment::g_invokenameToIDMap[jsonGetAsString(pc, "code")];

        std::vector<Argument> cargs;
        std::transform(pc.at("cargs").as_array().cbegin(), pc.at("cargs").as_array().cend(), std::back_inserter(cargs), [](boost::json::value carg) {
            return Argument{(ArgumentTag)carg.as_object().at("kind").as_int64(), (uint32_t)carg.as_object().at("location").as_int64()}; 
        });

        pcodes[name] = new BSQPCode(code, cargs);
    });

    return new BSQInvokePrimitiveDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, (size_t)v.as_object().at("scalarStackBytes").as_int64(), (size_t)v.as_object().at("mixedStackBytes").as_int64(), mask, (uint32_t)v.as_object().at("maskSlots").as_int64(), enclosingtype, implkey, implkeyname, scalaroffsetMap, mixedoffsetMap, binds, pcodes);
}
