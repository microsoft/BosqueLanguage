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
        auto mstr = std::string(val.as_string().cbegin(), val.as_string().cend());
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
    return BSQTypeSizeInfo{
        jsonGetAsUInt<uint64_t>(val, "heapsize"),
        jsonGetAsUInt<uint64_t>(val, "inlinedatasize"),
        jsonGetAsUInt<uint64_t>(val, "assigndatasize"),
        jsonLoadRefMask(jsonGet(val, "heapmask")),
        jsonLoadRefMask(jsonGet(val, "inlinedmask"))
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

const BSQType* jsonLoadListType(boost::json::value v)
{
    std::string etypestr = std::string(v.as_object().at("etype").as_string().cbegin(), v.as_object().at("etype").as_string().cend());
    BSQTypeID etype = Environment::g_typenameToIDMap[etypestr];

    uint64_t esize = v.as_object().at("esize").as_uint64();
    RefMask emask = jsonLoadRefMask(v.as_object().at("emask"));

    BSQListFlatKType<4>* list4 = new BSQListFlatKType<4>(j_name(v) + "_cons4", esize, emask);
    BSQListFlatKType<8>* list8 = new BSQListFlatKType<8>(j_name(v) + "_cons8", esize, emask);
    BSQListFlatKType<12>* list12 = new BSQListFlatKType<12>(j_name(v) + "_cons12", esize, emask);
    BSQListFlatKType<16>* list16 = new BSQListFlatKType<16>(j_name(v) + "_cons16", esize, emask);
    BSQListFlatKType<24>* list24 = new BSQListFlatKType<24>(j_name(v) + "_cons24", esize, emask);
    BSQListFlatKType<32>* list32 = new BSQListFlatKType<32>(j_name(v) + "_cons32", esize, emask);
    BSQListFlatKType<40>* list40 = new BSQListFlatKType<40>(j_name(v) + "_cons40", esize, emask);

    BSQListSliceType* slice = new BSQListSliceType(j_name(v) + "_consslice");
    BSQListConcatType* concat = new BSQListConcatType(j_name(v) + "_consconcat");

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
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    std::vector<BSQFieldID> fieldnames;
    std::transform(v.as_object().at("fieldnames").as_array().cbegin(), v.as_object().at("fieldnames").as_array().cend(), std::back_inserter(fieldnames), [](boost::json::value prop) {
        auto pstr = std::string(prop.as_string().cbegin(), prop.as_string().cend());
        return Environment::g_fieldnameToIDMap[pstr];
    });

    std::vector<BSQTypeID> fieldtypes;
    std::transform(v.as_object().at("fieldtypes").as_array().cbegin(), v.as_object().at("fieldtypes").as_array().cend(), std::back_inserter(fieldtypes), [](boost::json::value rtype) {
        auto tstr = std::string(rtype.as_string().cbegin(), rtype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    std::vector<size_t> fieldoffsets;
    std::transform(v.as_object().at("fieldoffsets").as_array().cbegin(), v.as_object().at("fieldoffsets").as_array().cend(), std::back_inserter(fieldoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_uint64();
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
    std::transform(v.as_object().at("etypes").as_array().cbegin(), v.as_object().at("etypes").as_array().cend(), std::back_inserter(etypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().cbegin(), ttype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    std::vector<size_t> idxoffsets;
    std::transform(v.as_object().at("idxoffsets").as_array().cbegin(), v.as_object().at("idxoffsets").as_array().cend(), std::back_inserter(idxoffsets), [](boost::json::value offset) {
        return (size_t)offset.as_uint64();
    });

    return new BSQEphemeralListType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), etypes, idxoffsets);
}

const BSQType* jsonLoadInlineUnionType(boost::json::value v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> subtypes;
    std::transform(v.as_object().at("subtypes").as_array().cbegin(), v.as_object().at("subtypes").as_array().cend(), std::back_inserter(subtypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().cbegin(), ttype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    return new BSQUnionInlineType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), subtypes);
}

const BSQType* jsonLoadRefUnionType(boost::json::value v)
{
    std::vector<BSQTypeID> subtypes;
    std::transform(v.as_object().at("subtypes").as_array().cbegin(), v.as_object().at("subtypes").as_array().cend(), std::back_inserter(subtypes), [](boost::json::value ttype) {
        auto tstr = std::string(ttype.as_string().cbegin(), ttype.as_string().cend());
        return Environment::g_typenameToIDMap[tstr];
    });

    return new BSQUnionRefType(j_tkey(v), j_name(v), subtypes);
}

enum class ICPPParseTag
{
    ValidatorTag = 0x0,
    StringOfTag,
    DataStringTag,
    TypedNumberTag,
    ListTag,
    TupleTag,
    RecordTag,
    EntityTag,
    EphemeralListTag,
    InlineUnionTag,
    RefUnionTag
};

void jsonLoadBSQTypeDecl(boost::json::value v)
{
    const BSQType* ttype = nullptr;

    ICPPParseTag ptag = (ICPPParseTag)v.as_object().at("ptag").as_uint64();
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
    storageOffset = (size_t)v.as_object().at("storageOffset").as_uint64();

    auto gstr = std::string(v.as_object().at("storage").as_string().cbegin(), v.as_object().at("storage").as_string().cend());
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[gstr]];

    lval = std::string(v.as_object().at("value").as_string().cbegin(), v.as_object().at("value").as_string().cend());
}

void jsonLoadBSQConstantDecl(boost::json::value v, size_t& storageOffset, BSQInvokeID& ikey, const BSQType*& gtype)
{
    storageOffset = (size_t)v.as_object().at("storageOffset").as_uint64();

    auto ikeystr = std::string(v.as_object().at("valueInvoke").as_string().cbegin(), v.as_object().at("valueInvoke").as_string().cend());
    ikey = Environment::g_invokenameToIDMap[ikeystr];

    auto gstr = std::string(v.as_object().at("ctype").as_string().cbegin(), v.as_object().at("ctype").as_string().cend());
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[gstr]];
}

void BSQInvokeDecl::jsonLoad(boost::json::value v)
{
    BSQInvokeDecl* dcl = nullptr;
    if(v.as_object().at("isbuiltin").as_bool())
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
    auto ikeystr = std::string(v.as_object().at("ikey").as_string().cbegin(), v.as_object().at("ikey").as_string().cend());
    auto ikey = Environment::g_invokenameToIDMap[ikeystr];

    auto srcfile = std::string(v.as_object().at("srcFile").as_string().cbegin(), v.as_object().at("srcFile").as_string().cend());

    auto recursive = v.as_object().at("recursive").as_bool();

    std::vector<BSQFunctionParameter> params;
    std::transform(v.as_object().at("params").as_array().cbegin(), v.as_object().at("params").as_array().cend(), std::back_inserter(params), [](boost::json::value param) {
        auto tstr = std::string(param.as_object().at("ptype").as_string().cbegin(), param.as_object().at("ptype").as_string().cend());
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr]];

        return BSQFunctionParameter{j_name(param), ptype};
    });

    auto rstr = std::string(v.as_object().at("resultType").as_string().cbegin(), v.as_object().at("resultType").as_string().cend());
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[rstr]];

    Argument resultArg = {(ArgumentTag)v.as_object().at("resultArg").as_object().at("kind").as_uint64(), (uint32_t)v.as_object().at("resultArg").as_object().at("location").as_uint64()}; 
    const RefMask mask = jsonLoadRefMask(v.as_object().at("mixedStackMask"));

    std::vector<InterpOp*> body;
    std::transform(v.as_object().at("body").as_array().cbegin(), v.as_object().at("body").as_array().cend(), std::back_inserter(body), [](boost::json::value jop) {
        return InterpOp::jparse(jop);
    });

    return new BSQInvokeBodyDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, resultArg, (size_t)v.as_object().at("scalarStackBytes").as_uint64(), (size_t)v.as_object().at("mixedStackBytes").as_uint64(), mask, (uint32_t)v.as_object().at("maskSlots").as_uint64(), body, (uint32_t)v.as_object().at("argmasksize").as_uint64());
}

BSQInvokePrimitiveDecl* BSQInvokePrimitiveDecl::jsonLoad(boost::json::value v)
{
    auto ikeystr = std::string(v.as_object().at("ikey").as_string().cbegin(), v.as_object().at("ikey").as_string().cend());
    auto ikey = Environment::g_invokenameToIDMap[ikeystr];

    auto srcfile = std::string(v.as_object().at("srcFile").as_string().cbegin(), v.as_object().at("srcFile").as_string().cend());

    auto recursive = v.as_object().at("recursive").as_bool();

    std::vector<BSQFunctionParameter> params;
    std::transform(v.as_object().at("params").as_array().cbegin(), v.as_object().at("params").as_array().cend(), std::back_inserter(params), [](boost::json::value param) {
        auto tstr = std::string(param.as_object().at("ptype").as_string().cbegin(), param.as_object().at("ptype").as_string().cend());
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr]];

        return BSQFunctionParameter{j_name(param), ptype};
    });

    auto rstr = std::string(v.as_object().at("resultType").as_string().cbegin(), v.as_object().at("resultType").as_string().cend());
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[rstr]];

    const RefMask mask = jsonLoadRefMask(v.as_object().at("mixedStackMask"));

    const BSQType* enclosingtype = nullptr;
    if(v.as_object().at("enclosingtype").is_string())
    {
        auto estr = std::string(v.as_object().at("enclosingtype").as_string().cbegin(), v.as_object().at("enclosingtype").as_string().cend());
        enclosingtype = BSQType::g_typetable[Environment::g_typenameToIDMap[estr]];
    }

    auto implkeyname = std::string(v.as_object().at("implkey").as_string().cbegin(), v.as_object().at("implkey").as_string().cend());
    BSQPrimitiveImplTag implkey = Environment::g_primitiveinvokenameToIDMap[implkeyname];
    
    std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap;
    std::for_each(v.as_object().at("scalaroffsetMap").as_array().cbegin(), v.as_object().at("scalaroffsetMap").as_array().cend(), [&scalaroffsetMap](boost::json::value so) {
        auto name = std::string(so.as_object().at("name").as_string().cbegin(), so.as_object().at("name").as_string().cend());

        auto offset = (uint32_t)so.as_object().at("info").as_array().at(0).as_uint64();

        auto tstr = std::string(so.as_object().at("info").as_array().at(1).as_string().cbegin(), so.as_object().at("info").as_array().at(1).as_string().cend());
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr]];

        scalaroffsetMap[name] = {offset, otype};
    });

    std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap;
    std::for_each(v.as_object().at("scalaroffsetMap").as_array().cbegin(), v.as_object().at("scalaroffsetMap").as_array().cend(), [&mixedoffsetMap](boost::json::value mo) {
        auto name = std::string(mo.as_object().at("name").as_string().cbegin(), mo.as_object().at("name").as_string().cend());

        auto offset = (uint32_t)mo.as_object().at("info").as_array().at(0).as_uint64();

        auto tstr = std::string(mo.as_object().at("info").as_array().at(1).as_string().cbegin(), mo.as_object().at("info").as_array().at(1).as_string().cend());
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr]];

        mixedoffsetMap[name] = {offset, otype};
    });

    std::map<std::string, const BSQType*> binds;
    std::for_each(v.as_object().at("binds").as_array().cbegin(), v.as_object().at("binds").as_array().cend(), [&binds](boost::json::value b) {
        auto name = std::string(b.as_object().at("name").as_string().cbegin(), b.as_object().at("name").as_string().cend());

        auto tstr = std::string(b.as_object().at("ttype").as_array().at(1).as_string().cbegin(), b.as_object().at("ttype").as_array().at(1).as_string().cend());
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[tstr]];

        binds[name] = otype;
    });

    std::map<std::string, BSQPCode*> pcodes;
    std::for_each(v.as_object().at("pcodes").as_array().cbegin(), v.as_object().at("pcodes").as_array().cend(), [&pcodes](boost::json::value pcode) {
        auto name = std::string(pcode.as_object().at("name").as_string().cbegin(), pcode.as_object().at("name").as_string().cend());

        auto codestr = std::string(pcode.as_object().at("code").as_string().cbegin(), pcode.as_object().at("code").as_string().cend());
        auto code = Environment::g_invokenameToIDMap[codestr];

        std::vector<Argument> cargs;
        std::transform(pcode.as_object().at("cargs").as_array().cbegin(), pcode.as_object().at("cargs").as_array().cend(), std::back_inserter(cargs), [](boost::json::value carg) {
            return Argument{(ArgumentTag)carg.as_object().at("kind").as_uint64(), (uint32_t)carg.as_object().at("location").as_uint64()}; 
        });

        pcodes[name] = new BSQPCode(code, cargs);
    });

    return new BSQInvokePrimitiveDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, (size_t)v.as_object().at("scalarStackBytes").as_uint64(), (size_t)v.as_object().at("mixedStackBytes").as_uint64(), mask, (uint32_t)v.as_object().at("maskSlots").as_uint64(), enclosingtype, implkey, implkeyname, scalaroffsetMap, mixedoffsetMap, binds, pcodes);
}