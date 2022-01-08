//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqinvoke.h"

std::vector<const BSQInvokeDecl*> BSQInvokeDecl::g_invokes;

RefMask jsonLoadRefMask(json val)
{
    if(val.is_null())
    {
        return nullptr;
    }
    else
    {
        auto mstr = val.get<std::string>();
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

BSQTypeSizeInfo jsonLoadTypeSizeInfo(json val)
{
    uint64_t heapsize = val["heapsize"].get<uint64_t>();
    uint64_t inlinedatasize = val["inlinedatasize"].get<uint64_t>();
    uint64_t assigndatasize = val["assigndatasize"].get<uint64_t>();

    RefMask hmask = jsonLoadRefMask(val["heapmask"]);
    RefMask imask = jsonLoadRefMask(val["inlinedmask"]);

    return BSQTypeSizeInfo{heapsize, inlinedatasize, assigndatasize, hmask, imask};
}

BSQTypeID j_tkey(json v)
{
    auto tstr = v["tkey"].get<std::string>();
    return Environment::g_typenameToIDMap[tstr].first;
}

std::string j_name(json v)
{
    return v["name"].get<std::string>();
}

BSQTypeKind j_tkind(json v)
{
    return v["tkind"].get<BSQTypeKind>();
}

bool j_iskey(json v)
{
    return v["iskey"].get<bool>();
}

BSQTypeSizeInfo j_allocinfo(json v)
{
    return jsonLoadTypeSizeInfo(v["allocinfo"]);
}

void j_vtable(std::map<BSQVirtualInvokeID, BSQInvokeID>& vtable, json v)
{
    auto varray = v["vtable"];
    for(size_t i = 0; i < varray.size(); ++i)
    {
        auto ventry = varray.at(i);

        auto vstr = ventry["vcall"].get<std::string>();
        auto istr = ventry["inv"].get<std::string>();
        
        vtable[Environment::g_vinvokenameToIDMap[vstr]] = Environment::g_invokenameToIDMap[istr];
    }
}

const BSQType* jsonLoadValidatorType(json v)
{
    auto re = bsqRegexJSONParse_impl(v["regex"]);
    return new BSQValidatorType(j_tkey(v), j_name(v), re);
}

const BSQType* jsonLoadStringOfType(json v)
{
    auto vname = v["validator"].get<std::string>();
    auto vtid = Environment::g_typenameToIDMap[vname].first;

    return new BSQStringOfType(j_tkey(v), j_name(v), vtid);
}

const BSQType* jsonLoadDataStringType(json v)
{
    auto iname = v["chkinv"].get<std::string>();
    auto inv = Environment::g_invokenameToIDMap[iname];

    return new BSQDataStringType(j_tkey(v), j_name(v), inv);
}

const BSQType* jsonLoadTypedNumberType(json v)
{
    auto primitive = Environment::g_typenameToIDMap[v["primitive"].get<std::string>()].first;
    auto underlying = Environment::g_typenameToIDMap[v["underlying"].get<std::string>()].first;

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

const BSQType* jsonLoadEnumType(json v)
{
    auto underlying = Environment::g_typenameToIDMap[v["underlying"].get<std::string>()].first;

    std::vector<std::pair<std::string, uint32_t>> enuminvs;
    auto jenuminvs = v["enuminvs"]; 
    std::transform(jenuminvs.cbegin(), jenuminvs.cend(), std::back_inserter(enuminvs), [](json arg) {
        return std::make_pair(arg["enum"].get<std::string>(), arg["offset"].get<uint32_t>());
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

const BSQType* jsonLoadListType(json v)
{
    BSQTypeID etype = Environment::g_typenameToIDMap[v["etype"].get<std::string>()].first;

    uint64_t esize = v["esize"].get<uint64_t>();
    RefMask emask = jsonLoadRefMask(v["emask"]);

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

const BSQType* jsonLoadTupleType(json v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    BSQTupleIndex maxIndex = v["maxIndex"].get<BSQTupleIndex>();

    std::vector<BSQTypeID> ttypes;
    auto ttlist = v["ttypes"];
    std::transform(ttlist.cbegin(), ttlist.cend(), std::back_inserter(ttypes), [](json ttype) {
        return Environment::g_typenameToIDMap[ttype.get<std::string>()].first;
    });

    std::vector<size_t> idxoffsets;
    auto idxlist = v["idxoffsets"];
    std::transform(idxlist.cbegin(), idxlist.cend(), std::back_inserter(idxoffsets), [](json offset) {
        return offset.get<size_t>();
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

const BSQType* jsonLoadRecordType(json v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    std::vector<BSQRecordPropertyID> propertynames;
    auto pnlist = v["propertynames"];
    std::transform(pnlist.cbegin(), pnlist.cend(), std::back_inserter(propertynames), [](json prop) {
        return Environment::g_propertynameToIDMap[prop.get<std::string>()];
    });

    std::vector<BSQTypeID> propertytypes;
    auto ptlist = v["propertytypes"];
    std::transform(ptlist.cbegin(), ptlist.cend(), std::back_inserter(propertytypes), [](json rtype) {
        return Environment::g_typenameToIDMap[rtype.get<std::string>()].first;
    });

    std::vector<size_t> propertyoffsets;
    auto polist = v["propertyoffsets"];
    std::transform(polist.cbegin(), polist.cend(), std::back_inserter(propertyoffsets), [](json offset) {
        return offset.get<size_t>();
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

const BSQType* jsonLoadEntityType(json v)
{
    auto tid = j_tkey(v);
    auto tkind = j_tkind(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v);

    std::vector<BSQFieldID> fieldnames;
    auto fnlist = v["fieldnames"];
    std::transform(fnlist.cbegin(), fnlist.cend(), std::back_inserter(fieldnames), [](json fname) {
        return Environment::g_fieldnameToIDMap[fname.get<std::string>()];
    });

    std::vector<BSQTypeID> fieldtypes;
    auto ftlist = v["fieldtypes"];
    std::transform(ftlist.cbegin(), ftlist.cend(), std::back_inserter(fieldtypes), [](json ftype) {
        return Environment::g_typenameToIDMap[ftype.get<std::string>()].first;
    });

    std::vector<size_t> fieldoffsets;
    auto folist = v["fieldoffsets"];
    std::transform(folist.cbegin(), folist.cend(), std::back_inserter(fieldoffsets), [](json offset) {
        return offset.get<size_t>();
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

const BSQType* jsonLoadEphemeralListType(json v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> etypes;
    auto etlist = v["etypes"];
    std::transform(etlist.cbegin(), etlist.cend(), std::back_inserter(etypes), [](json ttype) {
        return Environment::g_typenameToIDMap[ttype.get<std::string>()].first;
    });

    std::vector<size_t> idxoffsets;
    auto eolist = v["idxoffsets"];
    std::transform(eolist.cbegin(), eolist.cend(), std::back_inserter(idxoffsets), [](json offset) {
        return offset.get<size_t>();
    });

    return new BSQEphemeralListType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), etypes, idxoffsets);
}

const BSQType* jsonLoadInlineUnionType(json v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> subtypes;
    auto stlist = v["subtypes"];
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](json ttype) {
        return Environment::g_typenameToIDMap[ttype.get<std::string>()].first;
    });

    return new BSQUnionInlineType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), subtypes);
}

const BSQType* jsonLoadRefUnionType(json v)
{
    std::vector<BSQTypeID> subtypes;
    auto stlist = v["subtypes"];
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](json ttype) {
        return Environment::g_typenameToIDMap[ttype.get<std::string>()].first;
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

void jsonLoadBSQTypeDecl(json v)
{
    const BSQType* ttype = nullptr;

    ICPPParseTag ptag = v["ptag"].get<ICPPParseTag>();
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

    Environment::g_typenameToIDMap[ttype->name].second = ttype;
}

void jsonLoadBSQLiteralDecl(json v, size_t& storageOffset, const BSQType*& gtype, std::string& lval)
{
    storageOffset = v["offset"].get<size_t>();
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[v["storage"].get<std::string>()].first];
    lval = v["value"].get<std::string>();
}

void jsonLoadBSQConstantDecl(json v, size_t& storageOffset, BSQInvokeID& ikey, const BSQType*& gtype)
{
    storageOffset = v["storageOffset"].get<size_t>();
    ikey = Environment::g_invokenameToIDMap[v["valueInvoke"].get<std::string>()];
    gtype = BSQType::g_typetable[Environment::g_typenameToIDMap[v["ctype"].get<std::string>()].first];
}

void BSQInvokeDecl::jsonLoad(json v)
{
    BSQInvokeDecl* dcl = nullptr;
    if(v["isbuiltin"].get<bool>())
    {
        dcl = BSQInvokePrimitiveDecl::jsonLoad(v);
    }
    else
    {
        dcl = BSQInvokeBodyDecl::jsonLoad(v);
    }

    Environment::g_invokes[dcl->ikey] = dcl;
}

BSQInvokeBodyDecl* BSQInvokeBodyDecl::jsonLoad(json v)
{
    auto ikey = Environment::g_invokenameToIDMap[v["ikey"].get<std::string>()];
    auto srcfile = v["srcFile"].get<std::string>();
    auto recursive = v["recursive"].get<bool>();

    std::vector<BSQFunctionParameter> params;
    auto jparams = v["params"];
    std::transform(jparams.cbegin(), jparams.cend(), std::back_inserter(params), [](json param) {
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[param["ptype"].get<std::string>()].first];
        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[v["resultType"].get<std::string>()].first];

    Argument resultArg = { v["resultArg"]["kind"].get<ArgumentTag>(), v["resultArg"]["location"].get<uint32_t>() }; 
    const RefMask mask = jsonLoadRefMask(v["mixedStackMask"]);

    std::vector<InterpOp*> body;
    auto jbody = v["body"];
    std::transform(jbody.cbegin(), jbody.cend(), std::back_inserter(body), [](json jop) {
        return InterpOp::jparse(jop);
    });

    return new BSQInvokeBodyDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, resultArg, v["scalarStackBytes"].get<size_t>(), v["mixedStackBytes"].get<size_t>(), mask, v["maskSlots"].get<uint32_t>(), body, v["argmaskSize"].get<uint32_t>());
}

BSQInvokePrimitiveDecl* BSQInvokePrimitiveDecl::jsonLoad(json v)
{
    auto ikey = Environment::g_invokenameToIDMap[v["ikey"].get<std::string>()];
    auto srcfile = v["srcFile"].get<std::string>();
    auto recursive = v["recursive"].get<bool>();

    std::vector<BSQFunctionParameter> params;
    auto jparams = v["params"];
    std::transform(jparams.cbegin(), jparams.cend(), std::back_inserter(params), [](json param) {
        auto ptype = BSQType::g_typetable[Environment::g_typenameToIDMap[param["ptype"].get<std::string>()].first];
        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[Environment::g_typenameToIDMap[v["resultType"].get<std::string>()].first];

    const RefMask mask = jsonLoadRefMask(v["mixedStackMask"]);

    const BSQType* enclosingtype = nullptr;
    if(v.contains("enclosingtype") && v["enclosingtype"].is_string())
    {
       enclosingtype = BSQType::g_typetable[Environment::g_typenameToIDMap[v["enclosingtype"].get<std::string>()].first];
    }

    std::string implkeyname = v["implkeyname"].get<std::string>();
    BSQPrimitiveImplTag implkey = Environment::g_primitiveinvokenameToIDMap[implkeyname];
    
    std::map<std::string, std::pair<uint32_t, const BSQType*>> scalaroffsetMap;
    auto jsom = v["scalaroffsetMap"];
    std::for_each(jsom.cbegin(), jsom.cend(), [&scalaroffsetMap](json so) {
         auto name = so["name"].get<std::string>();

        auto minfo = so["info"];
        auto offset = minfo[0].get<uint32_t>();
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[minfo[1].get<std::string>()].first];

        scalaroffsetMap[name] = {offset, otype};
    });

    std::map<std::string, std::pair<uint32_t, const BSQType*>> mixedoffsetMap;
    auto jmom = v["mixedoffsetMap"];
    std::for_each(jmom.cbegin(), jmom.cend(), [&mixedoffsetMap](json mo) {
        auto name = mo["name"].get<std::string>();

        auto minfo = mo["info"];
        auto offset = minfo[0].get<uint32_t>();
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[minfo[1].get<std::string>()].first];

        mixedoffsetMap[name] = {offset, otype};
    });

    std::map<std::string, const BSQType*> binds;
    auto jbinds = v["binds"];
    std::for_each(jbinds.cbegin(), jbinds.cend(), [&binds](json b) {
        auto name = b["name"].get<std::string>();
        auto otype = BSQType::g_typetable[Environment::g_typenameToIDMap[b["ttype"].get<std::string>()].first];

        binds[name] = otype;
    });

    std::map<std::string, BSQPCode*> pcodes;
    auto jpcodes = v["pcodes"];
    std::for_each(jpcodes.cbegin(), jpcodes.cend(), [&pcodes](json pcode) {
        auto name = pcode["name"].get<std::string>();

        auto pc = pcode["pc"];
        auto code = Environment::g_invokenameToIDMap[pc["code"].get<std::string>()];

        std::vector<Argument> cargs;
        auto jcargs = pc["cargs"];
        std::transform(jcargs.cbegin(), jcargs.cend(), std::back_inserter(cargs), [](json carg) {
            return Argument{ carg["kind"].get<ArgumentTag>(), carg["location"].get<uint32_t>() }; 
        });

        pcodes[name] = new BSQPCode(code, cargs);
    });

    return new BSQInvokePrimitiveDecl(j_name(v), ikey, srcfile, j_sinfo(v), recursive, params, rtype, v["scalarStackBytes"].get<size_t>(), v["mixedStackBytes"].get<size_t>(), mask, v["maskSlots"].get<uint32_t>(), enclosingtype, implkey, implkeyname, scalaroffsetMap, mixedoffsetMap, binds, pcodes);
}
