//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqinvoke.h"
#include "bsqlist.h"
#include "bsqmap.h"

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
        return internRefMask(mstr);
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
    return MarshalEnvironment::g_typenameToIdMap.at(tstr);
}

std::string j_name(json v)
{
    return v["name"].get<std::string>();
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
    if(v.is_null())
    {
        return;
    }

    auto varray = v["vtable"];
    if(varray.is_array())
    {
        for(size_t i = 0; i < varray.size(); ++i)
        {
            auto ventry = varray.at(i);
            auto vcall = ventry["vcall"].get<std::string>();
            auto inv = ventry["inv"].get<std::string>();

            vtable[MarshalEnvironment::g_vinvokeToIdMap[vcall]] = MarshalEnvironment::g_invokeToIdMap[inv];
        }
    }
}

const BSQType* jsonLoadStringOfType(json v)
{
    return CONS_BSQ_STRING_TYPE(j_tkey(v), j_name(v));
}

const BSQType* jsonLoadDataStringType(json v)
{
    return CONS_BSQ_STRING_TYPE(j_tkey(v), j_name(v));
}

const BSQType* jsonLoadDataBufferType(json v)
{
    return CONS_BSQ_BYTE_BUFFER_TYPE(j_tkey(v), j_name(v));
}

const BSQType* jsonLoadEnumType(json v)
{
    std::vector<std::string> enumnames;
    auto jenumnames = v["enumnames"]; 
    std::transform(jenumnames.cbegin(), jenumnames.cend(), std::back_inserter(enumnames), [](json arg) {
        return arg.get<std::string>();
    });

    return CONS_BSQ_ENUM_TYPE(j_tkey(v), j_name(v), enumnames);
}

const BSQType* jsonLoadTupleType(json v, bool isref)
{
    auto tid = j_tkey(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v["vtable"]);

    BSQTupleIndex maxIndex = v["maxIndex"].get<BSQTupleIndex>();

    std::vector<BSQTypeID> ttypes;
    auto ttlist = v["ttypes"];
    std::transform(ttlist.cbegin(), ttlist.cend(), std::back_inserter(ttypes), [](json ttype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ttype.get<std::string>());
    });

    std::vector<size_t> idxoffsets;
    auto idxlist = v["idxoffsets"];
    std::transform(idxlist.cbegin(), idxlist.cend(), std::back_inserter(idxoffsets), [](json offset) {
        return offset.get<size_t>();
    });

    if(isref) 
    {
        return new BSQTupleRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), maxIndex, ttypes, idxoffsets);
    }
    else 
    {
        auto norefs = v["norefs"].get<bool>();
        BSQTypeID boxedtype = 0;
        if(v["boxedtype"].is_string())
        {
            boxedtype = MarshalEnvironment::g_typenameToIdMap.at(v["boxedtype"].get<std::string>());
        }
        return new BSQTupleStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), norefs, boxedtype, maxIndex, ttypes, idxoffsets);
    }
}

const BSQType* jsonLoadRecordType(json v, bool isref)
{
    auto tid = j_tkey(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v["vtable"]);

    std::vector<BSQRecordPropertyID> propertynames;
    auto pnlist = v["propertynames"];
    std::transform(pnlist.cbegin(), pnlist.cend(), std::back_inserter(propertynames), [](json prop) {
        return MarshalEnvironment::g_propertyToIdMap.at(prop.get<std::string>());
    });

    std::vector<BSQTypeID> propertytypes;
    auto ptlist = v["propertytypes"];
    std::transform(ptlist.cbegin(), ptlist.cend(), std::back_inserter(propertytypes), [](json rtype) {
        return MarshalEnvironment::g_typenameToIdMap.at(rtype.get<std::string>());
    });

    std::vector<size_t> propertyoffsets;
    auto polist = v["propertyoffsets"];
    std::transform(polist.cbegin(), polist.cend(), std::back_inserter(propertyoffsets), [](json offset) {
        return offset.get<size_t>();
    });

    if(isref) 
    {
        return new BSQRecordRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), propertynames, propertytypes, propertyoffsets);
    }
    else 
    {
        auto norefs = v["norefs"].get<bool>();
        BSQTypeID boxedtype = 0;
        if(v["boxedtype"].is_string())
        {
            boxedtype = MarshalEnvironment::g_typenameToIdMap.at(v["boxedtype"].get<std::string>());
        }
        return new BSQRecordStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), norefs, boxedtype, propertynames, propertytypes, propertyoffsets);
    }
}

const BSQType* jsonLoadEntityType(json v, bool isref)
{
    auto tid = j_tkey(v);
    auto allocinfo = j_allocinfo(v);

    std::map<BSQVirtualInvokeID, BSQInvokeID> vtable;
    j_vtable(vtable, v["vtable"]);

    std::vector<BSQFieldID> fieldnames;
    auto fnlist = v["fieldnames"];
    std::transform(fnlist.cbegin(), fnlist.cend(), std::back_inserter(fieldnames), [](json fname) {
        return MarshalEnvironment::g_fieldToIdMap.at(fname.get<std::string>());
    });

    std::vector<BSQTypeID> fieldtypes;
    auto ftlist = v["fieldtypes"];
    std::transform(ftlist.cbegin(), ftlist.cend(), std::back_inserter(fieldtypes), [](json ftype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ftype.get<std::string>());
    });

    std::vector<size_t> fieldoffsets;
    auto folist = v["fieldoffsets"];
    std::transform(folist.cbegin(), folist.cend(), std::back_inserter(fieldoffsets), [](json offset) {
        return offset.get<size_t>();
    });

    if(isref) 
    {
        return new BSQEntityRefType(tid, allocinfo.heapsize, allocinfo.heapmask, vtable, j_name(v), fieldnames, fieldoffsets, fieldtypes);
    }
    else 
    {
        auto norefs = v["norefs"].get<bool>();
        BSQTypeID boxedtype = 0;
        if(v["boxedtype"].is_string())
        {
            boxedtype = MarshalEnvironment::g_typenameToIdMap.at(v["boxedtype"].get<std::string>());
        }
        return new BSQEntityStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, vtable, j_name(v), norefs, boxedtype, fieldnames, fieldoffsets, fieldtypes);
    }
}

const BSQType* jsonLoadConstructableEntityType(json v, bool isref)
{
    auto tid = j_tkey(v);
    auto allocinfo = j_allocinfo(v);

    auto oftypeid = MarshalEnvironment::g_typenameToIdMap.at(v["oftype"].get<std::string>());

    if(isref) 
    {
        return new BSQEntityConstructableRefType(tid, allocinfo.heapsize, allocinfo.heapmask, j_name(v), oftypeid);
    }
    else 
    {
        auto norefs = v["norefs"].get<bool>();
        BSQTypeID boxedtype = 0;
        if(v["boxedtype"].is_string())
        {
            boxedtype = MarshalEnvironment::g_typenameToIdMap.at(v["boxedtype"].get<std::string>());
        }
        return new BSQEntityConstructableStructType(tid, allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), norefs, boxedtype, oftypeid);
    }
}

const BSQType* jsonLoadEphemeralListType(json v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> etypes;
    auto etlist = v["etypes"];
    std::transform(etlist.cbegin(), etlist.cend(), std::back_inserter(etypes), [](json ttype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ttype.get<std::string>());
    });

    std::vector<size_t> idxoffsets;
    auto eolist = v["idxoffsets"];
    std::transform(eolist.cbegin(), eolist.cend(), std::back_inserter(idxoffsets), [](json offset) {
        return offset.get<size_t>();
    });

    auto norefs = v["norefs"].get<bool>();

    return new BSQEphemeralListType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), etypes, idxoffsets, norefs);
}


const BSQType* jsonLoadDeclOfType(json v)
{
    auto ttype = j_tkey(v);
    auto tname = j_name(v);
    auto oftypeid = MarshalEnvironment::g_typenameToIdMap.at(v["basetype"].get<std::string>());

    switch(oftypeid)
    {
    case BSQ_TYPE_ID_NAT:
        return CONS_BSQ_NAT_TYPE(ttype, tname);
    case BSQ_TYPE_ID_INT:
        return CONS_BSQ_INT_TYPE(ttype, tname);
    case BSQ_TYPE_ID_BIGNAT:
        return CONS_BSQ_BIG_NAT_TYPE(ttype, tname);
    case BSQ_TYPE_ID_BIGINT:
        return CONS_BSQ_BIG_INT_TYPE(ttype, tname);
    case BSQ_TYPE_ID_FLOAT:
        return CONS_BSQ_FLOAT_TYPE(ttype, tname);
    case BSQ_TYPE_ID_DECIMAL:
        return CONS_BSQ_DECIMAL_TYPE(ttype, tname);
    case BSQ_TYPE_ID_RATIONAL:
        return CONS_BSQ_RATIONAL_TYPE(ttype, tname);
    case BSQ_TYPE_ID_DATETIME:
        return CONS_BSQ_DATE_TIME_TYPE(ttype, tname);
    case BSQ_TYPE_ID_UTC_DATETIME:
        return CONS_BSQ_UTC_DATE_TIME_TYPE(ttype, tname);
    case BSQ_TYPE_ID_CALENDAR_DATE:
        return CONS_BSQ_CALENDAR_DATE_TYPE(ttype, tname);
    case BSQ_TYPE_ID_RELATIVE_TIME:
        return CONS_BSQ_RELATIVE_TIME_TYPE(ttype, tname);
    case BSQ_TYPE_ID_TICKTIME:
        return CONS_BSQ_TICK_TIME_TYPE(ttype, tname);
    case BSQ_TYPE_ID_LOGICALTIME:
        return CONS_BSQ_LOGICAL_TIME_TYPE(ttype, tname);
    case BSQ_TYPE_ID_ISO_TIMESTAMP:
        return CONS_BSQ_ISO_TIME_STAMP_TYPE(ttype, tname);
    case BSQ_TYPE_ID_UUID4:
        return CONS_BSQ_UUID4_TYPE(ttype, tname);
    case BSQ_TYPE_ID_UUID7:
        return CONS_BSQ_UUID7_TYPE(ttype, tname);
    case BSQ_TYPE_ID_SHA_CONTENT_HASH:
        return CONS_BSQ_SHA_CONTENT_HASH_TYPE(ttype, tname); 
    case BSQ_TYPE_ID_LAT_LONG_COORDINATE:
        return CONS_BSQ_LAT_LONG_COORDINATE_TYPE(ttype, tname);
    default: {
        assert(false);
        return nullptr;
    }
    }
}

const BSQType* jsonLoadListType(json v)
{
    BSQTypeID etype = MarshalEnvironment::g_typenameToIdMap.at(v["etype"].get<std::string>());

    return CONS_BSQ_LIST_TYPE(j_tkey(v), j_name(v), etype);
}

const BSQType* jsonLoadMapType(json v)
{
    BSQTypeID ktype = MarshalEnvironment::g_typenameToIdMap.at(v["ktype"].get<std::string>());
    BSQTypeID vtype = MarshalEnvironment::g_typenameToIdMap.at(v["vtype"].get<std::string>());

    return CONS_BSQ_MAP_TYPE(j_tkey(v), j_name(v), ktype, vtype);
}

const BSQType* jsonLoadRefUnionType(json v)
{
    std::vector<BSQTypeID> subtypes;
    auto stlist = v["subtypes"];
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](json ttype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ttype.get<std::string>());
    });

    return new BSQUnionRefType(j_tkey(v), j_name(v), subtypes);
}

const BSQType* jsonLoadInlineUnionType(json v)
{
    auto allocinfo = j_allocinfo(v);

    std::vector<BSQTypeID> subtypes;
    auto stlist = v["subtypes"];
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](json ttype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ttype.get<std::string>());
    });

    return new BSQUnionInlineType(j_tkey(v), allocinfo.inlinedatasize, allocinfo.inlinedmask, j_name(v), subtypes);
}

const BSQType* jsonLoadUniversalUnionType(json v)
{
    std::vector<BSQTypeID> subtypes;
    auto stlist = v["subtypes"];
    std::transform(stlist.cbegin(), stlist.cend(), std::back_inserter(subtypes), [](json ttype) {
        return MarshalEnvironment::g_typenameToIdMap.at(ttype.get<std::string>());
    });

    return new BSQUnionUniversalType(j_tkey(v), j_name(v), subtypes);
}

enum class ICPPParseTag
{
    Builtin = 0x0,
    ValidatorTag,
    BoxedStructTag,
    EnumTag,
    StringOfTag,
    DataStringTag,
    DataBufferTag,
    TupleStructTag,
    TupleRefTag,
    RecordStructTag,
    RecordRefTag,
    EntityObjectStructTag,
    EntityObjectRefTag,
    EntityConstructableStructTag,
    EntityConstructableRefTag,
    EphemeralListTag,
    EntityDeclOfTag,
    ListTag,
    StackTag,
    QueueTag,
    SetTag,
    MapTag,
    RefUnionTag,
    InlineUnionTag,
    UniversalUnionTag
};

void jsonLoadBSQTypeDecl(json v)
{
    const BSQType* ttype = nullptr;

    ICPPParseTag ptag = v["ptag"].get<ICPPParseTag>();
    assert(ptag != ICPPParseTag::Builtin);
    assert(ptag != ICPPParseTag::BoxedStructTag);

    switch(ptag)
    {
    case ICPPParseTag::EnumTag:
        ttype = jsonLoadEnumType(v);
        break;
    case ICPPParseTag::StringOfTag:
        ttype = jsonLoadStringOfType(v);
        break;
    case ICPPParseTag::DataStringTag:
        ttype = jsonLoadDataStringType(v);
        break;
    case ICPPParseTag::DataBufferTag:
        ttype = jsonLoadDataBufferType(v);
        break;
    case ICPPParseTag::TupleStructTag:
        ttype = jsonLoadTupleType(v, false);
        break;
    case ICPPParseTag::TupleRefTag:
        ttype = jsonLoadTupleType(v, true);
        break;
    case ICPPParseTag::RecordStructTag:
        ttype = jsonLoadRecordType(v, false);
        break;
    case ICPPParseTag::RecordRefTag:
        ttype = jsonLoadRecordType(v, true);
        break;
    case ICPPParseTag::EntityObjectStructTag:
        ttype = jsonLoadEntityType(v, false);
        break;
    case ICPPParseTag::EntityObjectRefTag:
        ttype = jsonLoadEntityType(v, true);
        break;
    case ICPPParseTag::EntityConstructableStructTag:
        ttype = jsonLoadConstructableEntityType(v, false);
        break;
    case ICPPParseTag::EntityConstructableRefTag:
        ttype = jsonLoadConstructableEntityType(v, true);
        break;
    case ICPPParseTag::EphemeralListTag:
        ttype = jsonLoadEphemeralListType(v);
        break;
    case ICPPParseTag::EntityDeclOfTag:
        ttype = jsonLoadDeclOfType(v);
        break;
    case ICPPParseTag::ListTag:
        ttype = jsonLoadListType(v);
        break;
    case ICPPParseTag::StackTag:
        assert(false);
        break;
    case ICPPParseTag::QueueTag:
        assert(false);
        break;
    case ICPPParseTag::SetTag:
        assert(false);
        break;
    case ICPPParseTag::MapTag:
        ttype = jsonLoadMapType(v);
        break;
    case ICPPParseTag::RefUnionTag:
        ttype = jsonLoadRefUnionType(v);
        break;
    case ICPPParseTag::InlineUnionTag:
        ttype = jsonLoadInlineUnionType(v);
        break;
    case ICPPParseTag::UniversalUnionTag:
        ttype = jsonLoadUniversalUnionType(v);
        break;
    default:
        assert(false);
        break;
    }

    BSQType::g_typetable[ttype->tid] = ttype;
}

void jsonLoadBSQLiteralDecl(json v, size_t& storageOffset, const BSQType*& gtype, std::string& lval)
{
    storageOffset = v["offset"].get<size_t>();
    gtype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(v["storage"].get<std::string>())];
    lval = v["value"].get<std::string>();
}

void jsonLoadBSQConstantDecl(json v, size_t& storageOffset, BSQInvokeID& ikey, const BSQType*& gtype)
{
    storageOffset = v["storageOffset"].get<size_t>();
    ikey = MarshalEnvironment::g_invokeToIdMap.at(v["valueInvoke"].get<std::string>());
    gtype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(v["ctype"].get<std::string>())];
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

    BSQInvokeDecl::g_invokes[dcl->ikey] = dcl;
}

BSQInvokeBodyDecl* BSQInvokeBodyDecl::jsonLoad(json v)
{
    auto ikey = MarshalEnvironment::g_invokeToIdMap.at(v["ikey"].get<std::string>());

    auto srcfile = v["srcFile"].get<std::string>();
    auto recursive = v["recursive"].get<bool>();

    std::vector<BSQFunctionParameter> params;
    auto jparams = v["params"];
    std::transform(jparams.cbegin(), jparams.cend(), std::back_inserter(params), [](json param) {
        auto ptype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(param["ptype"].get<std::string>())];
        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(v["resultType"].get<std::string>())];

    std::vector<ParameterInfo> paraminfo;
    auto jparaminfo = v["paraminfo"];
    std::transform(jparaminfo.cbegin(), jparaminfo.cend(), std::back_inserter(paraminfo), [](json param) {
        auto offset = param["poffset"].get<uint32_t>();
        return ParameterInfo{offset};
    });

    Argument resultArg = { v["resultArg"]["kind"].get<ArgumentTag>(), v["resultArg"]["location"].get<uint32_t>() };

    std::vector<InterpOp*> body;
    auto jbody = v["body"];
    std::transform(jbody.cbegin(), jbody.cend(), std::back_inserter(body), [](json jop) {
        return InterpOp::jparse(jop);
    });

    return new BSQInvokeBodyDecl(j_name(v), ikey, srcfile, j_sinfoStart(v), j_sinfoEnd(v), recursive, params, rtype, paraminfo, resultArg, v["stackBytes"].get<size_t>(), v["maskSlots"].get<uint32_t>(), body, v["argmaskSize"].get<uint32_t>());
}

BSQInvokePrimitiveDecl* BSQInvokePrimitiveDecl::jsonLoad(json v)
{
    auto ikey = MarshalEnvironment::g_invokeToIdMap.at(v["ikey"].get<std::string>());

    auto srcfile = v["srcFile"].get<std::string>();
    auto recursive = v["recursive"].get<bool>();

    std::vector<BSQFunctionParameter> params;
    auto jparams = v["params"];
    std::transform(jparams.cbegin(), jparams.cend(), std::back_inserter(params), [](json param) {
        auto ptype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(param["ptype"].get<std::string>())];
        return BSQFunctionParameter{j_name(param), ptype};
    });
    auto rtype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(v["resultType"].get<std::string>())];

    const BSQType* enclosingtype = nullptr;
    if(v.contains("enclosingtype") && v["enclosingtype"].is_string())
    {
       enclosingtype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(v["enclosingtype"].get<std::string>())];
    }

    std::string implkeyname = v["implkeyname"].get<std::string>();
    BSQPrimitiveImplTag implkey = MarshalEnvironment::g_primitiveinvokenameToIDMap.at(implkeyname);

    std::map<std::string, const BSQType*> binds;
    auto jbinds = v["binds"];
    std::for_each(jbinds.cbegin(), jbinds.cend(), [&binds](json b) {
        auto name = b["name"].get<std::string>();
        auto otype = BSQType::g_typetable[MarshalEnvironment::g_typenameToIdMap.at(b["ttype"].get<std::string>())];

        binds[name] = otype;
    });

    std::map<std::string, BSQPCode*> pcodes;
    auto jpcodes = v["pcodes"];
    std::for_each(jpcodes.cbegin(), jpcodes.cend(), [&pcodes](json pcode) {
        auto name = pcode["name"].get<std::string>();

        auto pc = pcode["pc"];
        auto code = MarshalEnvironment::g_invokeToIdMap[pc["code"].get<std::string>()];

        std::vector<uint32_t> cargpos;
        auto jcargs = pc["cargs"];
        std::transform(jcargs.cbegin(), jcargs.cend(), std::back_inserter(cargpos), [](json carg) {
            return carg.get<uint32_t>(); 
        });

        pcodes[name] = new BSQPCode(code, cargpos);
    });

    return new BSQInvokePrimitiveDecl(j_name(v), ikey, srcfile, j_sinfoStart(v), j_sinfoEnd(v), recursive, params, rtype, v["stackBytes"].get<size_t>(), v["maskSlots"].get<uint32_t>(), enclosingtype, implkey, implkeyname, binds, pcodes);
}
