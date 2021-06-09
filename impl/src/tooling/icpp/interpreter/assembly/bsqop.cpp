//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqop.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

boost::json::value jsonGet(boost::json::value val, const char* prop)
{
    assert(val.is_object());
    return val.as_object().at(prop);
}

bool jsonGetAsBool(boost::json::value val, const char* prop)
{
    return jsonGet(val, prop).as_bool();
}

template <typename T>
T jsonGetAsTag(boost::json::value val, const char* prop)
{
    return (T)jsonGet(val, prop).as_uint64();
}

template <typename T>
T jsonGetAsInt(boost::json::value val, const char* prop)
{
    return (T)jsonGet(val, prop).as_int64();
}

template <typename T>
T jsonGetAsUInt(boost::json::value val, const char* prop)
{
    return (T)jsonGet(val, prop).as_uint64();
}

std::string jsonGetAsString(boost::json::value val, const char* prop)
{
    return std::string(jsonGet(val, prop).as_string().cbegin(), jsonGet(val, prop).as_string().cend());
}

Argument jsonParse_Argument(boost::json::value val)
{
    return Argument{ jsonGetAsTag<ArgumentTag>(val, "kind"), jsonGetAsUInt<uint32_t>(val, "location") };
}

TargetVar jsonParse_TargetVar(boost::json::value val)
{
    return TargetVar{ jsonGetAsInt<ArgumentTag>(val, "kind"), jsonGetAsUInt<uint32_t>(val, "offset") };
}

SourceInfo jsonParse_SourceInfo(boost::json::value val)
{
    return SourceInfo{ jsonGetAsUInt<uint32_t>(val, "line"), jsonGetAsUInt<uint32_t>(val, "column") };
}

BSQGuard jsonParse_BSQGuard(boost::json::value val)
{
    return BSQGuard{ jsonGetAsUInt<uint32_t>(val, "gmaskoffset"), jsonGetAsInt<int32_t>(val, "gindex"), jsonGetAsInt<int32_t>(val, "gvaroffset") };
}

BSQStatementGuard jsonParse_BSQStatementGuard(boost::json::value val)
{
    return BSQStatementGuard{ jsonParse_BSQGuard(jsonGet(val, "guard")), jsonParse_Argument(jsonGet(val, "defaultvar")), jsonGetAsBool(val, "usedefaulton"), jsonGetAsBool(val, "enabled") };
}

const BSQType* jsonParse_BSQType(boost::json::value val)
{
     auto tname = std::string(val.as_string().cbegin(), val.as_string().cend());
    return Environment::g_typenameToDeclMap[tname];
}

BSQRecordPropertyID jsonParse_BSQRecordPropertyID(boost::json::value val)
{
    auto tname = std::string(val.as_string().cbegin(), val.as_string().cend());
    return Environment::g_propertynameToIDMap[tname];
}

BSQFieldID jsonParse_BSQFieldID(boost::json::value val)
{
    auto tname = std::string(val.as_string().cbegin(), val.as_string().cend());
    return Environment::g_fieldnameToIDMap[tname];
}

SourceInfo j_sinfo(boost::json::value val)
{
    return jsonParse_SourceInfo(jsonGet(val, "sinfo"));
}

TargetVar j_trgt(boost::json::value val)
{
    return jsonParse_TargetVar(jsonGet(val, "trgt"));
}

Argument j_arg(boost::json::value val)
{
    return jsonParse_Argument(jsonGet(val, "arg"));
}

const BSQType* j_oftype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "oftype"));
}

const BSQType* j_argtype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "argtype"));
}

const BSQType* j_layouttype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "layouttype"));
}

const BSQType* j_flowtype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "flowtype"));
}

const BSQType* j_intotype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "intotype"));
}

const BSQType* j_trgttype(boost::json::value val)
{
    return jsonParse_BSQType(jsonGet(val, "trgttype"));
}

BSQGuard j_guard(boost::json::value v)
{
    return jsonParse_BSQGuard(jsonGet(v, "guard"));
}

BSQStatementGuard j_sguard(boost::json::value v)
{
    return jsonParse_BSQStatementGuard(jsonGet(v, "sguard"));
}

DeadFlowOp* DeadFlowOp::jparse(boost::json::value v)
{
    return new DeadFlowOp(j_sinfo(v));
}

AbortOp* AbortOp::jparse(boost::json::value v)
{
    return new AbortOp(j_sinfo(v), jsonGetAsString(v, "msg"));
}

AssertOp* AssertOp::jparse(boost::json::value v)
{
    return new AssertOp(j_sinfo(v), j_arg(v), jsonGetAsString(v, "msg"));
}

DebugOp* DebugOp::jparse(boost::json::value v)
{
    return new DebugOp(j_sinfo(v), j_arg(v), j_argtype(v));
}

LoadUnintVariableValueOp* LoadUnintVariableValueOp::jparse(boost::json::value v)
{
    return new LoadUnintVariableValueOp(j_sinfo(v), j_trgt(v), j_oftype(v));
}

NoneInitUnionOp* NoneInitUnionOp::jparse(boost::json::value v)
{
    return new NoneInitUnionOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQUnionType*>(j_oftype(v)));
}

StoreConstantMaskValueOp* StoreConstantMaskValueOp::jparse(boost::json::value v)
{
    return new StoreConstantMaskValueOp(j_sinfo(v), jsonGetAsUInt<uint32_t>(v, "gmaskoffset"), jsonGetAsInt<int32_t>(v, "gindex"), jsonGetAsBool(v, "flag"));
}

DirectAssignOp* DirectAssignOp::jparse(boost::json::value v)
{
    return new DirectAssignOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), jsonGetAsUInt<uint32_t>(v, "size"), j_sguard(v));
}

BoxOp* BoxOp::jparse(boost::json::value v)
{
    return new BoxOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "fromtype")), j_sguard(v));
}

ExtractOp* ExtractOp::jparse(boost::json::value v)
{
    return new ExtractOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "fromtype")), j_sguard(v));
}

LoadConstOp* LoadConstOp::jparse(boost::json::value v)
{
    return new LoadConstOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v));
}

TupleHasIndexOp::TupleHasIndexOp* jparse(boost::json::value v)
{
    return new TupleHasIndexOp(j_sinfo(v), j_trgt(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonGetAsUInt<BSQTupleIndex>(v, "idx"));
}

RecordHasPropertyOp* RecordHasPropertyOp::jparse(boost::json::value v)
{
    return new RecordHasPropertyOp(j_sinfo(v), j_trgt(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(jsonGet(v, "propId")));
}

LoadTupleIndexDirectOp* LoadTupleIndexDirectOp::jparse(boost::json::value v)
{
    return new LoadTupleIndexDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonGetAsUInt<BSQTupleIndex>(v, "idx"));
}

LoadTupleIndexVirtualOp* LoadTupleIndexVirtualOp::jparse(boost::json::value v)
{
    return new LoadTupleIndexVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonGetAsUInt<BSQTupleIndex>(v, "idx"));
}

LoadTupleIndexSetGuardDirectOp* LoadTupleIndexSetGuardDirectOp::jparse(boost::json::value v)
{
    return new LoadTupleIndexSetGuardDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonGetAsUInt<BSQTupleIndex>(v, "idx"), j_guard(v));
}

LoadTupleIndexSetGuardVirtualOp* LoadTupleIndexSetGuardVirtualOp::jparse(boost::json::value v)
{
    return new LoadTupleIndexSetGuardVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonGetAsUInt<BSQTupleIndex>(v, "idx"), j_guard(v));
}

LoadRecordPropertyDirectOp* LoadRecordPropertyDirectOp::jparse(boost::json::value v)
{
    return new LoadRecordPropertyDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonParse_BSQRecordPropertyID(jsonGet(v, "propId")));
}

LoadRecordPropertyVirtualOp* LoadRecordPropertyVirtualOp::jparse(boost::json::value v)
{
    return new LoadRecordPropertyVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(jsonGet(v, "propId")));
}

LoadRecordPropertySetGuardDirectOp* LoadRecordPropertySetGuardDirectOp::jparse(boost::json::value v)
{
    return new LoadRecordPropertySetGuardDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonParse_BSQRecordPropertyID(jsonGet(v, "propId")), j_guard(v));
}

LoadRecordPropertySetGuardVirtualOp* LoadRecordPropertySetGuardVirtualOp::jparse(boost::json::value v)
{
    return new LoadRecordPropertySetGuardVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(jsonGet(v, "propId")), j_guard(v));
}

LoadEntityFieldDirectOp* LoadEntityFieldDirectOp::jparse(boost::json::value v)
{
    return new LoadEntityFieldDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonParse_BSQFieldID(jsonGet(v, "fieldId")));
}

LoadEntityFieldVirtualOp* LoadEntityFieldVirtualOp::jparse(boost::json::value v)
{
    return new LoadEntityFieldVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQFieldID(jsonGet(v, "fieldId")));
}

ProjectTupleOp* ProjectTupleOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*>> idxs;
    auto idxl = v.as_object().at("idxs").as_array();
    for(size_t i = 0; i < idxl.size(); ++i)
    {
        auto vv = idxl[i].as_array();
        idxs.push_back(std::make_tuple((BSQTupleIndex)vv[0].as_uint64(), (uint32_t)vv[1].as_uint64(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectTupleOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), idxs);
}

ProjectRecordOp* ProjectRecordOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*>> props;
    auto propl = v.as_object().at("props").as_array();
    for(size_t i = 0; i < props.size(); ++i)
    {
        auto vv = propl[i].as_array();
        props.push_back(std::make_tuple(jsonParse_BSQRecordPropertyID(vv[0]), (BSQTupleIndex)vv[1].as_uint64(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectRecordOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), props);
}

ProjectEntityOp* ProjectEntityOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*>> fields;
    auto fieldl = v.as_object().at("fields").as_array();
    for(size_t i = 0; i < fields.size(); ++i)
    {
        auto vv = fieldl[i].as_array();
        fields.push_back(std::make_tuple(jsonParse_BSQFieldID(vv[0]), (BSQTupleIndex)vv[1].as_uint64(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectEntityOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), fields);
}

UpdateTupleOp* UpdateTupleOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v.as_object().at("updates").as_array();
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i].as_array();
        updates.push_back(std::make_tuple((BSQTupleIndex)vv[0].as_uint64(), (uint32_t)vv[1].as_uint64(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateTupleOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

UpdateRecordOp* UpdateRecordOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v.as_object().at("updates").as_array();
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i].as_array();
        updates.push_back(std::make_tuple(jsonParse_BSQRecordPropertyID(vv[0]), (uint32_t)vv[1].as_uint64(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateRecordOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

UpdateEntityOp* UpdateEntityOp::jparse(boost::json::value v)
{
    std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v.as_object().at("updates").as_array();
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i].as_array();
        updates.push_back(std::make_tuple(jsonParse_BSQFieldID(vv[0]), (uint32_t)vv[1].as_uint64(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateEntityOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

LoadFromEpehmeralListOp* LoadFromEpehmeralListOp::jparse(boost::json::value v)
{
    return new LoadFromEpehmeralListOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), jsonGetAsUInt<uint32_t>(v, "slotoffset"), jsonGetAsUInt<uint32_t>(v, "index"));
}

MultiLoadFromEpehmeralListOp* MultiLoadFromEpehmeralListOp::jparse(boost::json::value v)
{
    std::vector<TargetVar> trgts;
    std::transform(v.as_object().at("trgts").as_array().cbegin(), v.as_object().at("trgts").as_array().cend(), std::back_inserter(trgts), [](boost::json::value tv) {
        return jsonParse_TargetVar(tv);
    });

    std::vector<const BSQType*> trgttypes;
    std::transform(v.as_object().at("trgttypes").as_array().cbegin(), v.as_object().at("trgttypes").as_array().cend(), std::back_inserter(trgts), [](boost::json::value tt) {
        return jsonParse_BSQType(tt);
    });

    std::vector<uint32_t> slotoffsets;
    std::transform(v.as_object().at("slotoffsets").as_array().cbegin(), v.as_object().at("slotoffsets").as_array().cend(), std::back_inserter(trgts), [](boost::json::value so) {
        return (uint32_t)so.as_uint64();
    });

    std::vector<uint32_t> indexs;
    std::transform(v.as_object().at("indexs").as_array().cbegin(), v.as_object().at("indexs").as_array().cend(), std::back_inserter(trgts), [](boost::json::value idx) {
        return (uint32_t)idx.as_uint64();
    });

    return new MultiLoadFromEpehmeralListOp(j_sinfo(v), trgts, trgttypes, j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), slotoffsets, indexs);
}

SliceEphemeralListOp* SliceEphemeralListOp::jparse(boost::json::value v)
{
    return new SliceEphemeralListOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), jsonGetAsUInt<uint32_t>(v, "slotoffsetend"), jsonGetAsUInt<uint32_t>(v, "indexend"));
}

InvokeFixedFunctionOp* InvokeFixedFunctionOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new InvokeFixedFunctionOp(j_sinfo(v), j_trgt(v), j_trgttype(v), jsonGetAsUInt<BSQInvokeID>(v, "invokeId"), args, j_sguard(v), jsonGetAsInt<int32_t>(v, "optmaskoffset"));
}

InvokeVirtualFunctionOp* InvokeVirtualFunctionOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new InvokeVirtualFunctionOp(j_sinfo(v), j_trgt(v), j_trgttype(v), jsonGetAsUInt<BSQVirtualInvokeID>(v, "invokeId"), jsonParse_BSQType(jsonGet(v, "rcvrlayouttype")), args, jsonGetAsInt<int32_t>(v, "optmaskoffset"));
}

InvokeVirtualOperatorOp* InvokeVirtualOperatorOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new InvokeVirtualOperatorOp(j_sinfo(v), j_trgt(v), j_trgttype(v), jsonGetAsUInt<BSQVirtualInvokeID>(v, "invokeId"), args);
}

ConstructorTupleOp* ConstructorTupleOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorTupleOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

ConstructorTupleFromEphemeralListOp* ConstructorTupleFromEphemeralListOp::jparse(boost::json::value v)
{
    return new ConstructorTupleFromEphemeralListOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)));
}

ConstructorRecordOp* ConstructorRecordOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorRecordOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

ConstructorRecordFromEphemeralListOp* ConstructorRecordFromEphemeralListOp::jparse(boost::json::value v)
{
    std::vector<uint32_t> proppositions;
    std::transform(v.as_object().at("proppositions").as_array().cbegin(), v.as_object().at("proppositions").as_array().cend(), std::back_inserter(proppositions), [](boost::json::value pos) {
        return (uint32_t)pos.as_uint64();
    });

    return new ConstructorRecordFromEphemeralListOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), proppositions);
}

EphemeralListExtendOp* EphemeralListExtendOp::jparse(boost::json::value v)
{
    std::vector<Argument> ext;
    std::transform(v.as_object().at("ext").as_array().cbegin(), v.as_object().at("ext").as_array().cend(), std::back_inserter(ext), [](boost::json::value ee) {
        return jsonParse_Argument(ee);
    });

    return new EphemeralListExtendOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(jsonParse_BSQType(jsonGet(v, "resultType"))), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), ext);
}

ConstructorEphemeralListOp* ConstructorEphemeralListOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorEphemeralListOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_oftype(v)), args);
}

ConstructorPrimaryCollectionEmptyOp* ConstructorPrimaryCollectionEmptyOp::jparse(boost::json::value v)
{
    return new ConstructorPrimaryCollectionEmptyOp(j_sinfo(v), j_trgt(v), j_oftype(v));
}

ConstructorPrimaryCollectionSingletonsOp* ConstructorPrimaryCollectionSingletonsOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorPrimaryCollectionSingletonsOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}
ConstructorPrimaryCollectionCopiesOp* ConstructorPrimaryCollectionCopiesOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorPrimaryCollectionCopiesOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

ConstructorPrimaryCollectionMixedOp* ConstructorPrimaryCollectionMixedOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ConstructorPrimaryCollectionMixedOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

PrefixNotOp* PrefixNotOp::jparse(boost::json::value v)
{
    return new PrefixNotOp(j_sinfo(v), j_trgt(v), j_arg(v));
}

AllTrueOp* AllTrueOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new AllTrueOp(j_sinfo(v), j_trgt(v), args);
}

SomeTrueOp* SomeTrueOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new SomeTrueOp(j_sinfo(v), j_trgt(v), args);
}

BinKeyEqFastOp* BinKeyEqFastOp::jparse(boost::json::value v)
{
    return new BinKeyEqFastOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_Argument(jsonGet(v, "argr"))); 
}
    
BinKeyEqStaticOp* BinKeyEqStaticOp::jparse(boost::json::value v)
{
    return new BinKeyEqStaticOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_BSQType(jsonGet(v, "argllayout")), jsonParse_Argument(jsonGet(v, "argr")), jsonParse_BSQType(jsonGet(v, "argrlayout"))); 
}

BinKeyEqVirtualOp* BinKeyEqVirtualOp::jparse(boost::json::value v)
{
    return new BinKeyEqVirtualOp(j_sinfo(v), j_trgt(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_BSQType(jsonGet(v, "argllayout")), jsonParse_Argument(jsonGet(v, "argr")), jsonParse_BSQType(jsonGet(v, "argrlayout"))); 
}

BinKeyLessFastOp* BinKeyLessFastOp::jparse(boost::json::value v)
{
    return new BinKeyLessFastOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_Argument(jsonGet(v, "argr"))); 
}
    
BinKeyLessStaticOp* BinKeyLessStaticOp::jparse(boost::json::value v)
{
    return new BinKeyLessStaticOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_BSQType(jsonGet(v, "argllayout")), jsonParse_Argument(jsonGet(v, "argr")), jsonParse_BSQType(jsonGet(v, "argrlayout"))); 
}

BinKeyLessVirtualOp* BinKeyLessVirtualOp::jparse(boost::json::value v)
{
    return new BinKeyLessVirtualOp(j_sinfo(v), j_trgt(v), jsonParse_Argument(jsonGet(v, "argl")), jsonParse_BSQType(jsonGet(v, "argllayout")), jsonParse_Argument(jsonGet(v, "argr")), jsonParse_BSQType(jsonGet(v, "argrlayout"))); 
}

TypeIsNoneOp* TypeIsNoneOp::jparse(boost::json::value v)
{
    return new TypeIsNoneOp(j_sinfo(v), j_trgt(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "arglayout")), j_sguard(v));
}

TypeIsSomeOp* TypeIsSomeOp::jparse(boost::json::value v)
{
    return new TypeIsSomeOp(j_sinfo(v), j_trgt(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "arglayout")), j_sguard(v));
}

TypeTagIsOp* TypeTagIsOp::jparse(boost::json::value v)
{
    return new TypeTagIsOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "arglayout")), j_sguard(v));
}

TypeTagSubtypeOfOp* TypeTagSubtypeOfOp::jparse(boost::json::value v)
{
    return new TypeTagSubtypeOfOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQUnionType*>(j_oftype(v)), j_arg(v), jsonParse_BSQType(jsonGet(v, "arglayout")), j_sguard(v));
}

JumpOp* JumpOp::jparse(boost::json::value v)
{
    return new JumpOp(j_sinfo(v), jsonGetAsUInt<uint32_t>(v, "offset"), jsonGetAsString(v, "label"));
}

JumpCondOp* JumpCondOp::jparse(boost::json::value v)
{
    return new JumpCondOp(j_sinfo(v), j_arg(v), jsonGetAsUInt<uint32_t>(v, "toffset"), jsonGetAsUInt<uint32_t>(v, "foffset"), jsonGetAsString(v, "tlabel"), jsonGetAsString(v, "flabel"));
}

JumpNoneOp* JumpNoneOp::jparse(boost::json::value v)
{
    return new JumpNoneOp(j_sinfo(v), j_arg(v), jsonParse_BSQType(jsonGet(v, "arglayout")), jsonGetAsUInt<uint32_t>(v, "noffset"), jsonGetAsUInt<uint32_t>(v, "soffset"), jsonGetAsString(v, "nlabel"), jsonGetAsString(v, "slabel"));
}

RegisterAssignOp* RegisterAssignOp::jparse(boost::json::value v)
{
    return new RegisterAssignOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v), j_sguard(v));
}

ReturnAssignOp* ReturnAssignOp::jparse(boost::json::value v)
{
    return new ReturnAssignOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v));
}

ReturnAssignOfConsOp* ReturnAssignOfConsOp::jparse(boost::json::value v)
{
    std::vector<Argument> args;
    std::transform(v.as_object().at("args").as_array().cbegin(), v.as_object().at("args").as_array().cend(), std::back_inserter(args), [](boost::json::value arg) {
        return jsonParse_Argument(arg);
    });

    return new ReturnAssignOfConsOp(j_sinfo(v), j_trgt(v), args, j_oftype(v));
}

VarLifetimeStartOp* VarLifetimeStartOp::jparse(boost::json::value v)
{
    return new VarLifetimeStartOp(j_sinfo(v), jsonParse_Argument(jsonGet(v, "homelocation")), j_oftype(v), jsonGetAsString(v, "name"));
}

VarLifetimeEndOp* VarLifetimeEndOp::jparse(boost::json::value v)
{
    return new VarLifetimeEndOp(j_sinfo(v), jsonGetAsString(v, "name"));
}

template <OpCodeTag tag>
PrimitiveNegateOperatorOp<tag>* PrimitiveNegateOperatorOp<tag>::jparse(boost::json::value v)
{
    return new PrimitiveNegateOperatorOp<tag>(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v));
}

template <OpCodeTag tag>
PrimitiveBinaryOperatorOp<tag>* PrimitiveBinaryOperatorOp<tag>::jparse(boost::json::value v)
{
    return new PrimitiveBinaryOperatorOp<tag>(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "larg")), jsonParse_Argument(jsonGet(v, "rarg")));
}

template <OpCodeTag tag>
PrimitiveBinaryCompareOp<tag>* PrimitiveBinaryCompareOp<tag>::jparse(boost::json::value v)
{
    return new PrimitiveBinaryCompareOp<tag>(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(jsonGet(v, "larg")), jsonParse_Argument(jsonGet(v, "rarg")));
}


InterpOp* InterpOp::jparse(boost::json::value v)
{
    auto tag = jsonGetAsTag<OpCodeTag>(v, "tag");

    switch(tag)
    {
    case OpCodeTag::DeadFlowOp:
        return DeadFlowOp::jparse(v);
    case OpCodeTag::AbortOp:
        return AbortOp::jparse(v);
    case OpCodeTag::AssertOp:
        return AssertOp::jparse(v);
    case OpCodeTag::DebugOp:
        return DebugOp::jparse(v);
    case OpCodeTag::LoadUnintVariableValueOp:
        return LoadUnintVariableValueOp::jparse(v);
    case OpCodeTag::NoneInitUnionOp:
        return NoneInitUnionOp::jparse(v);
    case OpCodeTag::StoreConstantMaskValueOp:
        return StoreConstantMaskValueOp::jparse(v);
    case OpCodeTag::DirectAssignOp:
        return DirectAssignOp::jparse(v);
    case OpCodeTag::BoxOp:
        return BoxOp::jparse(v);
    case OpCodeTag::ExtractOp:
        return ExtractOp::jparse(v);
    case OpCodeTag::LoadConstOp:
        return LoadConstOp::jparse(v);
    case OpCodeTag::TupleHasIndexOp:
        return TupleHasIndexOp::jparse(v);
    case OpCodeTag::RecordHasPropertyOp:
        return RecordHasPropertyOp::jparse(v);
    case OpCodeTag::LoadTupleIndexDirectOp:
        return LoadTupleIndexDirectOp::jparse(v);
    case OpCodeTag::LoadTupleIndexVirtualOp:
        return LoadTupleIndexVirtualOp::jparse(v);
    case OpCodeTag::LoadTupleIndexSetGuardDirectOp:
        return LoadTupleIndexSetGuardDirectOp::jparse(v);
    case OpCodeTag::LoadTupleIndexSetGuardVirtualOp:
        return LoadTupleIndexSetGuardVirtualOp::jparse(v);
    case OpCodeTag::LoadRecordPropertyDirectOp:
        return LoadRecordPropertyDirectOp::jparse(v);
    case OpCodeTag::LoadRecordPropertyVirtualOp:
        return LoadRecordPropertyVirtualOp::jparse(v);
    case OpCodeTag::LoadRecordPropertySetGuardDirectOp:
        return LoadRecordPropertySetGuardDirectOp::jparse(v);
    case OpCodeTag::LoadRecordPropertySetGuardVirtualOp:
        return LoadRecordPropertySetGuardVirtualOp::jparse(v);
    case OpCodeTag::LoadEntityFieldDirectOp:
        return LoadEntityFieldDirectOp::jparse(v);
    case OpCodeTag::LoadEntityFieldVirtualOp:
        return LoadEntityFieldVirtualOp::jparse(v);
    case OpCodeTag::ProjectTupleOp:
        return ProjectTupleOp::jparse(v);
    case OpCodeTag::ProjectRecordOp:
        return ProjectRecordOp::jparse(v);
    case OpCodeTag::ProjectEntityOp:
        return ProjectEntityOp::jparse(v);
    case OpCodeTag::UpdateTupleOp:
        return UpdateTupleOp::jparse(v);
    case OpCodeTag::UpdateRecordOp:
        return UpdateRecordOp::jparse(v);
    case OpCodeTag::UpdateEntityOp:
        return UpdateEntityOp::jparse(v);
    case OpCodeTag::LoadFromEpehmeralListOp:
        return LoadFromEpehmeralListOp::jparse(v);
    case OpCodeTag::MultiLoadFromEpehmeralListOp:
        return MultiLoadFromEpehmeralListOp::jparse(v);
    case OpCodeTag::SliceEphemeralListOp:
        return SliceEphemeralListOp::jparse(v);
    case OpCodeTag::InvokeFixedFunctionOp:
        return InvokeFixedFunctionOp::jparse(v);
    case OpCodeTag::InvokeVirtualFunctionOp:
        return InvokeVirtualFunctionOp::jparse(v);
    case OpCodeTag::InvokeVirtualOperatorOp:
        return InvokeVirtualOperatorOp::jparse(v);
    case OpCodeTag::ConstructorTupleOp:
        return ConstructorTupleOp::jparse(v);
    case OpCodeTag::ConstructorTupleFromEphemeralListOp:
        return ConstructorTupleFromEphemeralListOp::jparse(v);
    case OpCodeTag::ConstructorRecordOp:
        return ConstructorRecordOp::jparse(v);
    case OpCodeTag::ConstructorRecordFromEphemeralListOp:
        return ConstructorTupleFromEphemeralListOp::jparse(v);
    case OpCodeTag::EphemeralListExtendOp:
        return EphemeralListExtendOp::jparse(v);
    case OpCodeTag::ConstructorEphemeralListOp:
        return ConstructorEphemeralListOp::jparse(v);
    case OpCodeTag::ConstructorPrimaryCollectionEmptyOp:
        return ConstructorPrimaryCollectionEmptyOp::jparse(v);
    case OpCodeTag::ConstructorPrimaryCollectionSingletonsOp:
        return ConstructorPrimaryCollectionSingletonsOp::jparse(v);
    case OpCodeTag::ConstructorPrimaryCollectionCopiesOp:
        return ConstructorPrimaryCollectionCopiesOp::jparse(v);
    case OpCodeTag::ConstructorPrimaryCollectionMixedOp:
        return ConstructorPrimaryCollectionMixedOp::jparse(v);
    case OpCodeTag::PrefixNotOp:
        return PrefixNotOp::jparse(v);
    case OpCodeTag::AllTrueOp:
        return AllTrueOp::jparse(v);
    case OpCodeTag::SomeTrueOp:
        return SomeTrueOp::jparse(v);
    case OpCodeTag::BinKeyEqFastOp:
        return BinKeyEqFastOp::jparse(v);
    case OpCodeTag::BinKeyEqStaticOp:
        return BinKeyEqStaticOp::jparse(v);
    case OpCodeTag::BinKeyEqVirtualOp:
        return BinKeyEqVirtualOp::jparse(v);
    case OpCodeTag::BinKeyLessFastOp:
        return BinKeyLessFastOp::jparse(v);
    case OpCodeTag::BinKeyLessStaticOp:
        return BinKeyLessStaticOp::jparse(v);
    case OpCodeTag::BinKeyLessVirtualOp:
        return BinKeyLessVirtualOp::jparse(v);
    case OpCodeTag::TypeIsNoneOp:
        return TypeIsNoneOp::jparse(v);
    case OpCodeTag::TypeIsSomeOp:
        return TypeIsSomeOp::jparse(v);
    case OpCodeTag::TypeTagIsOp:
        return TypeTagIsOp::jparse(v);
    case OpCodeTag::TypeTagSubtypeOfOp:
        return TypeTagSubtypeOfOp::jparse(v);
    case OpCodeTag::JumpOp:
        return JumpOp::jparse(v);
    case OpCodeTag::JumpCondOp:
        return JumpCondOp::jparse(v);
    case OpCodeTag::JumpNoneOp:
        return JumpNoneOp::jparse(v);
    case OpCodeTag::RegisterAssignOp:
        return RegisterAssignOp::jparse(v);
    case OpCodeTag::ReturnAssignOp:
        return ReturnAssignOp::jparse(v);
    case OpCodeTag::ReturnAssignOfConsOp:
        return ReturnAssignOfConsOp::jparse(v);
    case OpCodeTag::VarLifetimeStartOp:
        return VarLifetimeStartOp::jparse(v);
    case OpCodeTag::VarLifetimeEndOp:
        return VarLifetimeEndOp::jparse(v);
    case OpCodeTag::NegateIntOp:
        return PrimitiveNegateOperatorOp<OpCodeTag::NegateIntOp>::jparse(v);
    case OpCodeTag::NegateBigIntOp:
        return PrimitiveNegateOperatorOp<OpCodeTag::NegateBigIntOp>::jparse(v);
    case OpCodeTag::NegateRationalOp:
        return PrimitiveNegateOperatorOp<OpCodeTag::NegateRationalOp>::jparse(v);
    case OpCodeTag::NegateFloatOp:
        return PrimitiveNegateOperatorOp<OpCodeTag::NegateFloatOp>::jparse(v);
    case OpCodeTag::NegateDecimalOp:
        return PrimitiveNegateOperatorOp<OpCodeTag::NegateDecimalOp>::jparse(v);
    case OpCodeTag::AddNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddNatOp>::jparse(v);
    case OpCodeTag::AddIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddIntOp>::jparse(v);
    case OpCodeTag::AddBigNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddBigNatOp>::jparse(v);
    case OpCodeTag::AddBigIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddBigIntOp>::jparse(v);
    case OpCodeTag::AddRationalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddRationalOp>::jparse(v);
    case OpCodeTag::AddFloatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddFloatOp>::jparse(v);
    case OpCodeTag::AddDecimalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::AddDecimalOp>::jparse(v);
    case OpCodeTag::SubNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubNatOp>::jparse(v);
    case OpCodeTag::SubIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubIntOp>::jparse(v);
    case OpCodeTag::SubBigNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubBigNatOp>::jparse(v);
    case OpCodeTag::SubBigIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubBigIntOp>::jparse(v);
    case OpCodeTag::SubRationalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubRationalOp>::jparse(v);
    case OpCodeTag::SubFloatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubFloatOp>::jparse(v);
    case OpCodeTag::SubDecimalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::SubDecimalOp>::jparse(v);
    case OpCodeTag::MultNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultNatOp>::jparse(v);
    case OpCodeTag::MultIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultIntOp>::jparse(v);
    case OpCodeTag::MultBigNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultBigNatOp>::jparse(v);
    case OpCodeTag::MultBigIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultBigIntOp>::jparse(v);
    case OpCodeTag::MultRationalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultRationalOp>::jparse(v);
    case OpCodeTag::MultFloatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultFloatOp>::jparse(v);
    case OpCodeTag::MultDecimalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::MultDecimalOp>::jparse(v);
    case OpCodeTag::DivNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivNatOp>::jparse(v);
    case OpCodeTag::DivIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivIntOp>::jparse(v);
    case OpCodeTag::DivBigNatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivBigNatOp>::jparse(v);
    case OpCodeTag::DivBigIntOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivBigIntOp>::jparse(v);
    case OpCodeTag::DivRationalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivRationalOp>::jparse(v);
    case OpCodeTag::DivFloatOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivFloatOp>::jparse(v);
    case OpCodeTag::DivDecimalOp:
        return PrimitiveBinaryOperatorOp<OpCodeTag::DivDecimalOp>::jparse(v);
    case OpCodeTag::EqNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqNatOp>::jparse(v);
    case OpCodeTag::EqIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqIntOp>::jparse(v);
    case OpCodeTag::EqBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqBigNatOp>::jparse(v);
    case OpCodeTag::EqBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqBigIntOp>::jparse(v);
    case OpCodeTag::EqRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqRationalOp>::jparse(v);
    case OpCodeTag::NeqNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqNatOp>::jparse(v);
    case OpCodeTag::NeqIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqIntOp>::jparse(v);
    case OpCodeTag::NeqBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqBigNatOp>::jparse(v);
    case OpCodeTag::NeqBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqBigIntOp>::jparse(v);
    case OpCodeTag::NeqRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqRationalOp>::jparse(v);
    case OpCodeTag::LtNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtNatOp>::jparse(v);
    case OpCodeTag::LtIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtIntOp>::jparse(v);
    case OpCodeTag::LtBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtBigNatOp>::jparse(v);
    case OpCodeTag::LtBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtBigIntOp>::jparse(v);
    case OpCodeTag::LtRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtRationalOp>::jparse(v);
    case OpCodeTag::LtFloatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtFloatOp>::jparse(v);
    case OpCodeTag::LtDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtDecimalOp>::jparse(v);
    case OpCodeTag::GtNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtNatOp>::jparse(v);
    case OpCodeTag::GtIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtIntOp>::jparse(v);
    case OpCodeTag::GtBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtBigNatOp>::jparse(v);
    case OpCodeTag::GtBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtBigIntOp>::jparse(v);
    case OpCodeTag::GtRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtRationalOp>::jparse(v);
    case OpCodeTag::GtFloatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtFloatOp>::jparse(v);
    case OpCodeTag::GtDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtDecimalOp>::jparse(v);
    case OpCodeTag::LeNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeNatOp>::jparse(v);
    case OpCodeTag::LeIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeIntOp>::jparse(v);
    case OpCodeTag::LeBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeBigNatOp>::jparse(v);
    case OpCodeTag::LeBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeBigIntOp>::jparse(v);
    case OpCodeTag::LeRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeRationalOp>::jparse(v);
    case OpCodeTag::LeFloatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeFloatOp>::jparse(v);
    case OpCodeTag::LeDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeDecimalOp>::jparse(v);
    case OpCodeTag::GeNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeNatOp>::jparse(v);
    case OpCodeTag::GeIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeIntOp>::jparse(v);
    case OpCodeTag::GeBigNatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeBigNatOp>::jparse(v);
    case OpCodeTag::GeBigIntOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeBigIntOp>::jparse(v);
    case OpCodeTag::GeRationalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeRationalOp>::jparse(v);
    case OpCodeTag::GeFloatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeFloatOp>::jparse(v);
    case OpCodeTag::GeDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeDecimalOp>::jparse(v);
    case OpCodeTag::EqStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqStrPosOp>::jparse(v);
    case OpCodeTag::NeqStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqStrPosOp>::jparse(v);
    case OpCodeTag::LtStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LtStrPosOp>::jparse(v);
    case OpCodeTag::GtStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GtStrPosOp>::jparse(v);
    case OpCodeTag::LeStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::LeStrPosOp>::jparse(v);
    case OpCodeTag::GeStrPosOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::GeStrPosOp>::jparse(v);
    default: {
        assert(false);
        return nullptr;
    }
    }
}