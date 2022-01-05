//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqop.h"

Argument jsonParse_Argument(json j)
{
    return Argument{ j["kind"].get<ArgumentTag>(), j["location"].get<uint32_t>() };
}

TargetVar jsonParse_TargetVar(json j)
{
    return TargetVar{ j["kind"].get<ArgumentTag>(), j["offset"].get<uint32_t>() };
}

SourceInfo jsonParse_SourceInfo(json j)
{
    return SourceInfo{ j["line"].get<uint32_t>(), j["column"].get<uint32_t>() };
}

BSQGuard jsonParse_BSQGuard(json j)
{
    return BSQGuard{ j["gmaskoffset"].get<int32_t>(), j["gindex"].get<int32_t>(), j["gvaroffset"].get<int32_t>() };
}

BSQStatementGuard jsonParse_BSQStatementGuard(json j)
{
    return BSQStatementGuard{ jsonParse_BSQGuard(j["guard"]), jsonParse_Argument(j["defaultvar"]), j["usedefaulton"].get<bool>(), j["enabled"].get<bool>() };
}

const BSQType* jsonParse_BSQType(json j)
{
    auto tname = j.get<std::string>();
    auto tid = Environment::g_typenameToIDMap[tname].first;
    return BSQType::g_typetable[tid];
}

BSQRecordPropertyID jsonParse_BSQRecordPropertyID(json j)
{
    auto tname = j.get<std::string>();
    return Environment::g_propertynameToIDMap[tname];
}

BSQFieldID jsonParse_BSQFieldID(json j)
{
    auto tname = j.get<std::string>();
    return Environment::g_fieldnameToIDMap[tname];
}

SourceInfo j_sinfo(json j)
{
    return jsonParse_SourceInfo(j["sinfo"]);
}

TargetVar j_trgt(json j)
{
    return jsonParse_TargetVar(j["trgt"]);
}

Argument j_arg(json j)
{
    return jsonParse_Argument(j["arg"]);
}

const BSQType* j_oftype(json j)
{
    return jsonParse_BSQType(j["oftype"]);
}

const BSQType* j_argtype(json j)
{
    return jsonParse_BSQType(j["argtype"]);
}

const BSQType* j_layouttype(json j)
{
    return jsonParse_BSQType(j["layouttype"]);
}

const BSQType* j_flowtype(json j)
{
    return jsonParse_BSQType(j["flowtype"]);
}

const BSQType* j_intotype(json j)
{
    return jsonParse_BSQType(j["intotype"]);
}

const BSQType* j_trgttype(json j)
{
    return jsonParse_BSQType(j["trgttype"]);
}

BSQGuard j_guard(json j)
{
    return jsonParse_BSQGuard(j["guard"]);
}

BSQStatementGuard j_sguard(json j)
{
    return jsonParse_BSQStatementGuard(j["sguard"]);
}

void j_args(json j, std::vector<Argument>& args)
{
    auto jargs = j["args"];
    std::transform(jargs.cbegin(), jargs.cend(), std::back_inserter(args), [](json arg) {
        return jsonParse_Argument(arg);
    });
}

DeadFlowOp* DeadFlowOp::jparse(json v)
{
    return new DeadFlowOp(j_sinfo(v));
}

AbortOp* AbortOp::jparse(json v)
{
    return new AbortOp(j_sinfo(v), v["msg"].get<std::string>());
}

AssertOp* AssertOp::jparse(json v)
{
    return new AssertOp(j_sinfo(v), j_arg(v), v["msg"].get<std::string>());
}

DebugOp* DebugOp::jparse(json v)
{
    return new DebugOp(j_sinfo(v), j_arg(v), j_argtype(v));
}

LoadUnintVariableValueOp* LoadUnintVariableValueOp::jparse(json v)
{
    return new LoadUnintVariableValueOp(j_sinfo(v), j_trgt(v), j_oftype(v));
}

NoneInitUnionOp* NoneInitUnionOp::jparse(json v)
{
    return new NoneInitUnionOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQUnionType*>(j_oftype(v)));
}

StoreConstantMaskValueOp* StoreConstantMaskValueOp::jparse(json v)
{
    return new StoreConstantMaskValueOp(j_sinfo(v), v["gmaskoffset"].get<int32_t>(), v["gindex"].get<int32_t>(), v["flag"].get<bool>());
}

DirectAssignOp* DirectAssignOp::jparse(json v)
{
    return new DirectAssignOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), v["size"].get<uint32_t>(), j_sguard(v));
}

BoxOp* BoxOp::jparse(json v)
{
    return new BoxOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), jsonParse_BSQType(v["fromtype"]), j_sguard(v));
}

ExtractOp* ExtractOp::jparse(json v)
{
    return new ExtractOp(j_sinfo(v), j_trgt(v), j_intotype(v), j_arg(v), jsonParse_BSQType(v["fromtype"]), j_sguard(v));
}

LoadConstOp* LoadConstOp::jparse(json v)
{
    return new LoadConstOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v));
}

TupleHasIndexOp* TupleHasIndexOp::jparse(json v)
{
    return new TupleHasIndexOp(j_sinfo(v), j_trgt(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), v["idx"].get<BSQTupleIndex>());
}

RecordHasPropertyOp* RecordHasPropertyOp::jparse(json v)
{
    return new RecordHasPropertyOp(j_sinfo(v), j_trgt(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(v["propId"]));
}

LoadTupleIndexDirectOp* LoadTupleIndexDirectOp::jparse(json v)
{
    return new LoadTupleIndexDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), v["slotoffset"].get<uint32_t>(), v["idx"].get<BSQTupleIndex>());
}

LoadTupleIndexVirtualOp* LoadTupleIndexVirtualOp::jparse(json v)
{
    return new LoadTupleIndexVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), v["idx"].get<BSQTupleIndex>());
}

LoadTupleIndexSetGuardDirectOp* LoadTupleIndexSetGuardDirectOp::jparse(json v)
{
    return new LoadTupleIndexSetGuardDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), v["slotoffset"].get<uint32_t>(), v["idx"].get<BSQTupleIndex>(), j_guard(v));
}

LoadTupleIndexSetGuardVirtualOp* LoadTupleIndexSetGuardVirtualOp::jparse(json v)
{
    return new LoadTupleIndexSetGuardVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), v["idx"].get<BSQTupleIndex>(), j_guard(v));
}

LoadRecordPropertyDirectOp* LoadRecordPropertyDirectOp::jparse(json v)
{
    return new LoadRecordPropertyDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), v["slotoffset"].get<uint32_t>(), jsonParse_BSQRecordPropertyID(v["propId"]));
}

LoadRecordPropertyVirtualOp* LoadRecordPropertyVirtualOp::jparse(json v)
{
    return new LoadRecordPropertyVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(v["propId"]));
}

LoadRecordPropertySetGuardDirectOp* LoadRecordPropertySetGuardDirectOp::jparse(json v)
{
    return new LoadRecordPropertySetGuardDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), v["slotoffset"].get<uint32_t>(), jsonParse_BSQRecordPropertyID(v["propId"]), j_guard(v));
}

LoadRecordPropertySetGuardVirtualOp* LoadRecordPropertySetGuardVirtualOp::jparse(json v)
{
    return new LoadRecordPropertySetGuardVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQRecordPropertyID(v["propId"]), j_guard(v));
}

LoadEntityFieldDirectOp* LoadEntityFieldDirectOp::jparse(json v)
{
    return new LoadEntityFieldDirectOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), v["slotoffset"].get<uint32_t>(), jsonParse_BSQFieldID(v["fieldId"]));
}

LoadEntityFieldVirtualOp* LoadEntityFieldVirtualOp::jparse(json v)
{
    return new LoadEntityFieldVirtualOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQUnionType*>(j_layouttype(v)), jsonParse_BSQFieldID(v["fieldId"]));
}

ProjectTupleOp* ProjectTupleOp::jparse(json v)
{
    std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*>> idxs;
    auto idxl = v["idxs"];
    for(size_t i = 0; i < idxl.size(); ++i)
    {
        auto vv = idxl[i];
        idxs.push_back(std::make_tuple(vv[0].get<BSQTupleIndex>(), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectTupleOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), idxs);
}

ProjectRecordOp* ProjectRecordOp::jparse(json v)
{
    std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*>> props;
    auto propl = v["props"];
    for(size_t i = 0; i < props.size(); ++i)
    {
        auto vv = propl[i];
        props.push_back(std::make_tuple(jsonParse_BSQRecordPropertyID(vv[0]), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectRecordOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), props);
}

ProjectEntityOp* ProjectEntityOp::jparse(json v)
{
    std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*>> fields;
    auto fieldl = v["fields"];
    for(size_t i = 0; i < fields.size(); ++i)
    {
        auto vv = fieldl[i];
        fields.push_back(std::make_tuple(jsonParse_BSQFieldID(vv[0]), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2])));
    }

    return new ProjectEntityOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), j_layouttype(v), j_flowtype(v), fields);
}

UpdateTupleOp* UpdateTupleOp::jparse(json v)
{
    std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v["updates"];
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i];
        updates.push_back(std::make_tuple(vv[0].get<BSQTupleIndex>(), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateTupleOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

UpdateRecordOp* UpdateRecordOp::jparse(json v)
{
    std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v["updates"];
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i];
        updates.push_back(std::make_tuple(jsonParse_BSQRecordPropertyID(vv[0]), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateRecordOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

UpdateEntityOp* UpdateEntityOp::jparse(json v)
{
    std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*, Argument>> updates;
    auto updatel = v["updates"];
    for(size_t i = 0; i < updatel.size(); ++i)
    {
        auto vv = updatel[i];
        updates.push_back(std::make_tuple(jsonParse_BSQFieldID(vv[0]), vv[1].get<uint32_t>(), jsonParse_BSQType(vv[2]), jsonParse_Argument(vv[3])));
    }

    return new UpdateEntityOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), j_layouttype(v), j_flowtype(v), updates);
}

LoadFromEpehmeralListOp* LoadFromEpehmeralListOp::jparse(json v)
{
    return new LoadFromEpehmeralListOp(j_sinfo(v), j_trgt(v), j_trgttype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), v["slotoffset"].get<uint32_t>(), v["index"].get<uint32_t>());
}

MultiLoadFromEpehmeralListOp* MultiLoadFromEpehmeralListOp::jparse(json v)
{
    std::vector<TargetVar> trgts;
    auto jtrgts = v["trgts"];
    std::transform(jtrgts.cbegin(), jtrgts.cend(), std::back_inserter(trgts), [](json tv) {
        return jsonParse_TargetVar(tv);
    });

    std::vector<const BSQType*> trgttypes;
    auto jtrgttypes = v["trgttypes"];
    std::transform(jtrgttypes.cbegin(), jtrgttypes.cend(), std::back_inserter(trgttypes), [](json tt) {
        return jsonParse_BSQType(tt);
    });

    std::vector<uint32_t> slotoffsets;
    auto jslotoffsets = v["slotoffsets"];
    std::transform(jslotoffsets.cbegin(), jslotoffsets.cend(), std::back_inserter(slotoffsets), [](json so) {
        return so.get<uint32_t>();
    });

    std::vector<uint32_t> indexs;
    auto jindexs = v["indexs"];
    std::transform(jindexs.cbegin(), jindexs.cend(), std::back_inserter(indexs), [](json idx) {
        return idx.get<uint32_t>();
    });

    return new MultiLoadFromEpehmeralListOp(j_sinfo(v), trgts, trgttypes, j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), slotoffsets, indexs);
}

SliceEphemeralListOp* SliceEphemeralListOp::jparse(json v)
{
    return new SliceEphemeralListOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_trgttype(v)), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), v["slotoffsetend"].get<uint32_t>(), v["indexend"].get<uint32_t>());
}

InvokeFixedFunctionOp* InvokeFixedFunctionOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new InvokeFixedFunctionOp(j_sinfo(v), j_trgt(v), j_trgttype(v), Environment::g_invokenameToIDMap[v["invokeId"].get<std::string>()], args, j_sguard(v), v["optmaskoffset"].get<int32_t>());
}

InvokeVirtualFunctionOp* InvokeVirtualFunctionOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new InvokeVirtualFunctionOp(j_sinfo(v), j_trgt(v), j_trgttype(v), Environment::g_vinvokenameToIDMap[v["invokeId"].get<std::string>()], jsonParse_BSQType(v["rcvrlayouttype"]), args, v["optmaskoffset"].get<int32_t>());
}

InvokeVirtualOperatorOp* InvokeVirtualOperatorOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new InvokeVirtualOperatorOp(j_sinfo(v), j_trgt(v), j_trgttype(v), Environment::g_vinvokenameToIDMap[v["invokeId"].get<std::string>()], args);
}

ConstructorTupleOp* ConstructorTupleOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new ConstructorTupleOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

ConstructorTupleFromEphemeralListOp* ConstructorTupleFromEphemeralListOp::jparse(json v)
{
    return new ConstructorTupleFromEphemeralListOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)));
}

ConstructorRecordOp* ConstructorRecordOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new ConstructorRecordOp(j_sinfo(v), j_trgt(v), j_oftype(v), args);
}

ConstructorRecordFromEphemeralListOp* ConstructorRecordFromEphemeralListOp::jparse(json v)
{
    std::vector<uint32_t> proppositions;
    auto jproppositions = v["proppositions"];
    std::transform(jproppositions.cbegin(), jproppositions.cend(), std::back_inserter(proppositions), [](json pos) {
        return pos.get<uint32_t>();
    });

    return new ConstructorRecordFromEphemeralListOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), proppositions);
}

EphemeralListExtendOp* EphemeralListExtendOp::jparse(json v)
{
    std::vector<Argument> ext;
    auto jext = v["ext"];
    std::transform(jext.cbegin(), jext.cend(), std::back_inserter(ext), [](json ee) {
        return jsonParse_Argument(ee);
    });

    return new EphemeralListExtendOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(jsonParse_BSQType(v["resultType"])), j_arg(v), dynamic_cast<const BSQEphemeralListType*>(j_argtype(v)), ext);
}

ConstructorEphemeralListOp* ConstructorEphemeralListOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new ConstructorEphemeralListOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQEphemeralListType*>(j_oftype(v)), args);
}

PrefixNotOp* PrefixNotOp::jparse(json v)
{
    return new PrefixNotOp(j_sinfo(v), j_trgt(v), j_arg(v));
}

AllTrueOp* AllTrueOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new AllTrueOp(j_sinfo(v), j_trgt(v), args);
}

SomeTrueOp* SomeTrueOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new SomeTrueOp(j_sinfo(v), j_trgt(v), args);
}

BinKeyEqFastOp* BinKeyEqFastOp::jparse(json v)
{
    return new BinKeyEqFastOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_Argument(v["argr"]), j_sguard(v)); 
}
    
BinKeyEqStaticOp* BinKeyEqStaticOp::jparse(json v)
{
    return new BinKeyEqStaticOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_BSQType(v["argllayout"]), jsonParse_Argument(v["argr"]), jsonParse_BSQType(v["argrlayout"]), j_sguard(v)); 
}

BinKeyEqVirtualOp* BinKeyEqVirtualOp::jparse(json v)
{
    return new BinKeyEqVirtualOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_BSQType(v["argllayout"]), jsonParse_Argument(v["argr"]), jsonParse_BSQType(v["argrlayout"]), j_sguard(v)); 
}

BinKeyLessFastOp* BinKeyLessFastOp::jparse(json v)
{
    return new BinKeyLessFastOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_Argument(v["argr"])); 
}
    
BinKeyLessStaticOp* BinKeyLessStaticOp::jparse(json v)
{
    return new BinKeyLessStaticOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_BSQType(v["argllayout"]), jsonParse_Argument(v["argr"]), jsonParse_BSQType(v["argrlayout"])); 
}

BinKeyLessVirtualOp* BinKeyLessVirtualOp::jparse(json v)
{
    return new BinKeyLessVirtualOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["argl"]), jsonParse_BSQType(v["argllayout"]), jsonParse_Argument(v["argr"]), jsonParse_BSQType(v["argrlayout"])); 
}

TypeIsNoneOp* TypeIsNoneOp::jparse(json v)
{
    return new TypeIsNoneOp(j_sinfo(v), j_trgt(v), j_arg(v), jsonParse_BSQType(v["arglayout"]), j_sguard(v));
}

TypeIsSomeOp* TypeIsSomeOp::jparse(json v)
{
    return new TypeIsSomeOp(j_sinfo(v), j_trgt(v), j_arg(v), jsonParse_BSQType(v["arglayout"]), j_sguard(v));
}

TypeIsNothongOp* TypeIsNothingOp::jparse(json v)
{
    return new TypeIsNothingOp(j_sinfo(v), j_trgt(v), j_arg(v), jsonParse_BSQType(v["arglayout"]), j_sguard(v));
}

TypeTagIsOp* TypeTagIsOp::jparse(json v)
{
    return new TypeTagIsOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v), jsonParse_BSQType(v["arglayout"]), j_sguard(v));
}

TypeTagSubtypeOfOp* TypeTagSubtypeOfOp::jparse(json v)
{
    return new TypeTagSubtypeOfOp(j_sinfo(v), j_trgt(v), dynamic_cast<const BSQUnionType*>(j_oftype(v)), j_arg(v), jsonParse_BSQType(v["arglayout"]), j_sguard(v));
}

JumpOp* JumpOp::jparse(json v)
{
    return new JumpOp(j_sinfo(v), v["offset"].get<uint32_t>(), v["label"].get<std::string>());
}

JumpCondOp* JumpCondOp::jparse(json v)
{
    return new JumpCondOp(j_sinfo(v), j_arg(v), v["toffset"].get<uint32_t>(), v["foffset"].get<uint32_t>(), v["tlabel"].get<std::string>(), v["flabel"].get<std::string>());
}

JumpNoneOp* JumpNoneOp::jparse(json v)
{
    return new JumpNoneOp(j_sinfo(v), j_arg(v), jsonParse_BSQType(v["arglayout"]), v["noffset"].get<uint32_t>(), v["soffset"].get<uint32_t>(), v["nlabel"].get<std::string>(), v["slabel"].get<std::string>());
}

RegisterAssignOp* RegisterAssignOp::jparse(json v)
{
    return new RegisterAssignOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v), j_sguard(v));
}

ReturnAssignOp* ReturnAssignOp::jparse(json v)
{
    return new ReturnAssignOp(j_sinfo(v), j_trgt(v), j_arg(v), j_oftype(v));
}

ReturnAssignOfConsOp* ReturnAssignOfConsOp::jparse(json v)
{
    std::vector<Argument> args;
    j_args(v, args);

    return new ReturnAssignOfConsOp(j_sinfo(v), j_trgt(v), args, j_oftype(v));
}

VarLifetimeStartOp* VarLifetimeStartOp::jparse(json v)
{
    return new VarLifetimeStartOp(j_sinfo(v), jsonParse_Argument(v["homelocation"]), j_oftype(v), v["name"].get<std::string>());
}

VarLifetimeEndOp* VarLifetimeEndOp::jparse(json v)
{
    return new VarLifetimeEndOp(j_sinfo(v), v["name"].get<std::string>());
}

template <OpCodeTag tag>
PrimitiveNegateOperatorOp<tag>* PrimitiveNegateOperatorOp<tag>::jparse(json v)
{
    return new PrimitiveNegateOperatorOp(j_sinfo(v), j_trgt(v), j_oftype(v), j_arg(v));
}

template <OpCodeTag tag>
PrimitiveBinaryOperatorOp<tag>* PrimitiveBinaryOperatorOp<tag>::jparse(json v)
{
    return new PrimitiveBinaryOperatorOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["larg"]), jsonParse_Argument(v["rarg"]));
}

template <OpCodeTag tag>
PrimitiveBinaryCompareOp<tag>* PrimitiveBinaryCompareOp<tag>::jparse(json v)
{
    return new PrimitiveBinaryCompareOp(j_sinfo(v), j_trgt(v), j_oftype(v), jsonParse_Argument(v["larg"]), jsonParse_Argument(v["rarg"]));
}


InterpOp* InterpOp::jparse(json v)
{
    auto tag = v["tag"].get<OpCodeTag>();

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
    case OpCodeTag::TypeIsNothingOp:
        return TypeIsNothingOp::jparse(v);
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
    case OpCodeTag::EqFloatOp:
    return PrimitiveBinaryCompareOp<OpCodeTag::EqFloatOp>::jparse(v);
    case OpCodeTag::EqDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::EqDecimalOp>::jparse(v);
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
    case OpCodeTag::NeqFloatOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqFloatOp>::jparse(v);
    case OpCodeTag::NeqDecimalOp:
        return PrimitiveBinaryCompareOp<OpCodeTag::NeqDecimalOp>::jparse(v);
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
    default: {
        assert(false);
        return nullptr;
    }
    }
}