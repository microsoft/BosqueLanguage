//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqop.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

boost::json::value jsonGet(boost::json::value& val, const char* prop)
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
    return std::string(jsonGet(val, prop).as_string().cbegin(), jsonGet(val,prop).as_string().cend());
}

Argument jsonParse_Argument(boost::json::value val)
{
    return Argument{ jsonGetAsTag<ArgumentTag>(val, "kind"), jsonGetAsUInt<uint32_t>(val, "location") };
}

TargetVar jsonParse_TargetVar(boost::json::value val)
{
    return TargetVar{ jsonGetAsInt<ArgumentTag>(val, "kind"), jsonGetAsUInt<uint32_t>(val, "offset") };
}

SourceInfo jsonParse_SourceInfo(boost::json::value& val)
{
    return SourceInfo{ jsonGetAsUInt<uint32_t>(val, "line"), jsonGetAsUInt<uint32_t>(val, "column") };
}

BSQGuard jsonParse_BSQGuard(boost::json::value& val)
{
    return BSQGuard{ jsonGetAsUInt<uint32_t>(val, "gmaskoffset"), jsonGetAsInt<int32_t>(val, "gindex"), jsonGetAsInt<int32_t>(val, "gvaroffset") };
}

BSQStatementGuard jsonParse_BSQStatementGuard(boost::json::value& val)
{
    return BSQStatementGuard{ jsonParse_BSQGuard(jsonGet(val, "guard")), jsonParse_Argument(jsonGet(val, "defaultvar")), jsonGetAsBool(val, "usedefaulton"), jsonGetAsBool(val, "enabled") };
}

SourceInfo j_sinfo(boost::json::value val)
{
    return jsonParse_SourceInfo(jsonGet(val, "sinfo"));
}

TargetVar j_trgt(boost::json::value val)
{
    return jsonParse_TargetVar(jsonGet())
}

ArgumentTag j_arg(boost::json::value val)
{
    assert(val.is_object());
    return val.as_object().at(prop);
}

DeadFlowOp* DeadFlowOp::jparse(boost::json::value v)
{
    return new DeadFlowOp();
}
static AbortOp* jparse(boost::json::value v);

    static AbortOp* jparse(boost::json::value v);

class AssertOp : public InterpOp
{
public:
    const Argument arg;
    const std::string msg;

    AssertOp(SourceInfo sinfo, Argument arg, const std::string msg) : InterpOp(sinfo, OpCodeTag::AssertOp), arg(arg), msg(msg) {;}
    virtual ~AssertOp() {;}

    static AssertOp* jparse(boost::json::value v);
};

class DebugOp : public InterpOp
{
public:
    //Arg is invalid and type is nullptr if this is a break
    const Argument arg;
    const BSQType* argtype;

    DebugOp(SourceInfo sinfo, Argument arg, const BSQType* argtype) : InterpOp(sinfo, OpCodeTag::DebugOp), arg(arg), argtype(argtype) {;}
    virtual ~DebugOp() {;}

    static DebugOp* jparse(boost::json::value v);
};

//This op does not need to be emitted if we are in a release build
class LoadUnintVariableValueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;

    LoadUnintVariableValueOp(SourceInfo sinfo, TargetVar trgt, BSQType* oftype) : InterpOp(sinfo, OpCodeTag::LoadUnintVariableValueOp), trgt(trgt), oftype(oftype) {;}
    virtual ~LoadUnintVariableValueOp() {;}

    static LoadUnintVariableValueOp* jparse(boost::json::value v);
};

class NoneInitUnionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQUnionType* oftype;

    NoneInitUnionOp(SourceInfo sinfo, TargetVar trgt, BSQUnionType* oftype) : InterpOp(sinfo, OpCodeTag::LoadUnintVariableValueOp), trgt(trgt), oftype(oftype) {;}
    virtual ~NoneInitUnionOp() {;}

    static NoneInitUnionOp* jparse(boost::json::value v);
};

class StoreConstantMaskValueOp : public InterpOp
{
public:
    const uint32_t gmaskoffset; 
    const int32_t gindex;
    const BSQBool flag;

    StoreConstantMaskValueOp(SourceInfo sinfo, uint32_t gmaskoffset, int32_t gindex, BSQBool flag) : InterpOp(sinfo, OpCodeTag::StoreConstantMaskValueOp), gmaskoffset(gmaskoffset), gindex(gindex), flag(flag) {;}
    virtual ~StoreConstantMaskValueOp() {;}

    static StoreConstantMaskValueOp* jparse(boost::json::value v);
};

class DirectAssignOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* intotype;
    const Argument arg;
    const BSQStatementGuard sguard;

    DirectAssignOp(SourceInfo sinfo, TargetVar trgt, BSQType* intotype, Argument arg, uint32_t size, const BSQStatementGuard& sguard) : InterpOp(sinfo, OpCodeTag::DirectAssignOp), trgt(trgt), intotype(intotype), arg(arg), sguard(sguard) {;}
    virtual ~DirectAssignOp() {;}

    static DirectAssignOp* jparse(boost::json::value v);
};

class BoxOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* intotype;
    const Argument arg;
    const BSQType* fromtype;
    const BSQStatementGuard sguard;

    BoxOp(SourceInfo sinfo, TargetVar trgt, BSQType* intotype, Argument arg, BSQType* fromtype, const BSQStatementGuard& sguard) : InterpOp(sinfo, OpCodeTag::DirectAssignOp), trgt(trgt), intotype(intotype), arg(arg), fromtype(fromtype), sguard(sguard) {;}
    virtual ~BoxOp() {;}

    static BoxOp* jparse(boost::json::value v);
};

class ExtractOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* intotype;
    const Argument arg;
    const BSQType* fromtype;
    const BSQStatementGuard sguard;

    ExtractOp(SourceInfo sinfo, TargetVar trgt, BSQType* intotype, Argument arg, BSQType* fromtype, const BSQStatementGuard& sguard) : InterpOp(sinfo, OpCodeTag::DirectAssignOp), trgt(trgt), intotype(intotype), arg(arg), fromtype(fromtype), sguard(sguard) {;}
    virtual ~ExtractOp() {;}

    static ExtractOp* jparse(boost::json::value v);
};

class LoadConstOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* oftype;

    LoadConstOp(SourceInfo sinfo, TargetVar trgt, Argument arg, BSQType* oftype) : InterpOp(sinfo, OpCodeTag::LoadConstOp), trgt(trgt), arg(arg), oftype(oftype) {;}
    virtual ~LoadConstOp() {;}

    static LoadConstOp* jparse(boost::json::value v);
};

class TupleHasIndexOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQTupleIndex idx;

    TupleHasIndexOp(SourceInfo sinfo, TargetVar trgt, Argument arg, BSQUnionType* layouttype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::TupleHasIndexOp), trgt(trgt), arg(arg), layouttype(layouttype), idx(idx) {;}
    virtual ~TupleHasIndexOp() {;}

    static TupleHasIndexOp* jparse(boost::json::value v);
};

class RecordHasPropertyOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQRecordPropertyID propId;

    RecordHasPropertyOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQUnionType* layouttype, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::RecordHasPropertyOp), trgt(trgt), arg(arg), layouttype(layouttype), propId(propId) {;}
    virtual ~RecordHasPropertyOp() {;}

    static RecordHasPropertyOp* jparse(boost::json::value v);
};

class LoadTupleIndexDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const uint32_t slotoffset;
    const BSQTupleIndex idx;

    LoadTupleIndexDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, uint32_t slotoffset, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), slotoffset(slotoffset), idx(idx) {;}
    virtual ~LoadTupleIndexDirectOp() {;}

    static LoadTupleIndexDirectOp* jparse(boost::json::value v);
};

class LoadTupleIndexVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQTupleIndex idx;

    LoadTupleIndexVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQUnionType* layouttype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), idx(idx) {;}
    virtual ~LoadTupleIndexVirtualOp() {;}

    static LoadTupleIndexVirtualOp* jparse(boost::json::value v);
};

class LoadTupleIndexSetGuardDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const uint32_t slotoffset;
    const BSQTupleIndex idx;
    const BSQGuard guard;

    LoadTupleIndexSetGuardDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, uint32_t slotoffset, BSQTupleIndex idx, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), slotoffset(slotoffset), idx(idx), guard(guard) {;}
    virtual ~LoadTupleIndexSetGuardDirectOp() {;}

    static LoadTupleIndexSetGuardDirectOp* jparse(boost::json::value v);
};

class LoadTupleIndexSetGuardVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQTupleIndex idx;
    const BSQGuard guard;

    LoadTupleIndexSetGuardVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQUnionType* layouttype, BSQTupleIndex idx, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), idx(idx), guard(guard) {;}
    virtual ~LoadTupleIndexSetGuardVirtualOp() {;}

    static LoadTupleIndexSetGuardVirtualOp* jparse(boost::json::value v);
};

class LoadRecordPropertyDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const uint32_t slotoffset;
    const BSQRecordPropertyID propId;

    LoadRecordPropertyDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, uint32_t slotoffset, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertyDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), slotoffset(slotoffset), propId(propId) {;}
    virtual ~LoadRecordPropertyDirectOp() {;}

    static LoadRecordPropertyDirectOp* jparse(boost::json::value v);
};

class LoadRecordPropertyVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQRecordPropertyID propId;

    LoadRecordPropertyVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQUnionType* layouttype, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertyVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), propId(propId) {;}
    virtual ~LoadRecordPropertyVirtualOp() {;}

    static LoadRecordPropertyVirtualOp* jparse(boost::json::value v);
};

class LoadRecordPropertySetGuardDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const uint32_t slotoffset;
    const BSQRecordPropertyID propId;
    const BSQGuard guard;

    LoadRecordPropertySetGuardDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, uint32_t slotoffset, BSQRecordPropertyID propId, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertySetGuardDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), slotoffset(slotoffset), propId(propId), guard(guard) {;}
    virtual ~LoadRecordPropertySetGuardDirectOp() {;}

    static LoadRecordPropertySetGuardDirectOp* jparse(boost::json::value v);
};

class LoadRecordPropertySetGuardVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQRecordPropertyID propId;
    const BSQGuard guard;

    LoadRecordPropertySetGuardVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQUnionType* layouttype, BSQRecordPropertyID propId, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertySetGuardVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), propId(propId), guard(guard) {;}
    virtual ~LoadRecordPropertySetGuardVirtualOp() {;}

    static LoadRecordPropertySetGuardVirtualOp* jparse(boost::json::value v);
};

class LoadEntityFieldDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const uint32_t slotoffset;
    const BSQFieldID fieldId;

    LoadEntityFieldDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, uint32_t slotoffset, BSQFieldID fieldId) : InterpOp(sinfo, OpCodeTag::LoadEntityFieldDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), slotoffset(slotoffset), fieldId(fieldId) {;}
    virtual ~LoadEntityFieldDirectOp() {;}

    static LoadEntityFieldDirectOp* jparse(boost::json::value v);
};

class LoadEntityFieldVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQUnionType* layouttype;
    const BSQFieldID fieldId;

    LoadEntityFieldVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQUnionType* layouttype, BSQFieldID fieldId) : InterpOp(sinfo, OpCodeTag::LoadEntityFieldVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), fieldId(fieldId) {;}
    virtual ~LoadEntityFieldVirtualOp() {;}

    static LoadEntityFieldVirtualOp* jparse(boost::json::value v);
};

class ProjectTupleOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*>> idxs;

    ProjectTupleOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*>> idxs) : InterpOp(sinfo, OpCodeTag::ProjectTupleOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), idxs(idxs) {;}
    virtual ~ProjectTupleOp() {;}

    static ProjectTupleOp* jparse(boost::json::value v);
};

class ProjectRecordOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*>> props;

    ProjectRecordOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*>> props) : InterpOp(sinfo, OpCodeTag::ProjectRecordOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), props(props) {;}
    virtual ~ProjectRecordOp() {;}

    static ProjectRecordOp* jparse(boost::json::value v);
};

class ProjectEntityOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*>> fields;

    ProjectEntityOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*>> fields) : InterpOp(sinfo, OpCodeTag::ProjectEntityOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), fields(fields) {;}
    virtual ~ProjectEntityOp() {;}

    static ProjectEntityOp* jparse(boost::json::value v);
};
    
class UpdateTupleOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*, Argument>> updates;

    UpdateTupleOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQTupleIndex, uint32_t, const BSQType*, Argument>> updates) : InterpOp(sinfo, OpCodeTag::UpdateTupleOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), updates(updates) {;}
    virtual ~UpdateTupleOp() {;}

    static UpdateTupleOp* jparse(boost::json::value v);
};

class UpdateRecordOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*, Argument>> updates;

    UpdateRecordOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQRecordPropertyID, uint32_t, const BSQType*, Argument>> updates) : InterpOp(sinfo, OpCodeTag::UpdateRecordOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), updates(updates) {;}
    virtual ~UpdateRecordOp() {;}

    static UpdateRecordOp* jparse(boost::json::value v);
};

class UpdateEntityOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQType* flowtype;
    const std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*, Argument>> updates;

    UpdateEntityOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQType* layouttype, const BSQType* flowtype, std::vector<std::tuple<BSQFieldID, uint32_t, const BSQType*, Argument>> updates) : InterpOp(sinfo, OpCodeTag::UpdateEntityOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), flowtype(flowtype), updates(updates) {;}
    virtual ~UpdateEntityOp() {;}

    static UpdateEntityOp* jparse(boost::json::value v);
};

class LoadFromEpehmeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const uint32_t slotoffset;
    const uint32_t index;

    LoadFromEpehmeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQEphemeralListType* argtype, uint32_t slotoffset, uint32_t index) : InterpOp(sinfo, OpCodeTag::LoadFromEpehmeralListOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), index(index) {;}
    virtual ~LoadFromEpehmeralListOp() {;}

    static LoadFromEpehmeralListOp* jparse(boost::json::value v);
};

class MultiLoadFromEpehmeralListOp : public InterpOp
{
public:
    const std::vector<TargetVar> trgts;
    const std::vector<const BSQType*> trgttypes;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const std::vector<uint32_t> slotoffsets;
    const std::vector<uint32_t> indexs;

    MultiLoadFromEpehmeralListOp(SourceInfo sinfo, std::vector<TargetVar> trgts, std::vector<const BSQType*> trgttypes, Argument arg, BSQEphemeralListType* argtype, std::vector<uint32_t> slotoffsets, std::vector<uint32_t> indexs) : InterpOp(sinfo, OpCodeTag::MultiLoadFromEpehmeralListOp), trgts(trgts), trgttypes(trgttypes), arg(arg), argtype(argtype), slotoffsets(slotoffsets), indexs(indexs) {;}
    virtual ~MultiLoadFromEpehmeralListOp() {;}

    static MultiLoadFromEpehmeralListOp* jparse(boost::json::value v);
};

class SliceEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* trgttype;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const uint32_t slotoffsetend;
    const uint32_t indexend;

    SliceEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* trgttype, Argument arg, BSQEphemeralListType* argtype, uint32_t slotoffsetend, uint32_t indexend) : InterpOp(sinfo, OpCodeTag::SliceEphemeralListOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffsetend(slotoffsetend), indexend(indexend) {;}
    virtual ~SliceEphemeralListOp() {;}

    static SliceEphemeralListOp* jparse(boost::json::value v);
};

class InvokeFixedFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQInvokeID invokeId;
    const std::vector<Argument> args;
    const int32_t optmaskoffset;
    const BSQStatementGuard sguard;

    InvokeFixedFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQInvokeID invokeId, std::vector<Argument> args, BSQStatementGuard sguard, int32_t optmaskoffset) : InterpOp(sinfo, OpCodeTag::InvokeFixedFunctionOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args), sguard(sguard), optmaskoffset(optmaskoffset) {;}
    virtual ~InvokeFixedFunctionOp() {;}

    static InvokeFixedFunctionOp* jparse(boost::json::value v);
};

class InvokeVirtualFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQVirtualInvokeID invokeId;
    const BSQType* rcvrlayouttype;
    const int32_t optmaskoffset;
    const std::vector<Argument> args;
    
    InvokeVirtualFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQVirtualInvokeID invokeId, const BSQType* rcvrlayouttype, std::vector<Argument> args, int32_t optmaskoffset) : InterpOp(sinfo, OpCodeTag::InvokeVirtualFunctionOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), rcvrlayouttype(rcvrlayouttype), args(args), optmaskoffset(optmaskoffset) {;}
    virtual ~InvokeVirtualFunctionOp() {;}

    static InvokeVirtualFunctionOp* jparse(boost::json::value v);
};

class InvokeVirtualOperatorOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQVirtualInvokeID invokeId;
    const std::vector<Argument> args;
    
    InvokeVirtualOperatorOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQVirtualInvokeID invokeId, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::InvokeVirtualOperatorOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args) {;}
    virtual ~InvokeVirtualOperatorOp() {;}

    static InvokeVirtualOperatorOp* jparse(boost::json::value v);
};

class ConstructorTupleOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorTupleOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorTupleOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorTupleOp() {;}

    static ConstructorTupleOp* jparse(boost::json::value v);
};

class ConstructorTupleFromEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    
    ConstructorTupleFromEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg, const BSQEphemeralListType* argtype) : InterpOp(sinfo, OpCodeTag::ConstructorTupleFromEphemeralListOp), trgt(trgt), oftype(oftype), arg(arg), argtype(argtype) {;}
    virtual ~ConstructorTupleFromEphemeralListOp() {;}

    static ConstructorTupleFromEphemeralListOp* jparse(boost::json::value v);
};

class ConstructorRecordOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorRecordOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorRecordOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorRecordOp() {;}

    static ConstructorRecordOp* jparse(boost::json::value v);
};

class ConstructorRecordFromEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const std::vector<uint32_t> proppositions; //if empty then assume properties are in same order as elist
    
    ConstructorRecordFromEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg, const BSQEphemeralListType* argtype, std::vector<BSQRecordPropertyID> positions) : InterpOp(sinfo, OpCodeTag::ConstructorRecordFromEphemeralListOp), trgt(trgt), oftype(oftype), arg(arg), argtype(argtype), proppositions(proppositions) {;}
    virtual ~ConstructorRecordFromEphemeralListOp() {;}

    static ConstructorRecordFromEphemeralListOp* jparse(boost::json::value v);
};

class EphemeralListExtendOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* resultType;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const std::vector<Argument> ext;

    EphemeralListExtendOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* resultType, Argument arg, const BSQEphemeralListType* argtype, std::vector<Argument> ext) : InterpOp(sinfo, OpCodeTag::EphemeralListExtendOp), trgt(trgt), resultType(resultType), arg(arg), argtype(argtype), ext(ext) {;}
    virtual ~EphemeralListExtendOp() {;}

    static EphemeralListExtendOp* jparse(boost::json::value v);
};

class ConstructorEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* oftype;
    const std::vector<Argument> args;
    
    ConstructorEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorEphemeralListOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorEphemeralListOp() {;}

    static ConstructorEphemeralListOp* jparse(boost::json::value v);
};

class ConstructorPrimaryCollectionEmptyOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    
    ConstructorPrimaryCollectionEmptyOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionEmptyOp), trgt(trgt), oftype(oftype) {;}
    virtual ~ConstructorPrimaryCollectionEmptyOp() {;}

    static ConstructorPrimaryCollectionEmptyOp* jparse(boost::json::value v);
};

class ConstructorPrimaryCollectionSingletonsOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionSingletonsOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionSingletonsOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionSingletonsOp() {;}

    static ConstructorPrimaryCollectionEmptyOp* jparse(boost::json::value v);
};

class ConstructorPrimaryCollectionCopiesOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionCopiesOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionCopiesOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionCopiesOp() {;}

    static ConstructorPrimaryCollectionCopiesOp* jparse(boost::json::value v);
};

class ConstructorPrimaryCollectionMixedOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionMixedOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionMixedOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionMixedOp() {;}

    static ConstructorPrimaryCollectionMixedOp* jparse(boost::json::value v);
};

class PrefixNotOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    
    PrefixNotOp(SourceInfo sinfo, TargetVar trgt, Argument arg) : InterpOp(sinfo, OpCodeTag::PrefixNotOp), trgt(trgt), arg(arg) {;}
    virtual ~PrefixNotOp() {;}

    static PrefixNotOp* jparse(boost::json::value v);
};

class AllTrueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const std::vector<Argument> args;
    
    AllTrueOp(SourceInfo sinfo, TargetVar trgt, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::AllTrueOp), trgt(trgt), args(args) {;}
    virtual ~AllTrueOp() {;}

    static AllTrueOp* jparse(boost::json::value v);
};

class SomeTrueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const std::vector<Argument> args;
    
    SomeTrueOp(SourceInfo sinfo, TargetVar trgt, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::SomeTrueOp), trgt(trgt), args(args) {;}
    virtual ~SomeTrueOp() {;}

    static SomeTrueOp* jparse(boost::json::value v);
};

class BinKeyEqFastOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument argl;
    const Argument argr;
    
    BinKeyEqFastOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument argl, Argument argr) : InterpOp(sinfo, OpCodeTag::BinKeyEqFastOp), trgt(trgt), oftype(oftype), argl(argl), argr(argr) {;}
    virtual ~BinKeyEqFastOp() {;}

    static BinKeyEqFastOp* jparse(boost::json::value v);
};
    
class BinKeyEqStaticOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument argl;
    const BSQType* argllayout;
    const Argument argr;
    const BSQType* argrlayout;
    
    BinKeyEqStaticOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument argl, const BSQType* argllayout, Argument argr, const BSQType* argrlayout) : InterpOp(sinfo, OpCodeTag::BinKeyEqStaticOp), trgt(trgt), oftype(oftype), argl(argl), argllayout(argllayout), argr(argr), argrlayout(argrlayout) {;}
    virtual ~BinKeyEqStaticOp() {;}

    static BinKeyEqStaticOp* jparse(boost::json::value v);
};

class BinKeyEqVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument argl;
    const BSQType* argllayout;
    const Argument argr;
    const BSQType* argrlayout;
    
    BinKeyEqVirtualOp(SourceInfo sinfo, TargetVar trgt, Argument argl, const BSQType* argllayout, Argument argr, const BSQType* argrlayout) : InterpOp(sinfo, OpCodeTag::BinKeyEqVirtualOp), trgt(trgt), argl(argl), argllayout(argllayout), argr(argr), argrlayout(argrlayout) {;}
    virtual ~BinKeyEqVirtualOp() {;}

    static BinKeyEqVirtualOp* jparse(boost::json::value v);
};


class BinKeyLessFastOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument argl;
    const Argument argr;
    
    BinKeyLessFastOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument argl, Argument argr) : InterpOp(sinfo, OpCodeTag::BinKeyLessFastOp), trgt(trgt), oftype(oftype), argl(argl), argr(argr) {;}
    virtual ~BinKeyLessFastOp() {;}

    static BinKeyLessFastOp* jparse(boost::json::value v);
};
    
class BinKeyLessStaticOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument argl;
    const BSQType* argllayout;
    const Argument argr;
    const BSQType* argrlayout;
    
    BinKeyLessStaticOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument argl, const BSQType* argllayout, Argument argr, const BSQType* argrlayout) : InterpOp(sinfo, OpCodeTag::BinKeyLessStaticOp), trgt(trgt), oftype(oftype), argl(argl), argllayout(argllayout), argr(argr), argrlayout(argrlayout) {;}
    virtual ~BinKeyLessStaticOp() {;}

    static BinKeyLessStaticOp* jparse(boost::json::value v);
};

class BinKeyLessVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument argl;
    const BSQType* argltype;
    const BSQType* argllayout;
    const Argument argr;
    const BSQType* argrtype;
    const BSQType* argrlayout;
    
    BinKeyLessVirtualOp(SourceInfo sinfo, TargetVar trgt, Argument argl, const BSQType* argltype, const BSQType* argllayout, Argument argr, const BSQType* argrtype, const BSQType* argrlayout) : InterpOp(sinfo, OpCodeTag::BinKeyLessVirtualOp), trgt(trgt), argl(argl), argltype(argltype), argllayout(argllayout), argr(argr), argrtype(argrtype), argrlayout(argrlayout) {;}
    virtual ~BinKeyLessVirtualOp() {;}

    static BinKeyLessVirtualOp* jparse(boost::json::value v);
};

class TypeIsNoneOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeIsNoneOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::TypeIsNoneOp), trgt(trgt), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeIsNoneOp() {;}

    static TypeIsNoneOp* jparse(boost::json::value v);
};

class TypeIsSomeOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeIsSomeOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::TypeIsSomeOp), trgt(trgt), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeIsSomeOp() {;}

    static TypeIsSomeOp* jparse(boost::json::value v);
};

class TypeTagIsOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeTagIsOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::TypeTagIsOp), trgt(trgt), oftype(oftype), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeTagIsOp() {;}

    static TypeTagIsOp* jparse(boost::json::value v);
};

class TypeTagSubtypeOfOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQUnionType* oftype;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeTagSubtypeOfOp(SourceInfo sinfo, TargetVar trgt, const BSQUnionType* oftype, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::TypeTagSubtypeOfOp), trgt(trgt), oftype(oftype), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeTagSubtypeOfOp() {;}

    static TypeTagSubtypeOfOp* jparse(boost::json::value v);
};

class JumpOp : public InterpOp
{
public:
    const uint32_t offset;
    const std::string label;
    
    JumpOp(SourceInfo sinfo, uint32_t offset, const std::string label) : InterpOp(sinfo, OpCodeTag::JumpOp), offset(offset), label(label) {;}
    virtual ~JumpOp() {;}

    static JumpOp* jparse(boost::json::value v);
};

class JumpCondOp : public InterpOp
{
public:
    const Argument arg;
    const uint32_t toffset;
    const uint32_t foffset;
    const std::string tlabel;
    const std::string flabel;
    
    JumpCondOp(SourceInfo sinfo, Argument arg, uint32_t toffset, uint32_t foffset, const std::string tlabel, const std::string flabel) : InterpOp(sinfo, OpCodeTag::JumpCondOp), arg(arg), toffset(toffset), foffset(foffset), tlabel(tlabel), flabel(flabel) {;}
    virtual ~JumpCondOp() {;}

    static JumpCondOp* jparse(boost::json::value v);
};

class JumpNoneOp : public InterpOp
{
public:
    const Argument arg;
    const BSQType* arglayout;
    const uint32_t noffset;
    const uint32_t soffset;
    const std::string nlabel;
    const std::string slabel;
    
    JumpNoneOp(SourceInfo sinfo, Argument arg, const BSQType* arglayout, uint32_t noffset, uint32_t soffset, const std::string nlabel, const std::string slabel) : InterpOp(sinfo, OpCodeTag::JumpNoneOp), arg(arg), arglayout(arglayout), noffset(noffset), soffset(soffset), nlabel(nlabel), slabel(slabel) {;}
    virtual ~JumpNoneOp() {;}

    static JumpNoneOp* jparse(boost::json::value v);
};

class RegisterAssignOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* oftype;
    const BSQStatementGuard sguard;
    
    RegisterAssignOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* oftype, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::RegisterAssignOp), trgt(trgt), arg(arg), oftype(oftype), sguard(sguard) {;}
    virtual ~RegisterAssignOp() {;}

    static RegisterAssignOp* jparse(boost::json::value v);
};

class ReturnAssignOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* oftype;
    
    ReturnAssignOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ReturnAssignOp), trgt(trgt), arg(arg), oftype(oftype) {;}
    virtual ~ReturnAssignOp() {;}

    static ReturnAssignOp* jparse(boost::json::value v);
};

class ReturnAssignOfConsOp : public InterpOp
{
public:
    const TargetVar trgt;
    const std::vector<Argument> args;
    const BSQType* oftype;
    
    ReturnAssignOfConsOp(SourceInfo sinfo, TargetVar trgt, std::vector<Argument> args, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ReturnAssignOfConsOp), trgt(trgt), args(args), oftype(oftype) {;}
    virtual ~ReturnAssignOfConsOp() {;}

    static ReturnAssignOfConsOp* jparse(boost::json::value v);
};

class VarLifetimeStartOp : public InterpOp
{
public:
    const Argument homelocation;
    const BSQType* oftype;
    const std::string name;
    
    VarLifetimeStartOp(SourceInfo sinfo, Argument homelocation, const BSQType* oftype, const std::string name) : InterpOp(sinfo, OpCodeTag::VarLifetimeStartOp), homelocation(homelocation), oftype(oftype), name(name) {;}
    virtual ~VarLifetimeStartOp() {;}

    static VarLifetimeStartOp* jparse(boost::json::value v);
};

class VarLifetimeEndOp : public InterpOp
{
public:
    const std::string name;
    
    VarLifetimeEndOp(SourceInfo sinfo, const std::string name) : InterpOp(sinfo, OpCodeTag::VarLifetimeEndOp), name(name) {;}
    virtual ~VarLifetimeEndOp() {;}

    static VarLifetimeEndOp* jparse(boost::json::value v);
};

template <OpCodeTag tag>
class PrimitiveNegateOperatorOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    
    PrimitiveNegateOperatorOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg) : InterpOp(sinfo, tag), trgt(trgt), oftype(oftype), arg(arg) {;}
    virtual ~PrimitiveNegateOperatorOp() {;}

    static PrimitiveNegateOperatorOp* jparse(boost::json::value v);
};

template <OpCodeTag tag>
class PrimitiveBinaryOperatorOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument larg;
    const Argument rarg;
    
    PrimitiveBinaryOperatorOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument larg, Argument rarg) : InterpOp(sinfo, tag), trgt(trgt), oftype(oftype), larg(larg), rarg(rarg) {;}
    virtual ~PrimitiveBinaryOperatorOp() {;}

    static PrimitiveBinaryOperatorOp* jparse(boost::json::value v);
};

template <OpCodeTag tag>
class PrimitiveBinaryCompareOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument larg;
    const Argument rarg;
    
    PrimitiveBinaryCompareOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument larg, Argument rarg) : InterpOp(sinfo, tag), trgt(trgt), oftype(oftype), larg(larg), rarg(rarg) {;}
    virtual ~PrimitiveBinaryCompareOp() {;}

    static PrimitiveBinaryCompareOp* jparse(boost::json::value v);