//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqtype.h"

enum class ArgumentTag
{
    InvalidOp = 0x0,
    Const,
    Local,
    Argument
};

enum class OpCodeTag
{
    Invalid = 0x0,
    DeadFlowOp,
    AbortOp,
    AssertOp,
    DebugOp,
    LoadUnintVariableValueOp,
    NoneInitUnionOp,
    StoreConstantMaskValueOp,

    DirectAssignOp,
    BoxOp,
    ExtractOp,

    LoadConstOp,
    TupleHasIndexOp,
    RecordHasPropertyOp,
    LoadTupleIndexDirectOp,
    LoadTupleIndexVirtualOp,
    LoadTupleIndexSetGuardDirectOp,
    LoadTupleIndexSetGuardVirtualOp,
    LoadRecordPropertyDirectOp,
    LoadRecordPropertyVirtualOp,
    LoadRecordPropertySetGuardDirectOp,
    LoadRecordPropertySetGuardVirtualOp,
    LoadEntityFieldDirectOp,
    LoadEntityFieldVirtualOp,
    ProjectTupleOp,
    ProjectRecordOp,
    ProjectEntityOp,
    UpdateTupleOp,
    UpdateRecordOp,
    UpdateEntityOp,
    LoadFromEpehmeralListOp,
    MultiLoadFromEpehmeralListOp,
    SliceEphemeralListOp,

    InvokeFixedFunctionOp,
    GuardedInvokeFixedFunctionOp,
    InvokeVirtualFunctionOp,
    InvokeVirtualOperatorOp,

    ConstructorTupleOp,
    ConstructorTupleFromEphemeralListOp,
    ConstructorRecordOp,
    ConstructorRecordFromEphemeralListOp,
    EphemeralListExtendOp,
    ConstructorEphemeralListOp,
    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp,
    PrefixNotOp,
    AllTrueOp,
    SomeTrueOp,

    BinKeyEqVirtualOp,
    BinKeyLessVirtualOp,

    TypeIsNoneOp,
    TypeIsSomeOp,
    TypeTagIsOp,
    TypeTagSubtypeOfOp,
    GuardedTypeIsNoneOp,
    GuardedTypeIsSomeOp,
    GuardedTypeTagIsOp,
    GuardedTypeTagSubtypeOfOp,
    
    JumpOp,
    JumpCondOp,
    JumpNoneOp,
    RegisterAssignOp,
    GuardedRegisterAssignOp,
    ReturnAssignOp,
    ReturnAssignOfConsOp,
    VarLifetimeStartOp,
    VarLifetimeEndOp,

    AddNatOp,
    AddIntOp,
    AddBigNatOp,
    AddBigIntOp,
    AddRationalOp,
    AddFloatOp,
    AddDecimalOp,
    SubNatOp,
    SubIntOp,
    SubBigNatOp,
    SubBigIntOp,
    SubRationalOp,
    SubFloatOp,
    SubDecimalOp,
    MultNatOp,
    MultIntOp,
    MultBigNatOp,
    MultBigIntOp,
    MultRationalOp,
    MultFloatOp,
    MultDecimalOp,
    DivNatOp,
    DivIntOp,
    DivBigNatOp,
    DivBigIntOp,
    DivRationalOp,
    DivFloatOp,
    DivDecimalOp,

    EqNatOp,
    EqIntOp,
    EqBigNatOp,
    EqBigIntOp,
    EqRationalOp,
    NeqNatOp,
    NeqIntOp,
    NeqBigNatOp,
    NeqBigIntOp,
    NeqRationalOp,

    LtNatOp,
    LtIntOp,
    LtBigNatOp,
    LtBigIntOp,
    LtRationalOp,
    LtFloatOp,
    LtDecimalOp,
    LtStringOp,
    GtNatOp,
    GtIntOp,
    GtBigNatOp,
    GtBigIntOp,
    GtRationalOp,
    GtFloatOp,
    GtDecimalOp,
    GtStringOp,

    LeNatOp,
    LeIntOp,
    LeBigNatOp,
    LeBigIntOp,
    LeRationalOp,
    LeFloatOp,
    LeDecimalOp,
    GeNatOp,
    GeIntOp,
    GeBigNatOp,
    GeBigIntOp,
    GeRationalOp,
    GeFloatOp,
    GeDecimalOp,

    EqStrPosOp,
    NeqStrPosOp,
    LtStrPosOp,
    GtStrPosOp,
    LeStrPosOp,
    GeStrPosOp,

    EqStringOp,
    NeqStringOp,
    LessStringOp
};

struct Argument
{
    ArgumentTag kind;
    uint32_t location;
};

struct TargetVar
{
    uint32_t offset;
};

struct SourceInfo
{
    uint32_t line;
    uint32_t column;
};

struct BSQGuard
{
    uint32_t gmaskoffset; 
    int32_t gindex;

    int32_t gvaroffset; //-1 if this is a mask offset otherwise this is the local var offset
};

struct BSQStatementGuard
{
    BSQGuard guard;
    Argument defaultvar; //may be uninterp fill
    bool usedefaulton;
    bool enabled; //true if this statment guard is active and should be used
};

class InterpOp
{
public:
    const OpCodeTag tag;
    const SourceInfo sinfo;

    InterpOp(SourceInfo sinfo, OpCodeTag tag) : tag(tag), sinfo(sinfo) {;}
    virtual ~InterpOp() {;}
};

class DeadFlowOp : public InterpOp
{
public:
    DeadFlowOp(SourceInfo sinfo) : InterpOp(sinfo, OpCodeTag::DeadFlowOp) {;}
    virtual ~DeadFlowOp() {;}
};

class AbortOp : public InterpOp
{
public:
    const std::string* msg;

    AbortOp(SourceInfo sinfo, const std::string* msg) : InterpOp(sinfo, OpCodeTag::AbortOp), msg(msg) {;}
    virtual ~AbortOp() {;}
};

class AssertOp : public InterpOp
{
public:
    const Argument arg;
    const std::string* msg;

    AssertOp(SourceInfo sinfo, Argument arg, const std::string* msg) : InterpOp(sinfo, OpCodeTag::AssertOp), arg(arg), msg(msg) {;}
    virtual ~AssertOp() {;}
};

class DebugOp : public InterpOp
{
public:
    //Arg is invalid and type is nullptr if this is a break
    const Argument arg;
    const BSQType* argtype;

    DebugOp(SourceInfo sinfo, Argument arg, const BSQType* argtype) : InterpOp(sinfo, OpCodeTag::DebugOp), arg(arg), argtype(argtype) {;}
    virtual ~DebugOp() {;}
};

//This op does not need to be emitted if we are in a release build
class LoadUnintVariableValueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;

    LoadUnintVariableValueOp(SourceInfo sinfo, TargetVar trgt, BSQType* oftype) : InterpOp(sinfo, OpCodeTag::LoadUnintVariableValueOp), trgt(trgt), oftype(oftype) {;}
    virtual ~LoadUnintVariableValueOp() {;}
};

class NoneInitUnionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQUnionType* oftype;

    NoneInitUnionOp(SourceInfo sinfo, TargetVar trgt, BSQUnionType* oftype) : InterpOp(sinfo, OpCodeTag::LoadUnintVariableValueOp), trgt(trgt), oftype(oftype) {;}
    virtual ~NoneInitUnionOp() {;}
};

class StoreConstantMaskValueOp : public InterpOp
{
public:
    const uint32_t gmaskoffset; 
    const int32_t gindex;
    const BSQBool flag;

    StoreConstantMaskValueOp(SourceInfo sinfo, uint32_t gmaskoffset, int32_t gindex, BSQBool flag) : InterpOp(sinfo, OpCodeTag::StoreConstantMaskValueOp), gmaskoffset(gmaskoffset), gindex(gindex), flag(flag) {;}
    virtual ~StoreConstantMaskValueOp() {;}
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
};

class LoadConstOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* oftype;

    LoadConstOp(SourceInfo sinfo, TargetVar trgt, Argument arg, BSQType* oftype) : InterpOp(sinfo, OpCodeTag::LoadConstOp), trgt(trgt), arg(arg), oftype(oftype) {;}
    virtual ~LoadConstOp() {;}
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
};

template <OpCodeTag tag, bool isGuarded>
class InvokeFixedFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQInvokeID invokeId;
    const std::vector<Argument> args;
    const int32_t optmaskoffset;
    const BSQStatementGuard sguard;

    InvokeFixedFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQInvokeID invokeId, std::vector<Argument> args, BSQStatementGuard sguard, int32_t optmaskoffset) : InterpOp(sinfo, tag), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args), sguard(sguard), optmaskoffset(optmaskoffset) {;}
    virtual ~InvokeFixedFunctionOp() {;}
};

class InvokeVirtualFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQVirtualInvokeID invokeId;
    const int32_t optmaskoffset;
    const std::vector<Argument> args;
    
    InvokeVirtualFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQVirtualInvokeID invokeId, std::vector<Argument> args, int32_t optmaskoffset) : InterpOp(sinfo, OpCodeTag::InvokeVirtualFunctionOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args), optmaskoffset(optmaskoffset) {;}
    virtual ~InvokeVirtualFunctionOp() {;}
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
};

class ConstructorTupleOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorTupleOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorTupleOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorTupleOp() {;}
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
};

class ConstructorRecordOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorRecordOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorRecordOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorRecordOp() {;}
};

class ConstructorRecordFromEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    const BSQEphemeralListType* argtype;
    const std::vector<uint32_t> proppositions; //if empty then assume properties are in same order as elist
    
    ConstructorRecordFromEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg, const BSQEphemeralListType* argtype, std::vector<BSQRecordPropertyID> positions) : InterpOp(sinfo, OpCodeTag::ConstructorRecordFromEphemeralListOp), trgt(trgt), oftype(oftype), arg(arg), argtype(argtype), positions(positions) {;}
    virtual ~ConstructorRecordFromEphemeralListOp() {;}
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
};

class ConstructorEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* oftype;
    const std::vector<Argument> args;
    
    ConstructorEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorEphemeralListOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorEphemeralListOp() {;}
};

class ConstructorPrimaryCollectionEmptyOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    
    ConstructorPrimaryCollectionEmptyOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionEmptyOp), trgt(trgt), oftype(oftype) {;}
    virtual ~ConstructorPrimaryCollectionEmptyOp() {;}
};


class ConstructorPrimaryCollectionSingletonsOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionSingletonsOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionSingletonsOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionSingletonsOp() {;}
};


class ConstructorPrimaryCollectionCopiesOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionCopiesOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionCopiesOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionCopiesOp() {;}
};


class ConstructorPrimaryCollectionMixedOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const std::vector<Argument> args;
    
    ConstructorPrimaryCollectionMixedOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::ConstructorPrimaryCollectionMixedOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorPrimaryCollectionMixedOp() {;}
};

class PrefixNotOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    
    PrefixNotOp(SourceInfo sinfo, TargetVar trgt, Argument arg) : InterpOp(sinfo, OpCodeTag::PrefixNotOp), trgt(trgt), arg(arg) {;}
    virtual ~PrefixNotOp() {;}
};

class AllTrueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const std::vector<Argument> args;
    
    AllTrueOp(SourceInfo sinfo, TargetVar trgt, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::AllTrueOp), trgt(trgt), args(args) {;}
    virtual ~AllTrueOp() {;}
};

class SomeTrueOp : public InterpOp
{
public:
    const TargetVar trgt;
    const std::vector<Argument> args;
    
    SomeTrueOp(SourceInfo sinfo, TargetVar trgt, std::vector<Argument> args) : InterpOp(sinfo, OpCodeTag::SomeTrueOp), trgt(trgt), args(args) {;}
    virtual ~SomeTrueOp() {;}
};

class BinKeyEqVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument argl;
    const BSQType* argltype;
    const BSQType* argllayout;
    const Argument argr;
    const BSQType* argrtype;
    const BSQType* argrlayout;
    
    BinKeyEqVirtualOp(SourceInfo sinfo, TargetVar trgt, Argument argl, const BSQType* argltype, const BSQType* argllayout, Argument argr, const BSQType* argrtype, const BSQType* argrlayout) : InterpOp(sinfo, OpCodeTag::BinKeyEqVirtualOp), trgt(trgt), argl(argl), argltype(argltype), argllayout(argllayout), argr(argr), argrtype(argrtype), argrlayout(argrlayout) {;}
    virtual ~BinKeyEqVirtualOp() {;}
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
};

template <OpCodeTag tag, bool isGuarded>
class TypeIsNoneOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeIsNoneOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, tag), trgt(trgt), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeIsNoneOp() {;}
};

template <OpCodeTag tag, bool isGuarded>
class TypeIsSomeOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeIsSomeOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, tag), trgt(trgt), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeIsSomeOp() {;}
};

template <OpCodeTag tag, bool isGuarded>
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
};

template <OpCodeTag tag, bool isGuarded>
class TypeTagSubtypeOfOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* oftype;
    const Argument arg;
    const BSQType* arglayout;
    const BSQStatementGuard sguard;
    
    TypeTagSubtypeOfOp(SourceInfo sinfo, TargetVar trgt, const BSQType* oftype, Argument arg, const BSQType* arglayout, BSQStatementGuard sguard) : InterpOp(sinfo, OpCodeTag::TypeTagSubtypeOfOp), trgt(trgt), oftype(oftype), arg(arg), arglayout(arglayout), sguard(sguard) {;}
    virtual ~TypeTagSubtypeOfOp() {;}
};

class JumpOp : public InterpOp
{
public:
    const uint32_t offset;
    const std::string* label;
    
    JumpOp(SourceInfo sinfo, uint32_t offset, const std::string* label) : InterpOp(sinfo, OpCodeTag::JumpOp), offset(offset), label(label) {;}
    virtual ~JumpOp() {;}
};

class JumpCondOp : public InterpOp
{
public:
    const Argument arg;
    const uint32_t toffset;
    const uint32_t foffset;
    const std::string* tlabel;
    const std::string* flabel;
    
    JumpCondOp(SourceInfo sinfo, Argument arg, uint32_t toffset, uint32_t foffset, const std::string* tlabel, const std::string* flabel) : InterpOp(sinfo, OpCodeTag::JumpCondOp), arg(arg), toffset(toffset), foffset(foffset), tlabel(tlabel), flabel(flabel) {;}
    virtual ~JumpCondOp() {;}
};

class JumpNoneOp : public InterpOp
{
public:
    const Argument arg;
    const BSQType* arglayout;
    const uint32_t noffset;
    const uint32_t soffset;
    const std::string* nlabel;
    const std::string* slabel;
    
    JumpNoneOp(SourceInfo sinfo, Argument arg, const BSQType* arglayout, uint32_t noffset, uint32_t soffset, const std::string* nlabel, const std::string* slabel) : InterpOp(sinfo, OpCodeTag::JumpNoneOp), arg(arg), arglayout(arglayout), noffset(noffset), soffset(soffset), nlabel(nlabel), slabel(slabel) {;}
    virtual ~JumpNoneOp() {;}
};

template <OpCodeTag tag, bool isGuarded>
class RegisterAssignOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* oftype;
    const BSQStatementGuard sguard;
    
    RegisterAssignOp(SourceInfo sinfo, TargetVar trgt, Argument arg, const BSQType* oftype, BSQStatementGuard sguard) : InterpOp(sinfo, tag), trgt(trgt), arg(arg), oftype(oftype), sguard(sguard) {;}
    virtual ~RegisterAssignOp() {;}
};

class ReturnAssignOp : public InterpOp
{
public:
    const Argument arg;
    const BSQType* oftype;
    
    ReturnAssignOp(SourceInfo sinfo, Argument arg, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ReturnAssignOp), arg(arg), oftype(oftype) {;}
    virtual ~ReturnAssignOp() {;}
};

class ReturnAssignOfConsOp : public InterpOp
{
public:
    const std::vector<Argument> args;
    const BSQType* oftype;
    
    ReturnAssignOfConsOp(SourceInfo sinfo, std::vector<Argument> args, const BSQType* oftype) : InterpOp(sinfo, OpCodeTag::ReturnAssignOfConsOp), args(args), oftype(oftype) {;}
    virtual ~ReturnAssignOfConsOp() {;}
};

class VarLifetimeStartOp : public InterpOp
{
public:
    const Argument homelocation;
    const BSQType* oftype;
    const std::string* name;
    
    VarLifetimeStartOp(SourceInfo sinfo, Argument homelocation, const BSQType* oftype, const std::string* name) : InterpOp(sinfo, OpCodeTag::VarLifetimeStartOp), homelocation(homelocation), oftype(oftype), name(name) {;}
    virtual ~VarLifetimeStartOp() {;}
};

class VarLifetimeEndOp : public InterpOp
{
public:
    const std::string* name;
    
    VarLifetimeEndOp(SourceInfo sinfo, const std::string* name) : InterpOp(sinfo, OpCodeTag::VarLifetimeEndOp), name(name) {;}
    virtual ~VarLifetimeEndOp() {;}
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
};

