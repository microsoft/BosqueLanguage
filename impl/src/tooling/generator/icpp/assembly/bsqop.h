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
    ConstNone,
    ConstTrue,
    ConstFalse,
    ConstNat,
    ConstInt,
    ConstBigNat,
    ConstBigInt,
    ConstRational,
    ConstFloat,
    ConstDecimal,
    ConstString,
    ConstStringOf,
    ConstDataString,
    ConstRegex,
    Register,
    Argument,
    GlobalConst
};

enum class OpCodeTag
{
    Invalid = 0x0,
    DeadFlowOp,
    AbortOp,
    AssertOp,
    DebugOp,
    LoadUnintVariableValueOp,
    ConvertValueOp,
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
    LoadEnityFieldDirectOp,
    LoadEnityFieldVirtualOp,
    LoadFromEpehmeralListOp,
    InvokeFixedFunctionOp,
    InvokeVirtualFunctionOp,
    InvokeVirtualOperatorOp,
    ConstructorTupleOp,
    ConstructorRecordOp,
    ConstructorEphemeralListOp,
    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp
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
    int32_t gindex; //-1 if this is var guard

    TargetVar gvar; //if gindex is -1
};

class InterpOp
{
public:
    const OpCodeTag tag;
    const SourceInfo sinfo;

    InterpOp(SourceInfo sinfo, OpCodeTag tag) : sinfo(sinfo), tag(tag) {;}
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
    const std::wstring* msg;

    AbortOp(SourceInfo sinfo, const std::wstring* msg) : InterpOp(sinfo, OpCodeTag::AbortOp), msg(msg) {;}
    virtual ~AbortOp() {;}
};

class AssertOp : public InterpOp
{
public:
    const Argument arg;
    const std::wstring* msg;

    AssertOp(SourceInfo sinfo, Argument arg, const std::wstring* msg) : InterpOp(sinfo, OpCodeTag::AssertOp), arg(arg), msg(msg) {;}
    virtual ~AssertOp() {;}
};

class DebugOp : public InterpOp
{
public:
    //Is invalid if this is a break
    const Argument arg;

    DebugOp(SourceInfo sinfo, Argument arg) : InterpOp(sinfo, OpCodeTag::DebugOp), arg(arg) {;}
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

class ConvertValueOp : public InterpOp
{
public:
    ConvertValueOp(SourceInfo sinfo) : InterpOp(sinfo, OpCodeTag::ConvertValueOp) {;}
    virtual ~ConvertValueOp() {;}
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
    const BSQType* layouttype;
    const BSQTupleIndex idx;

    TupleHasIndexOp(SourceInfo sinfo, TargetVar trgt, Argument arg, BSQType* layouttype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::TupleHasIndexOp), trgt(trgt), arg(arg), layouttype(layouttype), idx(idx) {;}
    virtual ~TupleHasIndexOp() {;}
};

class RecordHasPropertyOp : public InterpOp
{
public:
    const TargetVar trgt;
    const Argument arg;
    const BSQType* layouttype;
    const BSQRecordPropertyID propId;

    RecordHasPropertyOp(SourceInfo sinfo, TargetVar trgt, Argument arg, BSQType* layouttype, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::RecordHasPropertyOp), trgt(trgt), arg(arg), layouttype(layouttype), propId(propId) {;}
    virtual ~RecordHasPropertyOp() {;}
};

class LoadTupleIndexDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQTupleType* argtype;
    const uint32_t slotoffset;
    const BSQTupleIndex idx;

    LoadTupleIndexDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQTupleType* argtype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), idx(idx) {;}
    virtual ~LoadTupleIndexDirectOp() {;}
};

class LoadTupleIndexVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQTupleIndex idx;

    LoadTupleIndexVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), idx(idx) {;}
    virtual ~LoadTupleIndexVirtualOp() {;}
};

class LoadTupleIndexSetGuardDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQTupleType* argtype;
    const uint32_t slotoffset;
    const BSQTupleIndex idx;
    const BSQGuard guard;

    LoadTupleIndexSetGuardDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQTupleType* argtype, BSQTupleIndex idx, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), idx(idx), guard(guard) {;}
    virtual ~LoadTupleIndexSetGuardDirectOp() {;}
};

class LoadTupleIndexSetGuardVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQTupleIndex idx;
    const BSQGuard guard;

    LoadTupleIndexSetGuardVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQTupleIndex idx, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), idx(idx), guard(guard) {;}
    virtual ~LoadTupleIndexSetGuardVirtualOp() {;}
};

class LoadRecordPropertyDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQRecordType* argtype;
    const uint32_t slotoffset;
    const BSQRecordPropertyID propId;

    LoadRecordPropertyDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQRecordType* argtype, uint32_t slotoffset, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertyDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), propId(propId) {;}
    virtual ~LoadRecordPropertyDirectOp() {;}
};

class LoadRecordPropertyVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQRecordPropertyID propId;

    LoadRecordPropertyVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertyVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), propId(propId) {;}
    virtual ~LoadRecordPropertyVirtualOp() {;}
};

class LoadRecordPropertySetGuardDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQRecordType* argtype;
    const uint32_t slotoffset;
    const BSQRecordPropertyID propId;
    const BSQGuard guard;

    LoadRecordPropertySetGuardDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQRecordType* argtype, uint32_t slotoffset, BSQRecordPropertyID propId, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertySetGuardDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), propId(propId), guard(guard) {;}
    virtual ~LoadRecordPropertySetGuardDirectOp() {;}
};

class LoadRecordPropertySetGuardVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQRecordPropertyID propId;
    const BSQGuard guard;

    LoadRecordPropertySetGuardVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQRecordPropertyID propId, BSQGuard guard) : InterpOp(sinfo, OpCodeTag::LoadRecordPropertySetGuardVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), propId(propId), guard(guard) {;}
    virtual ~LoadRecordPropertySetGuardVirtualOp() {;}
};

class LoadEntityFieldDirectOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQStdEntityType* argtype;
    const uint32_t slotoffset;
    const BSQFieldID fieldId;

    LoadEntityFieldDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQStdEntityType* argtype, uint32_t slotoffset, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadEnityFieldDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), slotoffset(slotoffset), fieldId(fieldId) {;}
    virtual ~LoadEntityFieldDirectOp() {;}
};

class LoadEntityFieldVirtualOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const Argument arg;
    const BSQType* layouttype;
    const BSQFieldID fieldId;

    LoadEntityFieldVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQRecordPropertyID propId) : InterpOp(sinfo, OpCodeTag::LoadEnityFieldVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), fieldId(fieldId) {;}
    virtual ~LoadEntityFieldVirtualOp() {;}
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

class InvokeFixedFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQInvokeID invokeId;
    const std::vector<Argument> args;
    const int32_t optmaskoffset;

    InvokeFixedFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQInvokeID invokeId, const std::vector<Argument>& args, int32_t optmaskoffset) : InterpOp(sinfo, OpCodeTag::InvokeFixedFunctionOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args), optmaskoffset(optmaskoffset) {;}
    virtual ~InvokeFixedFunctionOp() {;}
};

class InvokeVirtualFunctionOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQVirtualInvokeID invokeId;
    const std::vector<Argument> args;
    
    InvokeVirtualFunctionOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQVirtualInvokeID invokeId, const std::vector<Argument>& args) : InterpOp(sinfo, OpCodeTag::InvokeVirtualFunctionOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args) {;}
    virtual ~InvokeVirtualFunctionOp() {;}
};

class InvokeVirtualOperatorOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQType* trgttype;
    const BSQVirtualInvokeID invokeId;
    const std::vector<Argument> args;
    
    InvokeVirtualOperatorOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, BSQVirtualInvokeID invokeId, const std::vector<Argument>& args) : InterpOp(sinfo, OpCodeTag::InvokeVirtualOperatorOp), trgt(trgt), trgttype(trgttype), invokeId(invokeId), args(args) {;}
    virtual ~InvokeVirtualOperatorOp() {;}
};

class ConstructorTupleOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQTupleType* oftype;
    const std::vector<Argument> args;
    
    ConstructorTupleOp(SourceInfo sinfo, TargetVar trgt, const BSQTupleType* oftype, const std::vector<Argument>& args) : InterpOp(sinfo, OpCodeTag::ConstructorTupleOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorTupleOp() {;}
};

class ConstructorRecordOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQRecordType* oftype;
    const std::vector<Argument> args;
    
    ConstructorRecordOp(SourceInfo sinfo, TargetVar trgt, const BSQRecordType* oftype, const std::vector<Argument>& args) : InterpOp(sinfo, OpCodeTag::ConstructorRecordOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorRecordOp() {;}
};

class ConstructorEphemeralListOp : public InterpOp
{
public:
    const TargetVar trgt;
    const BSQEphemeralListType* oftype;
    const std::vector<Argument> args;
    
    ConstructorEphemeralListOp(SourceInfo sinfo, TargetVar trgt, const BSQEphemeralListType* oftype, const std::vector<Argument>& args) : InterpOp(sinfo, OpCodeTag::ConstructorEphemeralListOp), trgt(trgt), oftype(oftype), args(args) {;}
    virtual ~ConstructorEphemeralListOp() {;}
};

    ConstructorPrimaryCollectionEmptyOp,
    ConstructorPrimaryCollectionSingletonsOp,
    ConstructorPrimaryCollectionCopiesOp,
    ConstructorPrimaryCollectionMixedOp








