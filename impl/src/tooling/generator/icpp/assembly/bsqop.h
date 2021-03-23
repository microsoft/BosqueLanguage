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
    LoadTupleIndexSetGuardVirtualOp
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
    const std::wstring msg;

    AbortOp(SourceInfo sinfo, const std::wstring& msg) : InterpOp(sinfo, OpCodeTag::AbortOp), msg(msg) {;}
    virtual ~AbortOp() {;}
};

class AssertOp : public InterpOp
{
public:
    const Argument arg;
    const std::wstring msg;

    AssertOp(SourceInfo sinfo, Argument arg, const std::wstring& msg) : InterpOp(sinfo, OpCodeTag::AssertOp), arg(arg), msg(msg) {;}
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
    const BSQTupleIndex idx;

    LoadTupleIndexDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQTupleType* argtype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), idx(idx) {;}
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
    const BSQTupleIndex idx;

    LoadTupleIndexSetGuardDirectOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, const BSQTupleType* argtype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardDirectOp), trgt(trgt), trgttype(trgttype), arg(arg), argtype(argtype), idx(idx) {;}
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

    LoadTupleIndexSetGuardVirtualOp(SourceInfo sinfo, TargetVar trgt, const BSQType* trgttype, Argument arg, BSQType* layouttype, BSQTupleIndex idx) : InterpOp(sinfo, OpCodeTag::LoadTupleIndexSetGuardVirtualOp), trgt(trgt), trgttype(trgttype), arg(arg), layouttype(layouttype), idx(idx) {;}
    virtual ~LoadTupleIndexSetGuardVirtualOp() {;}
};