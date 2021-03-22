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

struct Argument
{
    ArgumentTag kind;
    uint32_t location;
};

enum class OPCode
{
    InvalidOp = 0x0,
    DeadFlowOp,
    AbortOp,
    AssertOp
};

struct SourceInfo
{
    uint32_t line;
    uint32_t column;
};

class InterpOp
{
public:
    const SourceInfo sinfo;

    InterpOp(SourceInfo sinfo) : sinfo(sinfo) {;}
    virtual ~InterpOp() {;}
};

class DeadFlowOp : public InterpOp
{
public:
    DeadFlowOp(SourceInfo sinfo) : InterpOp(sinfo) {;}
    virtual ~DeadFlowOp() {;}
};

class AbortOp : public InterpOp
{
public:
    const std::wstring msg;

    AbortOp(SourceInfo sinfo, const std::wstring& msg) : InterpOp(sinfo), msg(msg) {;}
    virtual ~AbortOp() {;}
};

class AssertOp : public InterpOp
{
public:
    const Argument arg;
    const std::wstring msg;

    AssertOp(SourceInfo sinfo, Argument arg, const std::wstring& msg) : InterpOp(sinfo), arg(arg), msg(msg) {;}
    virtual ~AssertOp() {;}
};

class DebugOp : public InterpOp
{
public:
    //Is invalid if this is a break
    const Argument arg;

    DebugOp(SourceInfo sinfo, Argument arg) : InterpOp(sinfo), arg(arg) {;}
    virtual ~DebugOp() {;}
};

//This op does not need to be emitted if we are in a release build
class LoadUnintVariableValueOp : public InterpOp
{
public:
    const SLValue trgt;
    const BSQType* oftype;

    LoadUnintVariableValueOp(SourceInfo sinfo, SLValue trgt, BSQType* oftype) : InterpOp(sinfo), trgt(trgt), oftype(oftype) {;}
    virtual ~LoadUnintVariableValueOp() {;}
};

class ConvertValueOp : public InterpOp
{
public:
    ConvertValueOp(SourceInfo sinfo) : InterpOp(sinfo) {;}
    virtual ~ConvertValueOp() {;}
};