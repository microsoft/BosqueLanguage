//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>

#include <optional>
#include <vector>
#include <map>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "z3++.h"

enum class TypeTag
{
    NoneTag = 0x0,
    BoolTag,
    NatTag,
    IntTag,
    BigNatTag,
    BigIntTag,
    RationalTag,
    FloatTag,
    DecimalTag,
    StringTag,
    StringOfTag,
    NumberOfTag,
    DataStringTag,
    ByteBufferTag,
    BufferTag,
    DataBufferTag,
    ISOTag,
    LogicalTag,
    UUIDTag,
    ContentHashTag
};

class Extractor;

class IType
{
public:
    const std::string name;

    IType(std::string name) : name(name) {;}
    virtual ~IType() {;}

    virtual void fuzz(RandGenerator& rnd) const = 0;
    virtual json extract(Extractor* ex, z3::expr ctx) const = 0;
};

class NoneType : public IType
{

};

class BoolType : public IType
{

};

class NatType : public IType
{

};

class IntType : public IType
{

};

class BigNatType : public IType
{

};

class BigIntType : public IType
{

};

class RationalType : public IType
{

};

class FloatType : public IType
{

};

class DecimalType : public IType
{

};

class StringType : public IType
{

};

class StringOfType : public IType
{

};

class NumberOfType : public IType
{

};

class DataStringType : public IType
{

};

class ByteBufferType : public IType
{

};

class BufferType : public IType
{

};

class DataBufferType : public IType
{

};

class ISOType : public IType
{

};

class LogicalType : public IType
{

};

class UUIDType : public IType
{

};

class ContentHashType : public IType
{

};


////
// ------ Need to add in the signature thing
////

class Extractor
{
public:
    z3::model m;
    std::map<std::string, std::optional<z3::func_decl>> consfuncs;

    //extend context

    //extract signature args

    //extract signature result
};