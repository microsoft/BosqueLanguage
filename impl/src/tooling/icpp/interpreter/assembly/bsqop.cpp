//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqop.h"
#include "../core/bsqmemory.h"
#include "../runtime/environment.h"

template <typename T>
T jsonGetAsTag(boost::json::value& val, const char* prop)
{
    assert(val.is_object());
    return (T)val.as_object().at(prop).as_uint64();
}

template <typename T>
T jsonGetAsInt(boost::json::value& val, const char* prop)
{
    assert(val.is_object());
    return (T)val.as_object().at(prop).as_int64();
}

template <typename T>
T jsonGetAsUInt(boost::json::value& val, const char* prop)
{
    assert(val.is_object());
    return (T)val.as_object().at(prop).as_uint64();
}

std::string jsonGetAsString(boost::json::value& val, const char* prop)
{
    assert(val.is_object());
    return xxxx; val.as_object().at(prop).as_string();
}

void jsonParse_Argument(boost::json::value& val, Argument& arg)
{
    arg.kind = jsonGetAsTag<ArgumentTag>(val, "kind");
    arg.location = jsonGetAsUInt<uint32_t>(val, "location");
}

void jsonParse_TargetVar(boost::json::value& val, TargetVar& tvar)
{
    xxxx;
}

void jsonParse_SourceInfo(boost::json::value& val, SourceInfo& sinfo)
{
    xxxx;
}

void jsonParse_BSQGuard(boost::json::value& val, BSQGuard& guard)
{
    xxxx;
}

void jsonParse_BSQStatementGuard(boost::json::value& val, BSQStatementGuard& sguard)
{
    xxxx;
}