//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

#pragma once

namespace BSQ
{   
class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

//%%STATIC_INT_DECLARE%%

static const char* propertyNames[];

static std::u32string diagnostic_format(Value v);
};
} // namespace BSQ
