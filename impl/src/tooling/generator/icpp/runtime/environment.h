//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

class Environment
{
public:
    //Constant storage locations
    static BSQNone g_constNone;
    static BSQBool g_constTrue;
    static BSQBool g_constFalse;
    static std::vector<BSQNat> g_constNats;
    static std::vector<BSQInt> g_constInts;

    static std::vector<BSQBigNat> g_constBigNats;
    static std::vector<BSQBigInt> g_constBigInts;
    ConstBigNat,
    ConstBigInt,
    ConstRational,
    ConstFloat,
    ConstDecimal,
    ConstString,
    ConstStringOf,
    ConstDataString,
    ConstRegex,
};
