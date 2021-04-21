//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

BSQNone Environment::g_constNone = 0;
BSQBool Environment::g_constTrue = (BSQBool)true;
BSQBool Environment::g_constFalse = (BSQBool)false;
BSQNat* Environment::g_constNats = nullptr;
BSQInt* Environment::g_constInts = nullptr;

BSQBigNat* Environment::g_constBigNats = nullptr;
BSQBigInt* Environment::g_constBigInts = nullptr;
BSQRational* Environment::g_constRationals = nullptr;
BSQFloat* Environment::g_constFloats = nullptr;
BSQDecimal* Environment::g_constDecimals = nullptr;
BSQString* Environment::g_constStrings = nullptr; 
BSQRegex* Environment::g_constRegexs = nullptr;

ConstValueLoad* Environment::g_constLoads = nullptr;

