//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

uint8_t* Environment::g_constantbuffer = nullptr;

std::vector<std::vector<BSQTypeID>> Environment::g_subtypes;
std::vector<BSQInvokeDecl*> Environment::g_invokes;

