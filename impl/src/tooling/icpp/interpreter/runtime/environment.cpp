//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

jmp_buf Environment::g_entrybuff;
bool Environment::g_small_model_gen = true;

uint8_t* Environment::g_constantbuffer = nullptr;
std::vector<BSQInvokeDecl*> Environment::g_invokes;

