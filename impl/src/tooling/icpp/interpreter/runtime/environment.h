//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqvalue.h"
#include "bsqcollections.h"

#include "../assembly/bsqassembly.h"

class Environment
{
public:
    static jmp_buf g_entrybuff;
    static bool g_small_model_gen;

    //Constant storage locations
    static uint8_t* g_constantbuffer; 
    static std::vector<BSQInvokeDecl*> g_invokes;
};
