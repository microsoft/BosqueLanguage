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

    //map from invoke id to decl
    static std::vector<BSQInvokeDecl*> g_invokes;

    //helpers for parsing -- map strings to decls
    static std::map<std::string, BSQTypeID> g_typenameToIDMap;
    static std::map<std::string, RefMask> g_stringmaskToDeclMap;
    static std::map<std::string, BSQRecordPropertyID> g_propertynameToIDMap;
    static std::map<std::string, BSQFieldID> g_fieldnameToIDMap;
    static std::map<std::string, BSQInvokeID> g_invokenameToIDMap;
    static std::map<std::string, BSQVirtualInvokeID> g_vinvokenameToIDMap;
    static std::map<std::string, BSQPrimitiveImplTag> g_primitiveinvokenameToIDMap;
};
