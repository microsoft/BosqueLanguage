//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

jmp_buf Environment::g_entrybuff;
bool Environment::g_small_model_gen = true;

uint8_t* Environment::g_constantbuffer = nullptr;
std::vector<BSQInvokeDecl*> Environment::g_invokes;

std::map<std::string, BSQTypeID> Environment::g_typenameToIDMap;
std::map<std::string, RefMask> Environment::g_stringmaskToDeclMap;
std::map<std::string, BSQRecordPropertyID> Environment::g_propertynameToIDMap;
std::map<std::string, BSQFieldID> Environment::g_fieldnameToIDMap;
std::map<std::string, BSQInvokeID> Environment::g_invokenameToIDMap;
std::map<std::string, BSQVirtualInvokeID> Environment::g_vinvokenameToIDMap;
