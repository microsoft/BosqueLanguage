//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

jmp_buf Environment::g_entrybuff;
bool Environment::g_small_model_gen = true;

uint8_t* Environment::g_constantbuffer = nullptr;
std::vector<BSQInvokeDecl*> Environment::g_invokes;

std::map<std::string, std::pair<BSQTypeID, const BSQType*>> Environment::g_typenameToIDMap;
std::map<std::string, RefMask> Environment::g_stringmaskToDeclMap;
std::map<std::string, BSQRecordPropertyID> Environment::g_propertynameToIDMap;
std::map<std::string, BSQFieldID> Environment::g_fieldnameToIDMap;
std::map<std::string, BSQInvokeID> Environment::g_invokenameToIDMap;
std::map<std::string, BSQVirtualInvokeID> Environment::g_vinvokenameToIDMap;

std::map<std::string, BSQPrimitiveImplTag> Environment::g_primitiveinvokenameToIDMap = {
    {"validator_accepts", BSQPrimitiveImplTag::validator_accepts},

    {"string_empty", BSQPrimitiveImplTag::string_empty},
    {"string_append", BSQPrimitiveImplTag::string_append},

    {"stringof_string", BSQPrimitiveImplTag::stringof_string},
    {"stringof_from", BSQPrimitiveImplTag::stringof_from},

    {"list_size", BSQPrimitiveImplTag::list_size},
    {"list_empty", BSQPrimitiveImplTag::list_empty},
    {"list_unsafe_get", BSQPrimitiveImplTag::list_unsafe_get},
    {"list_fill", BSQPrimitiveImplTag::list_fill},
    {"list_concat2", BSQPrimitiveImplTag::list_concat2},
    {"list_haspredcheck", BSQPrimitiveImplTag::list_haspredcheck},
    {"list_haspredcheck_idx", BSQPrimitiveImplTag::list_haspredcheck_idx},
    {"list_findindexof", BSQPrimitiveImplTag::list_findindexof},
    {"list_findindexoflast", BSQPrimitiveImplTag::list_findindexoflast},
    {"list_findindexof_idx", BSQPrimitiveImplTag::list_findindexof_idx},
    {"list_findindexoflast_idx", BSQPrimitiveImplTag::list_findindexoflast_idx},
    {"list_minidx", BSQPrimitiveImplTag::list_minidx},
    {"list_maxidx", BSQPrimitiveImplTag::list_maxidx},
    {"list_sum", BSQPrimitiveImplTag::list_sum},
    {"list_filter", BSQPrimitiveImplTag::list_filter},
    {"list_filter_idx", BSQPrimitiveImplTag::list_filter_idx},
    {"list_slice", BSQPrimitiveImplTag::list_slice},
    {"list_map", BSQPrimitiveImplTag::list_map},
    {"list_map_idx", BSQPrimitiveImplTag::list_map_idx}
};
