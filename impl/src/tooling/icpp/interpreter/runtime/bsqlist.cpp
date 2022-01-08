//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqlist.h"

#define BI_LAMBDA_CALL_SETUP_TEMP(TTYPE, TEMPSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_IDX(TTYPE, TEMPSL, PARAMS, PC, LPARAMS, IDXSL) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL, IDXSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_AND_RES(TTYPE, TEMPSL, RTYPE, RESSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        RESSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_POP() GCStack::popFrame();
