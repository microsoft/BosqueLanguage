//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "collection_eval.h"

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

std::map<BSQTypeID, BSQListTypeFlavor> BSQListOps::g_flavormap;

void BSQListOps::s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res)
{
    //TODO: support other types too
    assert(oftype->tid == BSQ_TYPE_ID_INT || oftype->tid == BSQ_TYPE_ID_NAT);

    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    if(oftype->tid == BSQ_TYPE_ID_INT)
    {
        auto ll = BSQListOps::s_range_ne_rec<BSQInt>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_INT)->second, SLPTR_LOAD_CONTENTS_AS(BSQInt, start), SLPTR_LOAD_CONTENTS_AS(BSQInt, count));
        LIST_STORE_RESULT_REPR(res, ll.first);
    }
    else
    {
        assert(oftype->tid == BSQ_TYPE_ID_NAT);

        auto ll = BSQListOps::s_range_ne_rec<BSQNat>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_NAT)->second, SLPTR_LOAD_CONTENTS_AS(BSQNat, start), SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
        LIST_STORE_RESULT_REPR(res, ll.first);
    }
    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
}

void BSQListOps::s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto ll = BSQListOps::s_fill_ne_rec(BSQListOps::g_flavormap.find(oftype->tid)->second, val, SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
    LIST_STORE_RESULT_REPR(res, ll);
    
    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
}

BSQNat BSQListOps::s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQType* lentrytype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t pos = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    {
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

        BSQBool found = BSQFALSE;
        StorageLocationPtr esl;
        BI_LAMBDA_CALL_SETUP_TEMP(lentrytype, esl, params, pred, lparams)

        while(iter.valid())
        {
            lentrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            pos++;
            iter.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    return (BSQNat)pos;
}

BSQNat BSQListOps::s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQType* lentrytype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t pos = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    {
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

        BSQBool found = BSQFALSE;
        StorageLocationPtr esl;
        BI_LAMBDA_CALL_SETUP_TEMP_IDX(lentrytype, esl, params, pred, lparams, &pos)

        while(iter.valid())
        {
            lentrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            pos++;
            iter.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    return (BSQNat)pos;
}

BSQNat BSQListOps::s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQType* lentrytype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t icount = ttype->getCount(t);
    int64_t pos = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    {
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

        BSQBool found = BSQFALSE;
        StorageLocationPtr esl;
        BI_LAMBDA_CALL_SETUP_TEMP(lentrytype, esl, params, pred, lparams)

        while(iter.valid())
        {
            lentrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            pos--;
            iter.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    return (BSQNat)(pos != -1 ? pos : icount);
}

BSQNat BSQListOps::s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQType* lentrytype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t icount = ttype->getCount(t);
    int64_t pos = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    {
        const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

        BSQBool found = BSQFALSE;
        StorageLocationPtr esl;
        BI_LAMBDA_CALL_SETUP_TEMP_IDX(lentrytype, esl, params, pred, lparams, &pos)

        while(iter.valid())
        {
            lentrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            pos--;
            iter.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    return (BSQNat)(pos != -1 ? pos : icount);
}
