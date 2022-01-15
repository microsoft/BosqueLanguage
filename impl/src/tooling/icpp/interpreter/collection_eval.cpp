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

#define BI_LAMBDA_CALL_SETUP_TEMP_AND_RES_VECTOR(TTYPE, TEMPSL, RTYPE, RESSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.heapsize); \
        uint8_t* RESSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.heapsize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.heapmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_AND_RES_VECTOR_IDX(TTYPE, TEMPSL, RTYPE, RESSL, PARAMS, PC, LPARAMS, IDXSL) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.heapsize); \
        uint8_t* RESSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.heapsize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.heapmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL, IDXSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_X2_AND_RES(TTYPE1, TEMPSL1, TTYPE2, TEMPSL2, RTYPE, RESSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL1 = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE1->allocinfo.inlinedatasize + TTYPE2->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        uint8_t* TEMPSL2 = TEMPSL1 + TTYPE1->allocinfo.inlinedatasize; \
        uint8_t* RESSL = TEMPSL2 + TTYPE2->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL1, TTYPE1->allocinfo.inlinedatasize + TTYPE2->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        std::string msk = std::string(TTYPE1->allocinfo.inlinedmask) + std::string(TTYPE2->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)TEMPSL1, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL1, TEMPSL2}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_REDUCE(TTYPE, TEMPSL, PARAMS, PC, LPARAMS, RSL) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {RSL, TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        }); 

#define BI_LAMBDA_CALL_SETUP_REDUCE_IDX(TTYPE, TEMPSL, PARAMS, PC, LPARAMS, RSL, POS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize); \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize); \
        GCStack::pushFrame((void**)TEMPSL, TTYPE->allocinfo.inlinedmask); \
        std::vector<StorageLocationPtr> LPARAMS = {RSL, TEMPSL, POS}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_TEMP_X2_CMP(TTYPE1, TEMPSL1, TTYPE2, TEMPSL2, PARAMS, PC, LPARAMS) uint8_t* TEMPSL1 = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE1->allocinfo.inlinedatasize + TTYPE2->allocinfo.inlinedatasize); \
        uint8_t* TEMPSL2 = TEMPSL1 + TTYPE1->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL1, TTYPE1->allocinfo.inlinedatasize + TTYPE2->allocinfo.inlinedatasize); \
        std::string msk = std::string(TTYPE1->allocinfo.inlinedmask) + std::string(TTYPE2->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)TEMPSL1, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {TEMPSL1, TEMPSL2}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(PVTYPE, PVL) GC_MEM_ZERO(PVL, PVTYPE->allocinfo.heapsize)

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

BSQNat BSQListOps::s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t pos = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        BSQBool found = BSQFALSE;
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

BSQNat BSQListOps::s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t pos = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        BSQBool found = BSQFALSE;
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

BSQNat BSQListOps::s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t icount = ttype->getCount(t);
    int64_t pos = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
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

BSQNat BSQListOps::s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    int64_t icount = ttype->getCount(t);
    int64_t pos = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        BSQBool found = BSQFALSE;
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

void* BSQListOps::s_filter_pred_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    void* rres = nullptr;
    {
        BI_LAMBDA_CALL_SETUP_TEMP(lflavor.entrytype, esl, params, pred, lparams)
    
        rres = BSQListOps::list_tree_transform(lflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);
           
            std::bitset<8> mask;
            BSQBool found = BSQFALSE;
            int16_t fcount = 0;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, &found);

                mask.set(i, found);
                fcount += found;
            }

            void* pvinto = nullptr;
            if(fcount != 0)
            {
                pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((fcount <= 4) ? lflavor.pv4type : lflavor.pv8type);
                BSQPartialVectorType::packPVData(pvinto, reprnode->repr, mask, lflavor.entrytype->allocinfo.inlinedatasize);
            }

            lflavor.entrytype->clearValue(esl);
            return pvinto;
        });
    
        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}

void* BSQListOps::s_filter_pred_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    void* rres = nullptr;
    {
        BSQNat pos = 0;
        BI_LAMBDA_CALL_SETUP_TEMP_IDX(lflavor.entrytype, esl, params, pred, lparams, &pos)
    
        rres = BSQListOps::list_tree_transform_idx(lflavor, rnode, 0, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype, uint64_t idx) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);

            std::bitset<8> mask;
            BSQBool found = BSQFALSE;
            int16_t fcount = 0;
            pos = idx;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, &found);
               
                mask.set(i, found);
                fcount += found;
                    
                pos++;
            }

            void* pvinto = nullptr;
            if(fcount != 0)
            {
                pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((fcount <= 4) ? lflavor.pv4type : lflavor.pv8type);
                BSQPartialVectorType::packPVData(pvinto, reprnode->repr, mask, lflavor.entrytype->allocinfo.inlinedatasize);
            }

            lflavor.entrytype->clearValue(esl);
            return pvinto;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}
    

void* BSQListOps::s_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        BI_LAMBDA_CALL_SETUP_TEMP_AND_RES_VECTOR(lflavor.entrytype, esl, resflavor.pv8type, resl, params, fn, lparams)

        rres = BSQListOps::list_tree_transform(lflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, resflavor.pv8type->get(resl, i));
            }

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? resflavor.pv4type : resflavor.pv8type);
            BSQPartialVectorType::directCopyPVData(pvinto, resl, resflavor.entrytype->allocinfo.inlinedatasize);

            lflavor.entrytype->clearValue(esl);
            BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(resflavor.pv8type, resl);
            return pvinto;
        });
    
        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}

void* BSQListOps::s_map_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        BSQNat pos = 0;
        BI_LAMBDA_CALL_SETUP_TEMP_AND_RES_VECTOR_IDX(lflavor.entrytype, esl, resflavor.pv8type, resl, params, fn, lparams, &pos)

        rres = BSQListOps::list_tree_transform_idx(lflavor, rnode, 0, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype, uint64_t idx) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);

            pos = idx;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, resflavor.pv8type->get(resl, i));
            }

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? resflavor.pv4type : resflavor.pv8type);
            BSQPartialVectorType::directCopyPVData(pvinto, resl, resflavor.entrytype->allocinfo.inlinedatasize);

            lflavor.entrytype->clearValue(esl);
            BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(resflavor.pv8type, resl);
            return pvinto;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}

void* BSQListOps::s_map_sync_ne(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, void* t1, const BSQListReprType* ttype1, void* t2, const BSQListReprType* ttype2, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    BSQListForwardIterator iter1(ttype1, t1);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter1);

    BSQListForwardIterator iter2(ttype2, t2);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter2);

    auto rootipos = Allocator::GlobalAllocator.getTempRootCurrPos();

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_AND_RES(lflavor1.entrytype, esl1, lflavor2.entrytype, esl2, resflavor.entrytype, resl, params, fn, lparams)

        while(iter1.valid() & iter2.valid())
        {
            lflavor1.entrytype->storeValue(esl1, iter1.getlocation());
            lflavor2.entrytype->storeValue(esl2, iter2.getlocation());
            ee.invoke(icall, lparams, resl);
            
            auto rr = Allocator::GlobalAllocator.registerTempRoot(resflavor.entrytype, nullptr);
            resflavor.entrytype->storeValue(rr->root, resl);

            iter1.advance();
            iter2.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter2);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter1);
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrPos();
    void* rres = BSQListOps::s_temp_root_to_list_rec(resflavor, lstart, count);

    Allocator::GlobalAllocator.resetRootCurrPos(rootipos);
    auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    
    return rres;
}

void BSQListOps::s_reduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res)
{
    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);

    {
        BI_LAMBDA_CALL_SETUP_REDUCE(lflavor.entrytype, esl, params, f, lparams, res)

        iter.advance(); //first element is always setup in the reduce value before calling this
        while(iter.valid())
        {
            lflavor.entrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, res);

            iter.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);
}

void BSQListOps::s_reduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res)
{
    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);

    {
        BSQNat pos = 1;
        BI_LAMBDA_CALL_SETUP_REDUCE_IDX(lflavor.entrytype, esl, params, f, lparams, res, &pos)

        iter.advance(); //first element is always setup in the reduce value before calling this
        while(iter.valid())
        {
            lflavor.entrytype->storeValue(esl, iter.getlocation());
            ee.invoke(icall, lparams, res);

            iter.advance();
            pos++;
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);
}

void* BSQListOps::s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQType* etype, StorageLocationPtr eres)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);

    void* rres = nullptr;
    {
        BI_LAMBDA_CALL_SETUP_TRANSDUCE(lflavor.entrytype, esl, resflavor.pv8type, resl, params, fn, lparams)

        rres = BSQListOps::list_tree_transform(lflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, resflavor.pv8type->get(resl, i));
            }

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? resflavor.pv4type : resflavor.pv8type);
            BSQPartialVectorType::directCopyPVData(pvinto, resl, resflavor.entrytype->allocinfo.inlinedatasize);

            lflavor.entrytype->clearValue(esl);
            BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(resflavor.pv8type, resl);
            return pvinto;
        });
    
        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}

void* BSQListOps::s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQType* etype, StorageLocationPtr eres)
{
    xxxx;
}

void* BSQListOps::s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params)
{
    //
    //TODO: this is somewhat inefficient -- we can do a better merge sort here
    //

    uint64_t count = ttype->getCount(t);

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    auto rootipos = Allocator::GlobalAllocator.getTempRootCurrPos();
    while(iter.valid())
    {
        auto rr = Allocator::GlobalAllocator.registerTempRoot(lflavor.entrytype, nullptr);
        lflavor.entrytype->storeValue(rr->root, iter.getlocation());

        iter.advance();
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[lt->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_CMP(lflavor.entrytype, esl, lflavor.entrytype, esr, params, lt, lparams)

        std::stable_sort(Allocator::GlobalAllocator.getTempRootCurrPos(), rootipos, [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
            BSQBool bb;
            ee.invoke(icall, lparams, &bb);
            return (bool)bb;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrPos();
    void* rres = BSQListOps::s_temp_root_to_list_rec(lflavor, lstart, count);

    Allocator::GlobalAllocator.resetRootCurrPos(rootipos);
    auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    
    return rres;
}

void* BSQListOps::s_unique_from_sorted_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* eq, const std::vector<StorageLocationPtr>& params)
{
    //
    //TODO: this is somewhat inefficient -- we can do a better merge sort here
    //

    uint64_t count = ttype->getCount(t);

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    auto rootipos = Allocator::GlobalAllocator.getTempRootCurrPos();
    while(iter.valid())
    {
        auto rr = Allocator::GlobalAllocator.registerTempRoot(lflavor.entrytype, nullptr);
        lflavor.entrytype->storeValue(rr->root, iter.getlocation());

        iter.advance();
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[eq->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_CMP(lflavor.entrytype, esl, lflavor.entrytype, esr, params, eq, lparams)

        std::unique(Allocator::GlobalAllocator.getTempRootCurrPos(), rootipos, [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
            BSQBool bb;
            ee.invoke(icall, lparams, &bb);
            return (bool)bb;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrPos();
    void* rres = BSQListOps::s_temp_root_to_list_rec(lflavor, lstart, count);

    Allocator::GlobalAllocator.resetRootCurrPos(rootipos);
    auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    
    return rres;
}
