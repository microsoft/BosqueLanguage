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

#define BI_LAMBDA_CALL_SETUP_TRANSDUCE(TTYPE, TEMPSL, RLTYPE, RSL, ENVTYPE, ENVSL, TYPEOUT, OUTSL, PARAMS, PC, LPARAMS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + ENVTYPE->allocinfo.inlinedatasize + TYPEOUT->allocinfo.inlinedatasize + RLTYPE->allocinfo.heapsize); \
        uint8_t* ENVSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        uint8_t* OUTSL = ENVSL + ENVTYPE->allocinfo.inlinedatasize; \
        uint8_t* RSL = OUTSL + TYPEOUT->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize + ENVTYPE->allocinfo.inlinedatasize + RLTYPE->allocinfo.heapsize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(ENVTYPE->allocinfo.inlinedmask) + std::string(TYPEOUT->allocinfo.inlinedmask) + std::string(RLTYPE->allocinfo.heapmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {ENVSL, TEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        }); 

#define BI_LAMBDA_CALL_SETUP_TRANSDUCE_IDX(TTYPE, TEMPSL, RLTYPE, RSL, ENVTYPE, ENVSL, TYPEOUT, OUTSL, PARAMS, PC, LPARAMS, POS) uint8_t* TEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(TTYPE->allocinfo.inlinedatasize + ENVTYPE->allocinfo.inlinedatasize + TYPEOUT->allocinfo.inlinedatasize + RLTYPE->allocinfo.heapsize); \
        uint8_t* ENVSL = TEMPSL + TTYPE->allocinfo.inlinedatasize; \
        uint8_t* OUTSL = ENVSL + ENVTYPE->allocinfo.inlinedatasize; \
        uint8_t* RSL = OUTSL + TYPEOUT->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(TEMPSL, TTYPE->allocinfo.inlinedatasize + ENVTYPE->allocinfo.inlinedatasize + RLTYPE->allocinfo.heapsize); \
        std::string msk = std::string(TTYPE->allocinfo.inlinedmask) + std::string(ENVTYPE->allocinfo.inlinedmask) + std::string(TYPEOUT->allocinfo.inlinedmask) + std::string(RLTYPE->allocinfo.heapmask); \
        GCStack::pushFrame((void**)TEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {ENVSL, TEMPSL, POS}; \
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


#define BI_LAMBDA_CALL_SETUP_KV_TEMP(KTYPE, KTEMPSL, VTYPE, VTEMPSL, PARAMS, PC, LPARAMS) uint8_t* KTEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(KTYPE->allocinfo.inlinedatasize + VTYPE->allocinfo.inlinedatasize); \
        uint8_t* VTEMPSL = KTEMPSL + KTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(KTEMPSL, KTYPE->allocinfo.inlinedatasize + VTYPE->allocinfo.inlinedatasize); \
        std::string msk = std::string(KTYPE->allocinfo.inlinedmask) + std::string(VTYPE->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)KTEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {KTEMPSL, VTEMPSL}; \
        std::transform(PC->cargpos.cbegin(), PC->cargpos.cend(), std::back_inserter(LPARAMS), [&PARAMS](uint32_t pos) { \
            return PARAMS[pos]; \
        });

#define BI_LAMBDA_CALL_SETUP_KV_TEMP_AND_RES(KTYPE, KTEMPSL, VTYPE, VTEMPSL, RTYPE, RESSL, PARAMS, PC, LPARAMS) uint8_t* KTEMPSL = (uint8_t*)BSQ_STACK_SPACE_ALLOC(KTYPE->allocinfo.inlinedatasize + VTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        uint8_t* VTEMPSL = KTEMPSL + KTYPE->allocinfo.inlinedatasize; \
        uint8_t* RESSL = VTEMPSL + VTYPE->allocinfo.inlinedatasize; \
        GC_MEM_ZERO(KTEMPSL, KTYPE->allocinfo.inlinedatasize + VTYPE->allocinfo.inlinedatasize + RTYPE->allocinfo.inlinedatasize); \
        std::string msk = std::string(KTYPE->allocinfo.inlinedmask) + std::string(VTYPE->allocinfo.inlinedmask) + std::string(RTYPE->allocinfo.inlinedmask); \
        GCStack::pushFrame((void**)KTEMPSL, msk.c_str()); \
        std::vector<StorageLocationPtr> LPARAMS = {KTEMPSL, VTEMPSL}; \
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

void* BSQListOps::s_reverse_ne(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode)
{
    auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
    auto count = reprtype->getCount(reprnode->repr);

    void* res = nullptr;
    if(reprtype->lkind == ListReprKind::PV4)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
        BSQPartialVectorType::setPVCount(res, (int16_t)count);
        for(int16_t i = 0; i < (int16_t)count; ++i)
        {
            lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), lflavor.pv4type->get(reprnode->repr, (int16_t)(count - 1) - i));
        }
    }
    else if(count <= 8)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
        BSQPartialVectorType::setPVCount(res, (int16_t)count);
        for(int16_t i = 0; i < (int16_t)count; ++i)
        {
            lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), lflavor.pv4type->get(reprnode->repr, (int16_t)(count - 1) - i));
        }
    }
    else
    {
        auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
        auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
        auto llnode = BSQListOps::s_reverse_ne(lflavor, lnode);
        auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

        auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
        auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
        auto rrnode = BSQListOps::s_reverse_ne(lflavor, rnode);
        auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

        res = BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
    }

    return res;
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

    Allocator::GlobalAllocator.pushTempRootScope();

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_AND_RES(lflavor1.entrytype, esl1, lflavor2.entrytype, esl2, resflavor.entrytype, resl, params, fn, lparams)

        while(iter1.valid() & iter2.valid())
        {
            lflavor1.entrytype->storeValue(esl1, iter1.getlocation());
            lflavor2.entrytype->storeValue(esl2, iter2.getlocation());
            ee.invoke(icall, lparams, resl);
            
            auto rr = Allocator::GlobalAllocator.registerTempRoot(resflavor.entrytype);
            resflavor.entrytype->storeValue(rr->root, resl);

            iter1.advance();
            iter2.advance();
        }

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter2);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter1);
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrScope().begin();
    void* rres = BSQListOps::s_temp_root_to_list_rec(resflavor, lstart, count);

    Allocator::GlobalAllocator.popTempRootScope();
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

void* BSQListOps::s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);
    const BSQEphemeralListType* pcrtype = dynamic_cast<const BSQEphemeralListType*>(icall->resultType);

    void* rres = nullptr;
    {
        BI_LAMBDA_CALL_SETUP_TRANSDUCE(lflavor.entrytype, esl, uflavor.pv8type, rsl, envtype, envsl, pcrtype, outsl, params, f, lparams)
        envtype->storeValue(envsl, params[1]);

        rres = BSQListOps::list_tree_transform(lflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, outsl);

                envtype->storeValue(envsl, pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[0]));
                uflavor.entrytype->storeValue(uflavor.pv8type->get(rsl, i), pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[1]));
            }

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? uflavor.pv4type : uflavor.pv8type);
            BSQPartialVectorType::directCopyPVData(pvinto, rsl, uflavor.entrytype->allocinfo.inlinedatasize);

            lflavor.entrytype->clearValue(esl);
            pcrtype->clearValue(outsl);
            envtype->clearValue(envsl);
            BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(uflavor.pv8type, rsl);
            return pvinto;
        });
    
        envtype->storeValue(rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[0]), envsl);

        auto lsl = rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[1]);
        LIST_STORE_RESULT_REPR(rres, lsl);

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
}

void* BSQListOps::s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);
    const BSQEphemeralListType* pcrtype = dynamic_cast<const BSQEphemeralListType*>(icall->resultType);

    void* rres = nullptr;
    {
        BSQNat pos = 0;
        BI_LAMBDA_CALL_SETUP_TRANSDUCE_IDX(lflavor.entrytype, esl, uflavor.pv8type, rsl, envtype, envsl, pcrtype, outsl, params, f, lparams, &pos)
        envtype->storeValue(envsl, params[1]);

        rres = BSQListOps::list_tree_transform(lflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, const BSQPartialVectorType* reprtype, uint64_t idx) {
            int16_t vcount = reprtype->getPVCount(reprnode->repr);
        
            pos = idx;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(reprnode->repr, i));
                ee.invoke(icall, lparams, outsl);

                envtype->storeValue(envsl, pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[0]));
                uflavor.entrytype->storeValue(uflavor.pv8type->get(rsl, i), pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[1]));
            }

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? uflavor.pv4type : uflavor.pv8type);
            BSQPartialVectorType::directCopyPVData(pvinto, rsl, uflavor.entrytype->allocinfo.inlinedatasize);

            lflavor.entrytype->clearValue(esl);
            pcrtype->clearValue(outsl);
            envtype->clearValue(envsl);
            BI_LAMBDA_CALL_SETUP_CLEAR_TEMP_PV(uflavor.pv8type, rsl);
            return pvinto;
        });
    
        envtype->storeValue(rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[0]), envsl);

        auto lsl = rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[1]);
        LIST_STORE_RESULT_REPR(rres, lsl);

        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
}

void* BSQListOps::s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params)
{
    //
    //TODO: this is somewhat inefficient -- we can do a better merge sort here
    //

    uint64_t count = ttype->getCount(t);

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    Allocator::GlobalAllocator.pushTempRootScope();
    while(iter.valid())
    {
        auto rr = Allocator::GlobalAllocator.registerTempRoot(lflavor.entrytype);
        lflavor.entrytype->storeValue(rr->root, iter.getlocation());

        iter.advance();
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[lt->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_CMP(lflavor.entrytype, esl, lflavor.entrytype, esr, params, lt, lparams)

        std::list<BSQTempRootNode>& roots = Allocator::GlobalAllocator.getTempRootCurrScope();
        std::stable_sort(roots.begin(), roots.end(), [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
            BSQBool bb;
            ee.invoke(icall, lparams, &bb);
            return (bool)bb;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrScope().begin();
    void* rres = BSQListOps::s_temp_root_to_list_rec(lflavor, lstart, count);

    Allocator::GlobalAllocator.popTempRootScope();
    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    
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

    Allocator::GlobalAllocator.pushTempRootScope();
    while(iter.valid())
    {
        auto rr = Allocator::GlobalAllocator.registerTempRoot(lflavor.entrytype);
        lflavor.entrytype->storeValue(rr->root, iter.getlocation());

        iter.advance();
    }

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[eq->code]);

    {
        BI_LAMBDA_CALL_SETUP_TEMP_X2_CMP(lflavor.entrytype, esl, lflavor.entrytype, esr, params, eq, lparams)

        std::list<BSQTempRootNode>& roots = Allocator::GlobalAllocator.getTempRootCurrScope();
        std::unique(roots.begin(), roots.end(), [&](const BSQTempRootNode& ln, const BSQTempRootNode& rn) {
            BSQBool bb;
            ee.invoke(icall, lparams, &bb);
            return (bool)bb;
        });

        BI_LAMBDA_CALL_SETUP_POP()
    }
    
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrScope().begin();
    void* rres = BSQListOps::s_temp_root_to_list_rec(lflavor, lstart, count);

    Allocator::GlobalAllocator.popTempRootScope();
    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    
    return rres;
}

std::map<std::pair<BSQTypeID, BSQTypeID>, BSQMapTypeFlavor> BSQMapOps::g_flavormap;

void s_union_rec_ne(const BSQMapTypeFlavor& mflavor, StorageLocationPtr tnode, BSQMapSpineIterator& ii)
{
    if(BSQMapTreeType::getLeft(ii.lcurr) != nullptr)
    {
        ii.moveLeft();
        s_union_rec_ne(mflavor, tnode, ii);
        ii.pop();
    }

    auto tmpi = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(tnode);
    auto tmpr = BSQMapOps::s_add_ne(mflavor, tmpi, mflavor.treetype, mflavor.treetype->getKeyLocation(ii.lcurr), mflavor.treetype->getKeyLocation(ii.lcurr));
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(tmpnam, tmpr);

    if(BSQMapTreeType::getRight(ii.lcurr) != nullptr)
    {
        ii.moveRight();
        s_union_rec_ne(mflavor, tnode, ii);
        ii.pop();
    }
}

void* BSQMapOps::s_union_ne(const BSQMapTypeFlavor& mflavor, void* t1, const BSQMapTreeType* ttype1, void* t2, const BSQMapTreeType* ttype2, uint64_t ccount)
{
    void* ll = t1;
    GCStack::pushFrame(&ll, "2");

    BSQMapSpineIterator iter2(ttype2, t2);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter2);
    s_union_rec_ne(mflavor, &ll, iter2);
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter2);

    GCStack::popFrame();
    return ll;
}

std::pair<void*, BSQNat> BSQMapOps::s_submap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    Allocator::GlobalAllocator.pushTempRootScope();

    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        BI_LAMBDA_CALL_SETUP_KV_TEMP(mflavor.keytype, ksl, mflavor.valuetype, vsl, params, pred, lparams)

        BSQMapOps::map_tree_flatten(mflavor, iter, [&](StorageLocationPtr lk, StorageLocationPtr lv) { 
            mflavor.keytype->storeValue(ksl, lk);
            mflavor.valuetype->storeValue(vsl, lv);

            BSQBool bb = BSQFALSE;
            ee.invoke(icall, lparams, &bb);

            mflavor.keytype->clearValue(ksl);
            mflavor.valuetype->clearValue(vsl);
            return (bool)bb;
        });
    
        BI_LAMBDA_CALL_SETUP_POP()
    }
    
    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);

    auto lstart = Allocator::GlobalAllocator.getTempRootCurrScope().begin();
    auto lsize = Allocator::GlobalAllocator.getTempRootCurrScope().size();
    auto llnode = BSQMapOps::s_temp_root_to_map_rec(mflavor, lstart, lsize);

    Allocator::GlobalAllocator.pushTempRootScope();

    return std::make_pair(llnode, (BSQNat)lsize);
}

void* BSQMapOps::s_remap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQMapTypeFlavor& resflavor)
{
    auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
    auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQMapTreeRepr*>(t));

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        BI_LAMBDA_CALL_SETUP_KV_TEMP_AND_RES(mflavor.keytype, ksl, mflavor.valuetype, vsl, resflavor.valuetype, resl, params, fn, lparams)

        rres = BSQMapOps::map_tree_transform(mflavor, rnode, [&](BSQCollectionGCReprNode* reprnode, BSQCollectionGCReprNode* ll, BSQCollectionGCReprNode* rr) {
            mflavor.keytype->storeValue(ksl, mflavor.treetype->getKeyLocation(reprnode->repr));
            mflavor.valuetype->storeValue(vsl, mflavor.treetype->getValueLocation(reprnode->repr));
            ee.invoke(icall, lparams, resl);

            void* tinto = (void*)Allocator::GlobalAllocator.allocateDynamic(resflavor.treetype);
            resflavor.treetype->initializeLR(tinto, mflavor.treetype->getKeyLocation(reprnode->repr), mflavor.keytype, resl, resflavor.valuetype, ll->repr, rr->repr);

            mflavor.keytype->clearValue(ksl);
            mflavor.valuetype->clearValue(vsl);
            resflavor.valuetype->clearValue(resl);
            return tinto;
        });
    
        BI_LAMBDA_CALL_SETUP_POP()
    }

    Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    return rres;
}

void* s_add_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl, uint32_t alloc)
{
    void* res = nullptr;

    if(iter.lcurr == nullptr)
    {
        Allocator::GlobalAllocator.ensureSpace(alloc);
        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLeaf(res, kl, mflavor.keytype, vl, mflavor.valuetype);
    }
    else
    {
        auto nalloc = alloc + mflavor.treetype->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);

        auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
        if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck))
        {
            iter.moveLeft();
            void* ll = s_add_ne_rec(mflavor, iter, kl, vl, nalloc);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, ll, BSQMapTreeType::getRight(iter.lcurr));
        }
        else
        {
            BSQ_INTERNAL_ASSERT(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl));

            iter.moveRight();
            void* rr = s_add_ne_rec(mflavor, iter, kl, vl, nalloc);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), rr);
        }
    }

    return res;
}

void* BSQMapOps::s_add_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    void* res = s_add_ne_rec(mflavor, iter, kl, vl, 0);

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);
    return res;
}

void* s_set_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl, uint32_t alloc)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    void* res;
    auto nalloc = alloc + mflavor.treetype->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);

    auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck))
    {
        iter.moveLeft();
        void* ll = s_add_ne_rec(mflavor, iter, kl, vl, nalloc);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, ll, BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl))
    {
        iter.moveRight();
        void* rr = s_add_ne_rec(mflavor, iter, kl, vl, nalloc);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), rr);
    }
    else
    {
        Allocator::GlobalAllocator.ensureSpace(nalloc);
        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, kl, mflavor.keytype, vl, mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), BSQMapTreeType::getRight(iter.lcurr));
    }

    return res;
}

void* BSQMapOps::s_set_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    void* res = s_set_ne_rec(mflavor, iter, kl, vl, 0);

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);
    return res;
}

std::pair<void*, void*> s_remove_rotate_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, uint32_t alloc)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    std::pair<void*, void*> res;
    if(BSQMapTreeType::getLeft(iter.lcurr) != nullptr)
    {
        auto nalloc = alloc + mflavor.treetype->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);

        iter.moveLeft();
        auto tnp = s_remove_rotate_ne_rec(mflavor, iter, kl, nalloc);
        iter.pop();

        res = std::make_pair((void*)Allocator::GlobalAllocator.allocateSafe(mflavor.treetype), tnp.second);
        mflavor.treetype->initializeLR(res.first, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, tnp.first, BSQMapTreeType::getRight(iter.lcurr));
    }
    else
    {
        Allocator::GlobalAllocator.ensureSpace(alloc);
        res = std::make_pair(nullptr, iter.lcurr);
    }

    return res;
}

void* s_remove_find_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, uint32_t alloc)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    void* res;
    auto nalloc = alloc + mflavor.treetype->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);

    auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck))
    {
        iter.moveLeft();
        void* ll = s_remove_find_ne_rec(mflavor, iter, kl, nalloc);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, ll, BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl))
    {
        iter.moveRight();
        void* rr = s_remove_find_ne_rec(mflavor, iter, kl, nalloc);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), rr);
    }
    else
    {
        Allocator::GlobalAllocator.ensureSpace(alloc);

        auto lltmp = BSQMapTreeType::getLeft(iter.lcurr);
        auto rrtmp = BSQMapTreeType::getRight(iter.lcurr);
        if(lltmp == nullptr && rrtmp == nullptr)
        {    
            res = nullptr;
        }
        else if(lltmp == nullptr)
        {
            res = rrtmp;
        }
        else if(rrtmp == nullptr)
        {
            res = lltmp;
        }
        else
        {
            iter.moveRight();
            auto tnp = s_remove_rotate_ne_rec(mflavor, iter, kl, nalloc);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(tnp.second), mflavor.keytype, mflavor.treetype->getValueLocation(tnp.second), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), tnp.first);
        }
    }

    return res;
}

void* BSQMapOps::s_remove_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.registerCollectionIterator(&iter);

    void* res = s_remove_find_ne_rec(mflavor, iter, kl, 0);

    Allocator::GlobalAllocator.releaseCollectionIterator(&iter);
    return res;
}

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto ltype = dynamic_cast<const BSQListType*>(btype);
    auto lflavor = BSQListOps::g_flavormap.find(ltype->etype)->second;

    std::string res = btype->name + "{";
    BSQListForwardIterator iter(LIST_LOAD_TYPE_INFO(data), LIST_LOAD_DATA(data));
    bool first = true;
    while(iter.valid())
    {
        if(!first)
        {
            res += ",";
        }

        res += lflavor.entrytype->fpDisplay(lflavor.entrytype, iter.getlocation());
    }
    res += "}";

    return res;
}


std::string entityMapDisplay_impl_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter)
{
    if(iter.lcurr == nullptr)
    {
        return "";
    }
    else
    {
        iter.moveLeft();
        auto ll = entityMapDisplay_impl_rec(mflavor, iter);
        iter.pop();

        auto iistr = mflavor.keytype->fpDisplay(mflavor.keytype, mflavor.treetype->getKeyLocation(iter.lcurr)) + " => " + mflavor.valuetype->fpDisplay(mflavor.valuetype, mflavor.treetype->getValueLocation(iter.lcurr));

        iter.moveRight();
        auto rr = entityMapDisplay_impl_rec(mflavor, iter);
        iter.pop();

        return ll + (ll.empty() ? "" : ", ") + iistr + (rr.empty() ? "" : ", ") + rr;
    }
}

std::string entityMapDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    auto mtype = dynamic_cast<const BSQMapType*>(btype);
    auto mflavor = BSQMapOps::g_flavormap.find(std::make_pair(mtype->ktype, mtype->vtype))->second;

    std::string res = btype->name + "{";
    BSQMapSpineIterator iter(MAP_LOAD_TYPE_INFO(data), MAP_LOAD_REPR(data));
    if(iter.valid())
    {
        res += entityMapDisplay_impl_rec(mflavor, iter);
    }
    res += "}";

    return res;
}