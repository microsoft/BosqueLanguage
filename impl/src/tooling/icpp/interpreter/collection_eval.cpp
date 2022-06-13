//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "collection_eval.h"

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

void* s_set_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, BSQNat i, StorageLocationPtr v)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);

    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto pvsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        auto pvalloc = pvsize <= 4 ? lflavor.pv4type : lflavor.pv8type;
        
        BSQPartialVectorType::setPVData(res, iter.lcurr, i, v, pvsize, pvalloc->entrysize);
    }
    else
    {
        auto trepr = static_cast<BSQListTreeRepr*>(iter.lcurr);
        auto ll = trepr->l;
        auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, ll);
        auto llcount = lltype->getCount(ll);

        void** stck = (void**)GCStack::allocFrame(sizeof(void*));
        if(i < llcount)
        {
            iter.moveLeft();
            stck[0] = s_set_ne_rec(lflavor, iter, i, v);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount;
        }
        else
        {
            iter.moveRight();
            stck[0] = s_set_ne_rec(lflavor, iter, i - llcount, v);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = static_cast<BSQListTreeRepr*>(iter.lcurr)->l;
            ((BSQListTreeRepr*)res)->r = stck[0];
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount;
        }
        GCStack::popFrame(sizeof(void*));
    }

    return res;
}

void* BSQListOps::s_set_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i, StorageLocationPtr v)
{
    BSQListSpineIterator iter(ttype, t);
    return s_set_ne_rec(lflavor, iter, i, v);
}

void* s_push_back_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, StorageLocationPtr v)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);

    void** stck = (void**)GCStack::allocFrame(sizeof(void*));
    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto vsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        if(vsize < 8)
        {
            auto pvsize = BSQPartialVectorType::getPVCount(iter.lcurr);
            auto pvalloc = pvsize <= 4 ? lflavor.pv4type : lflavor.pv8type;
        
            res = Allocator::GlobalAllocator.allocateDynamic(pvalloc);
            BSQPartialVectorType::pushBackPVData(res, iter.lcurr, v, pvalloc->entrysize);
        }
        else
        {
            stck[0] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::initializePVDataSingle(stck[0], v, lflavor.entrytype);

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = static_cast<BSQListTreeRepr*>(iter.lcurr);
            ((BSQListTreeRepr*)res)->r = stck[0];
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
        }
    }
    else
    {
        iter.moveRight();
        stck[0] = s_push_back_ne_rec(lflavor, iter, v);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
        ((BSQListTreeRepr*)res)->l = static_cast<BSQListTreeRepr*>(iter.lcurr)->l;
        ((BSQListTreeRepr*)res)->r = stck[0];
        ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
    }

    GCStack::popFrame(sizeof(void*));
    return res;
}

void* BSQListOps::s_push_back_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, StorageLocationPtr v)
{
    BSQListSpineIterator iter(ttype, t);
    return s_push_back_ne_rec(lflavor, iter, v);
}

void* s_push_front_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, StorageLocationPtr v)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);

    void** stck = (void**)GCStack::allocFrame(sizeof(void*));
    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto vsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        if(vsize < 8)
        {
            auto pvsize = BSQPartialVectorType::getPVCount(iter.lcurr);
            auto pvalloc = pvsize <= 4 ? lflavor.pv4type : lflavor.pv8type;
        
            res = Allocator::GlobalAllocator.allocateDynamic(pvalloc);
            BSQPartialVectorType::pushFrontPVData(res, iter.lcurr, v, pvalloc->entrysize);
        }
        else
        {
            stck[0] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::initializePVDataSingle(stck[0], v, lflavor.entrytype);

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
        }
    }
    else
    {
        iter.moveLeft();
        stck[0] = s_push_front_ne_rec(lflavor, iter, v);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
        ((BSQListTreeRepr*)res)->l = stck[0];
        ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
        ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
    }

    GCStack::popFrame(sizeof(void*));
    return res;
}

void* BSQListOps::s_push_front_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, StorageLocationPtr v)
{
    BSQListSpineIterator iter(ttype, t);
    return s_push_front_ne_rec(lflavor, iter, v);
}

void* s_remove_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, BSQNat i)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);

    void** stck = (void**)GCStack::allocFrame(sizeof(void*));
    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto pvsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        auto pvalloc = (pvsize - 1) <= 4 ? lflavor.pv4type : lflavor.pv8type;
        
        res = Allocator::GlobalAllocator.allocateDynamic(pvalloc);
        BSQPartialVectorType::removePVData(res, iter.lcurr, i, pvsize, pvalloc->entrysize);
    }
    else
    {
        auto trepr = static_cast<BSQListTreeRepr*>(iter.lcurr);
        auto ll = trepr->l;
        auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, ll);
        auto llcount = lltype->getCount(ll);

        if(i < llcount)
        {
            iter.moveLeft();
            stck[0] = s_remove_ne_rec(lflavor, iter, i);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount - 1;
        }
        else
        {
            iter.moveRight();
            stck[0] = s_remove_ne_rec(lflavor, iter, i - llcount);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = static_cast<BSQListTreeRepr*>(iter.lcurr)->l;
            ((BSQListTreeRepr*)res)->r = stck[0];
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount - 1;
        }
    }

    GCStack::popFrame(sizeof(void*));
    return res;
}

void* BSQListOps::s_remove_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i)
{
    BSQListSpineIterator iter(ttype, t);
    return s_remove_ne_rec(lflavor, iter, i);
}

void BSQListOps::s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res)
{
    //TODO: support other types too
    assert(oftype->tid == BSQ_TYPE_ID_INT || oftype->tid == BSQ_TYPE_ID_NAT);

    if(oftype->tid == BSQ_TYPE_ID_INT)
    {
        auto ll = BSQListOps::s_range_ne_rec<BSQInt>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_INT)->second, SLPTR_LOAD_CONTENTS_AS(BSQInt, start), SLPTR_LOAD_CONTENTS_AS(BSQInt, count));
        LIST_STORE_RESULT_REPR(res, ll);
    }
    else
    {
        assert(oftype->tid == BSQ_TYPE_ID_NAT);

        auto ll = BSQListOps::s_range_ne_rec<BSQNat>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_NAT)->second, SLPTR_LOAD_CONTENTS_AS(BSQNat, start), SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
        LIST_STORE_RESULT_REPR(res, ll);
    }
}

void BSQListOps::s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res)
{
    auto ll = BSQListOps::s_fill_ne_rec(BSQListOps::g_flavormap.find(oftype->tid)->second, val, SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
    LIST_STORE_RESULT_REPR(res, ll);
}

void* BSQListOps::s_reverse_ne(const BSQListTypeFlavor& lflavor, void* reprnode)
{
    auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode));
    auto count = reprtype->getCount(reprnode);

    void* res = nullptr;
    if(reprtype->lkind == ListReprKind::PV4)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
        BSQPartialVectorType::setPVCount(res, (int16_t)count);
        for(int16_t i = 0; i < (int16_t)count; ++i)
        {
            lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), lflavor.pv4type->get(reprnode, (int16_t)(count - 1) - i));
        }
    }
    else if(count <= 8)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
        BSQPartialVectorType::setPVCount(res, (int16_t)count);
        for(int16_t i = 0; i < (int16_t)count; ++i)
        {
            lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), lflavor.pv4type->get(reprnode, (int16_t)(count - 1) - i));
        }
    }
    else
    {
        void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 3);
        stck[0] = reprnode;

        stck[1] = BSQListOps::s_reverse_ne(lflavor, ((BSQListTreeRepr*)stck[0])->l);
        stck[2] = BSQListOps::s_reverse_ne(lflavor, ((BSQListTreeRepr*)stck[0])->r);

        res = BSQListOps::list_append(lflavor, stck[2], stck[1]);
        GCStack::popFrame(sizeof(void*) * 3);
    }

    return res;
}

BSQNat BSQListOps::s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    BSQBool found = BSQFALSE;
    int64_t idx = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        uint8_t* tmpl = GCStack::allocFrame(lentrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {tmpl};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        while(iter.valid())
        {
            lentrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            idx++;
            iter.advance();
        }

        GCStack::popFrame(lentrytype->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    return (BSQInt)(found ? idx : -1);
}

BSQNat BSQListOps::s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    BSQBool found = BSQFALSE;
    int64_t idx = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        uint8_t* tmpl = GCStack::allocFrame(lentrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {tmpl, &idx};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        while(iter.valid())
        {
            lentrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            idx++;
            iter.advance();
        }

        GCStack::popFrame(lentrytype->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    return (BSQInt)(found ? idx : -1);
}

BSQNat BSQListOps::s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    BSQBool found = BSQFALSE;
    int64_t icount = ttype->getCount(t);
    int64_t idx = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        uint8_t* tmpl = GCStack::allocFrame(lentrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {tmpl};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        while(iter.valid())
        {
            lentrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            idx--;
            iter.advance();
        }

        GCStack::popFrame(lentrytype->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    return (BSQInt)idx;
}

BSQNat BSQListOps::s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    BSQBool found = BSQFALSE;
    int64_t icount = ttype->getCount(t);
    int64_t idx = icount - 1;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    {
        BSQNat idx = icount - 1;
        uint8_t* tmpl = GCStack::allocFrame(lentrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {tmpl, &idx};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        BSQBool found = BSQFALSE;
        while(iter.valid())
        {
            lentrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, &found);
            if(found)
            {
                break;
            }

            idx--;
            iter.advance();
        }

        GCStack::popFrame(lentrytype->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    return (BSQInt)idx;
}

void* BSQListOps::s_filter_pred_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        tmpl[0] = t;

        std::vector<StorageLocationPtr> lparams = {esl};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });
    
        rres = BSQListOps::list_tree_transform(lflavor, tmpl[0], [&](void* vv, const BSQPartialVectorType* reprtype) {
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
           
            std::bitset<8> mask;
            BSQBool found = BSQFALSE;
            int16_t fcount = 0;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, &found);

                mask.set(i, found);
                fcount += found;
            }
            lflavor.entrytype->clearValue(esl);

            void* pvinto = nullptr;
            if(fcount != 0)
            {
                pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((fcount <= 4) ? lflavor.pv4type : lflavor.pv8type);
                BSQPartialVectorType::packPVData(pvinto, tmpl[1], mask, lflavor.entrytype->allocinfo.inlinedatasize);
            }
            tmpl[1] = nullptr;
    
            return pvinto;
        });
    
        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
    }

    return rres;
}

void* BSQListOps::s_filter_pred_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        tmpl[0] = t;

        uint64_t idxarg = 0;
        std::vector<StorageLocationPtr> lparams = {esl, &idxarg};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        rres = BSQListOps::list_tree_transform_idx(lflavor, tmpl[0], 0, [&](void* vv, const BSQPartialVectorType* reprtype, uint64_t idx) {
            idxarg = idx;
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);

            std::bitset<8> mask;
            BSQBool found = BSQFALSE;
            int16_t fcount = 0;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, &found);
               
                mask.set(i, found);
                fcount += found;
                    
                idxarg++;
            }
            lflavor.entrytype->clearValue(esl);

            void* pvinto = nullptr;
            if(fcount != 0)
            {
                pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((fcount <= 4) ? lflavor.pv4type : lflavor.pv8type);
                BSQPartialVectorType::packPVData(pvinto, tmpl[1], mask, lflavor.entrytype->allocinfo.inlinedatasize);
            }
            tmpl[1] = nullptr;

            return pvinto;
        });

        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
    }

    return rres;
}
    
void* BSQListOps::s_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        tmpl[0] = t;

        std::vector<StorageLocationPtr> lparams = {esl};
        std::transform(fn->cargpos.cbegin(), fn->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        rres = BSQListOps::list_tree_transform(lflavor, tmpl[0], [&](void* vv, const BSQPartialVectorType* reprtype) {
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
   
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, resflavor.pv8type->get(pv8l, i));
            }
            lflavor.entrytype->clearValue(esl);

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? resflavor.pv4type : resflavor.pv8type);
            BSQPartialVectorType::directSetPVData(pvinto, pv8l, vcount, resflavor.entrytype->allocinfo.inlinedatasize);

            tmpl[1] = nullptr;
            GC_MEM_ZERO(pv8l, resflavor.pv8type->allocinfo.heapsize);

            return pvinto;
        });
    
        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
    }

    return rres;
}

void* BSQListOps::s_map_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize +  resflavor.pv8type->allocinfo.heapsize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        tmpl[0] = t;

        uint64_t idxarg = 0;
        std::vector<StorageLocationPtr> lparams = {esl, &idxarg};
        std::transform(fn->cargpos.cbegin(), fn->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        rres = BSQListOps::list_tree_transform_idx(lflavor, tmpl[0], 0, [&](void* vv, const BSQPartialVectorType* reprtype, uint64_t idx) {
            idxarg = idx;
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);

            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, resflavor.pv8type->get(pv8l, i));
            }
            lflavor.entrytype->clearValue(esl);

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? resflavor.pv4type : resflavor.pv8type);
            BSQPartialVectorType::directSetPVData(pvinto, pv8l, vcount, resflavor.entrytype->allocinfo.inlinedatasize);

            tmpl[1] = nullptr;
            GC_MEM_ZERO(pv8l, resflavor.pv8type->allocinfo.heapsize);

            return pvinto;
        });

        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
    }

    return rres;
}

void* s_map_sync_rec(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, BSQListForwardIterator& iter1, BSQListForwardIterator& iter2, const BSQPCode* fn, const BSQInvokeBodyDecl* icall, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor1.entrytype->allocinfo.inlinedatasize + lflavor2.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
    
    void* res = nullptr;
    if(count <= 8)
    {
        uint8_t* esl1 = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* esl2 = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor1.entrytype->allocinfo.inlinedatasize);
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor1.entrytype->allocinfo.inlinedatasize + lflavor2.entrytype->allocinfo.inlinedatasize);

        std::vector<StorageLocationPtr> lparams = {esl1, esl2};
        std::transform(fn->cargpos.cbegin(), fn->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        for(uint64_t i = 0; i < count; ++i)
        {
            lflavor1.entrytype->storeValue(esl1, iter1.getlocation());
            lflavor2.entrytype->storeValue(esl2, iter2.getlocation());
            ee.invoke(icall, lparams, resflavor.pv8type->get(pv8l, i));

            iter1.advance();
            iter2.advance();
        }
        lflavor1.entrytype->clearValue(esl1);
        lflavor2.entrytype->clearValue(esl2);

        res = (void*)Allocator::GlobalAllocator.allocateDynamic((count <= 4) ? resflavor.pv4type : resflavor.pv8type);
        BSQPartialVectorType::directSetPVData(res, pv8l, count, resflavor.entrytype->allocinfo.inlinedatasize);

        GC_MEM_ZERO(pv8l, resflavor.pv8type->allocinfo.heapsize);
    }
    else
    {
        auto lcount = count / 2;
        auto rcount = count - lcount;

        tmpl[0] = s_map_sync_rec(lflavor1, lflavor2, ee, lcount, iter1, iter2, fn, icall, params, resflavor);
        tmpl[1] = s_map_sync_rec(lflavor1, lflavor2, ee, rcount, iter1, iter2, fn, icall, params, resflavor);

        res = BSQListOps::list_append(resflavor, tmpl[1], tmpl[2]);
    }

    GCStack::popFrame((sizeof(void*) * 2) + lflavor1.entrytype->allocinfo.inlinedatasize + lflavor2.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
    return res;
}

void* BSQListOps::s_map_sync_ne(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, void* t1, const BSQListReprType* ttype1, void* t2, const BSQListReprType* ttype2, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    BSQListForwardIterator iter1(ttype1, t1);
    Allocator::GlobalAllocator.insertCollectionIter(&iter1);

    BSQListForwardIterator iter2(ttype2, t2);
    Allocator::GlobalAllocator.insertCollectionIter(&iter2);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* res = s_map_sync_rec(lflavor1, lflavor2, ee, count, iter1, iter2, fn, icall, params, resflavor);

    Allocator::GlobalAllocator.removeCollectionIter(&iter2);
    Allocator::GlobalAllocator.removeCollectionIter(&iter1);
    
    return res;
}

void BSQListOps::s_reduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res)
{
    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);

    {
        uint8_t* tmpl = (uint8_t*)GCStack::allocFrame(lflavor.entrytype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
        uint8_t* resl = (tmpl + lflavor.entrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {resl, tmpl};
        std::transform(f->cargpos.cbegin(), f->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        }); 

        iter.advance(); //first element is always setup in the reduce value before calling this
        while(iter.valid())
        {
            icall->resultType->storeValue(resl, res);
            lflavor.entrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, res);

            iter.advance();
        }

        GCStack::popFrame(lflavor.entrytype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
}

void BSQListOps::s_reduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res)
{
    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);

    {
        uint64_t idxarg = 0;
        uint8_t* tmpl = (uint8_t*)GCStack::allocFrame(lflavor.entrytype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
        uint8_t* resl = (tmpl + lflavor.entrytype->allocinfo.inlinedatasize);
        std::vector<StorageLocationPtr> lparams = {resl, tmpl, &idxarg};
        std::transform(f->cargpos.cbegin(), f->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        }); 

        while(iter.valid())
        {
            icall->resultType->storeValue(resl, res);
            lflavor.entrytype->storeValue(tmpl, iter.getlocation());
            ee.invoke(icall, lparams, res);

            iter.advance();
            idxarg++;
        }

        GCStack::popFrame(lflavor.entrytype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
    }

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
}

void BSQListOps::s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);
    const BSQEphemeralListType* pcrtype = dynamic_cast<const BSQEphemeralListType*>(icall->resultType);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize + uflavor.pv8type->allocinfo.heapsize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* envsl = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        uint8_t* outsl = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize);
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
        tmpl[0] = t;

        std::vector<StorageLocationPtr> lparams = {esl, envsl};
        std::transform(f->cargpos.cbegin(), f->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });
        envtype->storeValue(envsl, params[1]);

        rres = BSQListOps::list_tree_transform(lflavor, tmpl[0], [&](void* vv, const BSQPartialVectorType* reprtype) {
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, outsl);

                envtype->storeValue(envsl, pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[0]));
                uflavor.entrytype->storeValue(uflavor.pv8type->get(pv8l, i), pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[1]));
            }
            lflavor.entrytype->clearValue(esl);
            pcrtype->clearValue(outsl);

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? uflavor.pv4type : uflavor.pv8type);
            BSQPartialVectorType::directSetPVData(pvinto, pv8l, vcount, uflavor.entrytype->allocinfo.inlinedatasize);

            tmpl[1] = nullptr;
            GC_MEM_ZERO(pv8l, uflavor.pv8type->allocinfo.heapsize);

            return pvinto;
        });
    
        envtype->storeValue(rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[0]), envsl);
        LIST_STORE_RESULT_REPR(rres, rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[1]));

        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize + uflavor.pv8type->allocinfo.heapsize);
    }
}

void BSQListOps::s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[f->code]);
    const BSQEphemeralListType* pcrtype = dynamic_cast<const BSQEphemeralListType*>(icall->resultType);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize + uflavor.pv8type->allocinfo.heapsize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* envsl = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        uint8_t* outsl = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize);
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize);
        tmpl[0] = t;

        uint64_t idxarg = 0;
        std::vector<StorageLocationPtr> lparams = {esl, envsl, &idxarg};
        std::transform(f->cargpos.cbegin(), f->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });
        envtype->storeValue(envsl, params[1]);

        rres = BSQListOps::list_tree_transform(lflavor, tmpl[0], [&](void* vv, const BSQPartialVectorType* reprtype, uint64_t idx) {
            idxarg = idx;
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, outsl);

                envtype->storeValue(envsl, pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[0]));
                uflavor.entrytype->storeValue(uflavor.pv8type->get(pv8l, i), pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[1]));
            }
            lflavor.entrytype->clearValue(esl);
            pcrtype->clearValue(outsl);

            void* pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((vcount <= 4) ? uflavor.pv4type : uflavor.pv8type);
            BSQPartialVectorType::directSetPVData(pvinto, pv8l, vcount, uflavor.entrytype->allocinfo.inlinedatasize);

            tmpl[1] = nullptr;
            GC_MEM_ZERO(pv8l, uflavor.pv8type->allocinfo.heapsize);

            return pvinto;
        });
    
        envtype->storeValue(rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[0]), envsl);
        LIST_STORE_RESULT_REPR(rres, rrtype->indexStorageLocationOffset(eres, rrtype->idxoffsets[1]));

        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + envtype->allocinfo.inlinedatasize + icall->resultType->allocinfo.inlinedatasize + uflavor.pv8type->allocinfo.heapsize);
    }
}

void* BSQListOps::s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params)
{
    //TODO: implement
    assert(false);
    return nullptr;
}

void* BSQListOps::s_unique_from_sorted_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* eq, const std::vector<StorageLocationPtr>& params)
{
    //TODO: implement
    assert(false);
    return nullptr;
}

std::map<std::pair<BSQTypeID, BSQTypeID>, BSQMapTypeFlavor> BSQMapOps::g_flavormap;

void* BSQMapOps::s_lookup_ne(void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, const BSQType* ktype)
{
    BSQMapTreeRepr* curr = static_cast<BSQMapTreeRepr*>(t);
    while(curr != nullptr)
    {
        auto ck = ttype->getKeyLocation(curr);
        if(ktype->fpkeycmp(ktype, kl, ck) < 0)
        {
            curr = static_cast<BSQMapTreeRepr*>(curr->l);
        }
        else if(ktype->fpkeycmp(ktype, ck, kl) < 0)
        {
            curr = static_cast<BSQMapTreeRepr*>(curr->r);
        }
        else
        {
            return curr;
        }
    }

    return nullptr;
}

void* s_add_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl)
{
    void* res = nullptr;

    if(iter.lcurr == nullptr)
    {
        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLeaf(res, kl, mflavor.keytype, vl, mflavor.valuetype);
    }
    else
    {
        void** stck = (void**)GCStack::allocFrame(sizeof(void*));

        auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
        if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck) < 0)
        {
            iter.moveLeft();
            stck[0] = s_add_ne_rec(mflavor, iter, kl, vl);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));
        }
        else
        {
            BSQ_INTERNAL_ASSERT(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0);

            iter.moveRight();
            stck[0] = s_add_ne_rec(mflavor, iter, kl, vl);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), stck[0]);
        }

        GCStack::popFrame(sizeof(void*));
    }

    return res;
}

void* BSQMapOps::s_add_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    void* res = s_add_ne_rec(mflavor, iter, kl, vl);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    return res;
}

void* s_set_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    void* res = nullptr;
    void** stck = (void**)GCStack::allocFrame(sizeof(void*));

    auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck) < 0)
    {
        iter.moveLeft();
        stck[0] = s_add_ne_rec(mflavor, iter, kl, vl);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0)
    {
        iter.moveRight();
        stck[0] = s_add_ne_rec(mflavor, iter, kl, vl);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), stck[0]);
    }
    else
    {
        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, kl, mflavor.keytype, vl, mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), BSQMapTreeType::getRight(iter.lcurr));
    }

    GCStack::popFrame(sizeof(void*));
    return res;
}

void* BSQMapOps::s_set_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    void* res = s_set_ne_rec(mflavor, iter, kl, vl);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    return res;
}

std::pair<void*, void*> s_remove_rotate_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl)
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
        xxxx;
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
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck) < 0)
    {
        iter.moveLeft();
        void* ll = s_remove_find_ne_rec(mflavor, iter, kl, nalloc);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateSafe(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, ll, BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0)
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
    SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(tnode, tmpr);

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

xxxx;
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

std::string entityPartialVectorDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    auto pvtype = dynamic_cast<const BSQPartialVectorType*>(btype);
    auto lflavor = BSQListOps::g_flavormap.find(pvtype->entrytype)->second;
    auto lv = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(data);

    size_t count = BSQPartialVectorType::getPVCount(lv);
    std::string res = pvtype->name + "{";
    for(size_t i = 0; i < count; ++i)
    {
        if(i != 0)
        {
            res += ", ";
        }
        res += lflavor.entrytype->fpDisplay(lflavor.entrytype, pvtype->get(lv, i), mode);
    }
    res += "}";

    return res;
}

std::string entityListTreeDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    return "[ListTree]";
}

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{    
    if(LIST_LOAD_TYPE_INFO(data)->tid == BSQ_TYPE_ID_NONE)
    {
        return btype->name + "{}";
    }
    else
    {
        PROCESS_DISPLAY_MODE(btype, mode, data);

        auto ltype = dynamic_cast<const BSQListType*>(btype);
        auto lflavor = BSQListOps::g_flavormap.find(ltype->etype)->second;

        std::string res = btype->name + "{";
        BSQListForwardIterator iter(LIST_LOAD_TYPE_INFO(data), LIST_LOAD_DATA(data));
        bool first = true;
        while(iter.valid())
        {
            if(!first)
            {
                res += ", ";
            }
            first = false;

            res += lflavor.entrytype->fpDisplay(lflavor.entrytype, iter.getlocation(), mode);
            iter.advance();
        }
        res += "}";

        return res;
    }
}

std::string entityMapDisplay_impl_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, DisplayMode mode)
{
    if(iter.lcurr == nullptr)
    {
        return "";
    }
    else
    {
        iter.moveLeft();
        auto ll = entityMapDisplay_impl_rec(mflavor, iter, mode);
        iter.pop();

        auto iistr = mflavor.keytype->fpDisplay(mflavor.keytype, mflavor.treetype->getKeyLocation(iter.lcurr), mode) + " => " + mflavor.valuetype->fpDisplay(mflavor.valuetype, mflavor.treetype->getValueLocation(iter.lcurr), mode);

        iter.moveRight();
        auto rr = entityMapDisplay_impl_rec(mflavor, iter, mode);
        iter.pop();

        return ll + (ll.empty() ? "" : ", ") + iistr + (rr.empty() ? "" : ", ") + rr;
    }
}

std::string entityMapDisplay_impl(const BSQType* btype, StorageLocationPtr data, DisplayMode mode)
{
    if(MAP_LOAD_TYPE_INFO(data)->tid == BSQ_TYPE_ID_NONE)
    {
        return btype->name + "{}";
    }
    else
    {
        PROCESS_DISPLAY_MODE(btype, mode, data);

        auto mtype = dynamic_cast<const BSQMapType*>(btype);
        auto mflavor = BSQMapOps::g_flavormap.find(std::make_pair(mtype->ktype, mtype->vtype))->second;

        std::string res = btype->name + "{";
        BSQMapSpineIterator iter(MAP_LOAD_TYPE_INFO(data), MAP_LOAD_REPR(data));
        if(iter.valid())
        {
            res += entityMapDisplay_impl_rec(mflavor, iter, mode);
        }
        res += "}";

        return res;
    }
}