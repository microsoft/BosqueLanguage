//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "collection_eval.h"

std::map<BSQTypeID, BSQListTypeFlavor> BSQListOps::g_flavormap;

void* s_set_list_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, BSQNat i, StorageLocationPtr v)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);

    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto pvsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        auto pvalloc = pvsize <= 4 ? lflavor.pv4type : lflavor.pv8type;
        
        res = Allocator::GlobalAllocator.allocateDynamic(pvalloc);
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
            stck[0] = s_set_list_ne_rec(lflavor, iter, i, v);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount;
        }
        else
        {
            iter.moveRight();
            stck[0] = s_set_list_ne_rec(lflavor, iter, i - llcount, v);
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
    return s_set_list_ne_rec(lflavor, iter, i, v);
}

void* s_push_back_list_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, StorageLocationPtr v)
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
            auto pvalloc = pvsize < 4 ? lflavor.pv4type : lflavor.pv8type;
        
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
        stck[0] = s_push_back_list_ne_rec(lflavor, iter, v);
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
    return s_push_back_list_ne_rec(lflavor, iter, v);
}

void* s_push_front_list_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, StorageLocationPtr v)
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
            auto pvalloc = pvsize < 4 ? lflavor.pv4type : lflavor.pv8type;
        
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
        stck[0] = s_push_front_list_ne_rec(lflavor, iter, v);
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
    return s_push_front_list_ne_rec(lflavor, iter, v);
}

void* s_remove_list_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, BSQNat i)
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
            stck[0] = s_remove_list_ne_rec(lflavor, iter, i);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount - 1;
        }
        else
        {
            iter.moveRight();
            stck[0] = s_remove_list_ne_rec(lflavor, iter, i - llcount);
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
    return s_remove_list_ne_rec(lflavor, iter, i);
}

void* s_insert_list_ne_rec(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, BSQNat i, StorageLocationPtr v)
{
    auto ttype = GET_TYPE_META_DATA_AS(BSQListReprType, iter.lcurr);
    void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);
        
    void* res = nullptr;
    if(ttype->lkind != ListReprKind::TreeElement)
    {
        auto vsize = BSQPartialVectorType::getPVCount(iter.lcurr);
        if(vsize < 8)
        {
            auto pvalloc = (vsize + 1) <= 4 ? lflavor.pv4type : lflavor.pv8type;
            res = Allocator::GlobalAllocator.allocateDynamic(pvalloc);

            BSQPartialVectorType::initializePVDataInsert(res, iter.lcurr, i, v, 0, vsize, ((BSQPartialVectorType*)ttype)->entrysize);
        }
        else
        {
            if(i < 4)
            {
                stck[0] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
                stck[1] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);

                BSQPartialVectorType::initializePVDataInsert(stck[0], iter.lcurr, i, v, 0, 4, ((BSQPartialVectorType*)ttype)->entrysize);
                BSQPartialVectorType::initializePVDataInsert(stck[1], iter.lcurr, vsize + 1, v, 4, vsize - 4, ((BSQPartialVectorType*)ttype)->entrysize);
            }
            else
            {
                stck[0] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
                stck[1] = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);

                BSQPartialVectorType::initializePVDataInsert(stck[0], iter.lcurr, vsize + 1, v, 0, 4, ((BSQPartialVectorType*)ttype)->entrysize);
                BSQPartialVectorType::initializePVDataInsert(stck[1], iter.lcurr, vsize + 1, v, 4, vsize - 4, ((BSQPartialVectorType*)ttype)->entrysize);
            }

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = stck[1];
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
        }
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
            stck[0] = s_insert_list_ne_rec(lflavor, iter, i, v);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = static_cast<BSQListTreeRepr*>(iter.lcurr)->r;
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
        }
        else
        {
            iter.moveRight();
            stck[0] = s_insert_list_ne_rec(lflavor, iter, i - llcount, v);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = static_cast<BSQListTreeRepr*>(iter.lcurr)->l;
            ((BSQListTreeRepr*)res)->r = stck[0];
            ((BSQListTreeRepr*)res)->lcount = static_cast<BSQListTreeRepr*>(iter.lcurr)->lcount + 1;
        }
    }
    GCStack::popFrame(sizeof(void*) * 2);

    return res;
}

void* BSQListOps::s_insert_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i, StorageLocationPtr v)
{
    BSQListSpineIterator iter(ttype, t);
    return s_insert_list_ne_rec(lflavor, iter, i, v);
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

BSQInt BSQListOps::s_find_value_ne(void* t, const BSQListReprType* ttype, StorageLocationPtr v)
{
    BSQBool found = BSQFALSE;
    int64_t idx = 0;

    BSQListForwardIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    {
        while(iter.valid())
        {
            auto found = lentrytype->fpkeycmp(lentrytype, iter.getlocation(), v);
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

BSQInt BSQListOps::s_find_value_last_ne(void* t, const BSQListReprType* ttype, StorageLocationPtr v)
{
    BSQBool found = BSQFALSE;
    int64_t idx = 0;

    BSQListReverseIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    const BSQType* lentrytype = BSQType::g_typetable[ttype->entrytype];
    {
        while(iter.valid())
        {
            auto found = lentrytype->fpkeycmp(lentrytype, iter.getlocation(), v);
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

BSQInt BSQListOps::s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
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

BSQInt BSQListOps::s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
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

BSQInt BSQListOps::s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
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

BSQInt BSQListOps::s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
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

                idxarg++;
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

void* s_map_sync_list_rec(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, BSQListForwardIterator& iter1, BSQListForwardIterator& iter2, const BSQPCode* fn, const BSQInvokeBodyDecl* icall, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
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

        tmpl[0] = s_map_sync_list_rec(lflavor1, lflavor2, ee, lcount, iter1, iter2, fn, icall, params, resflavor);
        tmpl[1] = s_map_sync_list_rec(lflavor1, lflavor2, ee, rcount, iter1, iter2, fn, icall, params, resflavor);

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

    void* res = s_map_sync_list_rec(lflavor1, lflavor2, ee, count, iter1, iter2, fn, icall, params, resflavor);

    Allocator::GlobalAllocator.removeCollectionIter(&iter2);
    Allocator::GlobalAllocator.removeCollectionIter(&iter1);
    
    return res;
}

void* BSQListOps::s_filter_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const BSQPCode* p, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);
    const BSQInvokeBodyDecl* pcall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[p->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
        uint8_t* esl = ((uint8_t*)tmpl + (sizeof(void*) * 2));
        uint8_t* pv8l = ((uint8_t*)tmpl + (sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize);
        tmpl[0] = t;

        std::vector<StorageLocationPtr> plparams = {esl};
        std::transform(p->cargpos.cbegin(), p->cargpos.cend(), std::back_inserter(plparams), [&params](uint32_t pos) {
            return params[pos];
        });

        std::vector<StorageLocationPtr> ilparams = {esl};
        std::transform(fn->cargpos.cbegin(), fn->cargpos.cend(), std::back_inserter(ilparams), [&params](uint32_t pos) {
            return params[pos];
        });

        rres = BSQListOps::list_tree_transform(lflavor, tmpl[0], [&](void* vv, const BSQPartialVectorType* reprtype) {
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
   
            size_t j = 0;
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                
                BSQBool found = BSQFALSE;
                ee.invoke(pcall, plparams, &found);
                if(found)
                {
                    ee.invoke(icall, ilparams, resflavor.pv8type->get(pv8l, j));
                    j++;
                }
            }
            lflavor.entrytype->clearValue(esl);

            void* pvinto = nullptr;
            if(j != 0)
            {
                pvinto = (void*)Allocator::GlobalAllocator.allocateDynamic((j <= 4) ? resflavor.pv4type : resflavor.pv8type);
                BSQPartialVectorType::directSetPVData(pvinto, pv8l, j, resflavor.entrytype->allocinfo.inlinedatasize);

                tmpl[1] = nullptr;
                GC_MEM_ZERO(pv8l, resflavor.pv8type->allocinfo.heapsize);
            }

            return pvinto;
        });
    
        GCStack::popFrame((sizeof(void*) * 2) + lflavor.entrytype->allocinfo.inlinedatasize + resflavor.pv8type->allocinfo.heapsize);
    }

    return rres;
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

        rres = BSQListOps::list_tree_transform_idx(lflavor, tmpl[0], 0, [&](void* vv, const BSQPartialVectorType* reprtype, uint64_t idx) {
            idxarg = idx;
            tmpl[1] = vv;
            int16_t vcount = reprtype->getPVCount(tmpl[1]);
        
            for(int16_t i = 0; i < vcount; ++i)
            {
                lflavor.entrytype->storeValue(esl, reprtype->get(tmpl[1], i));
                ee.invoke(icall, lparams, outsl);

                envtype->storeValue(envsl, pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[0]));
                uflavor.entrytype->storeValue(uflavor.pv8type->get(pv8l, i), pcrtype->indexStorageLocationOffset(outsl, pcrtype->idxoffsets[1]));

                idxarg++;
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

void* s_add_map_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl)
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
            stck[0] = s_add_map_ne_rec(mflavor, iter, kl, vl);
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));
        }
        else
        {
            BSQ_INTERNAL_ASSERT(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0);

            iter.moveRight();
            stck[0] = s_add_map_ne_rec(mflavor, iter, kl, vl);
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

    void* res = s_add_map_ne_rec(mflavor, iter, kl, vl);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    return res;
}

void* s_set_map_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl, StorageLocationPtr vl)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    void* res = nullptr;
    void** stck = (void**)GCStack::allocFrame(sizeof(void*));

    auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck) < 0)
    {
        iter.moveLeft();
        stck[0] = s_set_map_ne_rec(mflavor, iter, kl, vl);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0)
    {
        iter.moveRight();
        stck[0] = s_set_map_ne_rec(mflavor, iter, kl, vl);
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

    void* res = s_set_map_ne_rec(mflavor, iter, kl, vl);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    return res;
}

void* s_remove_find_map_ne_rec(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, StorageLocationPtr kl)
{
    BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

    void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);
    void* res = nullptr;

    auto ck = mflavor.treetype->getKeyLocation(iter.lcurr);
    if(mflavor.keytype->fpkeycmp(mflavor.keytype, kl, ck) < 0)
    {
        iter.moveLeft();
        stck[0] = s_remove_find_map_ne_rec(mflavor, iter, kl);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));
    }
    else if(mflavor.keytype->fpkeycmp(mflavor.keytype, ck, kl) < 0)
    {
        iter.moveRight();
        stck[0] = s_remove_find_map_ne_rec(mflavor, iter, kl);
        iter.pop();

        res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), stck[0]);
    }
    else
    {
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
            auto tnp = BSQMapOps::extract_min_and_remaining_tree(mflavor, iter);
            stck[0] = tnp.first;
            stck[1] = tnp.second;
            iter.pop();

            res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(stck[1]), mflavor.keytype, mflavor.treetype->getValueLocation(stck[1]), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), stck[0]);
        }
    }

    GCStack::popFrame(sizeof(void*) * 2);
    return res;
}

void* BSQMapOps::s_remove_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    void* res = s_remove_find_map_ne_rec(mflavor, iter, kl);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    return res;
}

void* BSQMapOps::s_fast_union_ne(const BSQMapTypeFlavor& mflavor, void* t1, const BSQMapTreeType* ttype1, void* t2, const BSQMapTreeType* ttype2)
{
    void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);
    void* res = nullptr;

    BSQMapSpineIterator iter(ttype2, t2);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    auto tnp = BSQMapOps::extract_min_and_remaining_tree(mflavor, iter);
    stck[0] = tnp.first;
    stck[1] = tnp.second;
    
    res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
    mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(stck[0]), mflavor.keytype, mflavor.treetype->getValueLocation(stck[0]), mflavor.valuetype, t1, stck[1]);

    Allocator::GlobalAllocator.removeCollectionIter(&iter);
    GCStack::popFrame(sizeof(void*) * 2);
    return res;
}

void* BSQMapOps::s_submap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params)
{
    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);

    void* res = nullptr;

    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[pred->code]);
    {
        void** tmpl = (void**)GCStack::allocFrame(mflavor.keytype->allocinfo.inlinedatasize + mflavor.valuetype->allocinfo.heapsize);
        uint8_t* ksl = (uint8_t*)tmpl;
        uint8_t* vsl = (uint8_t*)tmpl + mflavor.keytype->allocinfo.inlinedatasize;

        std::vector<StorageLocationPtr> lparams = {ksl, vsl};
        std::transform(pred->cargpos.cbegin(), pred->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        }); 

        res = BSQMapOps::map_tree_flatten(mflavor, iter, [&](StorageLocationPtr lk, StorageLocationPtr lv) { 
            mflavor.keytype->storeValue(ksl, lk);
            mflavor.valuetype->storeValue(vsl, lv);

            BSQBool bb = BSQFALSE;
            ee.invoke(icall, lparams, &bb);

            mflavor.keytype->clearValue(ksl);
            mflavor.valuetype->clearValue(vsl);
            return (bool)bb;
        });
    
        GCStack::popFrame(mflavor.keytype->allocinfo.inlinedatasize + mflavor.valuetype->allocinfo.heapsize);
    }
    
    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    return res;
}

void s_entries_rec_ne(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& ii, const BSQListTypeFlavor& lflavor, StorageLocationPtr tnode)
{
    if(BSQMapTreeType::getLeft(ii.lcurr) != nullptr)
    {
        ii.moveLeft();
        s_entries_rec_ne(mflavor, ii, lflavor, tnode);
        ii.pop();
    }
    
    auto mtype = GET_TYPE_META_DATA_AS(BSQMapTreeType, ii.lcurr);
    if(tnode == nullptr)
    {
        void** tmpl = (void**)GCStack::allocFrame(sizeof(void*) + lflavor.entrytype->allocinfo.inlinedatasize);
        void* data = nullptr;
        if(lflavor.entrytype->tkind != BSQTypeLayoutKind::Struct)
        {
            *tmpl = Allocator::GlobalAllocator.allocateDynamic(lflavor.entrytype);
            data = *tmpl;
        }
        else
        {
            data = tmpl + 1;
        }

        mflavor.keytype->storeValue(lflavor.entrytype->indexStorageLocationOffset(&data, 0), mtype->getKeyLocation(ii.lcurr));
        mflavor.valuetype->storeValue(lflavor.entrytype->indexStorageLocationOffset(&data, mflavor.keytype->allocinfo.inlinedatasize), mtype->getValueLocation(ii.lcurr));
        auto vv = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);

        BSQPartialVectorType::initializePVDataSingle(vv, data, lflavor.entrytype);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(tnode, vv);

        GCStack::popFrame(sizeof(void*) + lflavor.entrytype->allocinfo.inlinedatasize);
    }
    else 
    {
        auto tmpi = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(tnode);
        auto tmpr = BSQListOps::s_push_back_ne(lflavor, tmpi, GET_TYPE_META_DATA_AS(BSQListReprType, tmpi), tnode);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(tnode, tmpr);
    }

    if(BSQMapTreeType::getRight(ii.lcurr) != nullptr)
    {
        ii.moveRight();
        s_entries_rec_ne(mflavor, ii, lflavor, tnode);
        ii.pop();
    }
}

void* BSQMapOps::s_entries_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, const BSQListTypeFlavor& lflavor)
{
    void** stck = (void**)GCStack::allocFrame(sizeof(void*));
    stck[0] = t;

    BSQMapSpineIterator iter(ttype, t);
    Allocator::GlobalAllocator.insertCollectionIter(&iter);
    s_entries_rec_ne(mflavor, iter, lflavor, stck);
    Allocator::GlobalAllocator.removeCollectionIter(&iter);

    void* res = stck[0];
    GCStack::popFrame(sizeof(void*));

    return res;
}

void* BSQMapOps::s_remap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQMapTypeFlavor& resflavor)
{
    const BSQInvokeBodyDecl* icall = dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[fn->code]);

    void* rres = nullptr;
    {
        void** tmpl = (void**)GCStack::allocFrame((sizeof(void*) * 4) + mflavor.keytype->allocinfo.inlinedatasize + mflavor.valuetype->allocinfo.heapsize + icall->resultType->allocinfo.inlinedatasize);
        uint8_t* ksl = ((uint8_t*)tmpl + sizeof(void*) * 4);
        uint8_t* vsl = ((uint8_t*)tmpl + sizeof(void*) * 4 + mflavor.keytype->allocinfo.inlinedatasize);
        uint8_t* resl = ((uint8_t*)tmpl + sizeof(void*) * 4 + mflavor.keytype->allocinfo.inlinedatasize + mflavor.valuetype->allocinfo.heapsize);
        tmpl[0] = t;

        std::vector<StorageLocationPtr> lparams = {ksl, vsl};
        std::transform(fn->cargpos.cbegin(), fn->cargpos.cend(), std::back_inserter(lparams), [&params](uint32_t pos) {
            return params[pos];
        });

        rres = BSQMapOps::map_tree_transform(mflavor, tmpl[0], [&](void* vv, void* ll, void* rr) {
            tmpl[1] = vv;
            tmpl[2] = ll;
            tmpl[3] = rr;

            mflavor.keytype->storeValue(ksl, mflavor.treetype->getKeyLocation(tmpl[1]));
            mflavor.valuetype->storeValue(vsl, mflavor.treetype->getValueLocation(tmpl[1]));
            ee.invoke(icall, lparams, resl);

            mflavor.keytype->clearValue(ksl);
            mflavor.valuetype->clearValue(vsl);

            void* tinto = (void*)Allocator::GlobalAllocator.allocateDynamic(resflavor.treetype);
            resflavor.treetype->initializeLR(tinto, mflavor.treetype->getKeyLocation(tmpl[1]), mflavor.keytype, resl, resflavor.valuetype, tmpl[1], tmpl[2]);

            resflavor.valuetype->clearValue(resl);
            tmpl[1] = nullptr;
            tmpl[2] = nullptr;
            tmpl[3] = nullptr;
            
            return tinto;
        });
    
        GCStack::popFrame((sizeof(void*) * 4) + mflavor.keytype->allocinfo.inlinedatasize + mflavor.valuetype->allocinfo.heapsize + icall->resultType->allocinfo.inlinedatasize);
    }

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
    if(LIST_LOAD_DATA(data) == nullptr)
    {
        return btype->name + "{}";
    }
    else
    {
        auto ltype = dynamic_cast<const BSQListType*>(btype);
        auto lflavor = BSQListOps::g_flavormap.find(ltype->etype)->second;

        std::string res = btype->name + "{";
        BSQListForwardIterator iter(SLPTR_LOAD_HEAP_TYPE_AS(BSQListReprType, data), LIST_LOAD_DATA(data));
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
    if(MAP_LOAD_DATA(data) == nullptr)
    {
        return btype->name + "{}";
    }
    else
    {
        auto mtype = dynamic_cast<const BSQMapType*>(btype);
        auto mflavor = BSQMapOps::g_flavormap.find(std::make_pair(mtype->ktype, mtype->vtype))->second;

        BSQMapSpineIterator iter(SLPTR_LOAD_HEAP_TYPE_AS(BSQMapTreeType, data), MAP_LOAD_DATA(data));

        std::string res = btype->name + "{";
        res += entityMapDisplay_impl_rec(mflavor, iter, mode);
        res += "}";

        return res;
    }
}