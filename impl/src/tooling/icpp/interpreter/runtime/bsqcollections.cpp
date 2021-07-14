//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "./bsqcollections.h"
#include "./environment.h"

void registerIteratorGCRoots(BSQListReprIterator* iter)
{
    Allocator::GlobalAllocator.pushRoot(&(iter->lroot));
    Allocator::GlobalAllocator.pushRoot(&(iter->cbuff));
}

void releaseIteratorGCRoots()
{
    Allocator::GlobalAllocator.popRoots<2>();
}

bool iteratorIsValid(const BSQListReprIterator* iter)
{
    return iter->cbuff != nullptr;
}

void initializeListIterPosition(BSQListReprIterator* iter, int64_t pos)
{
    auto ssize = (int64_t)GET_TYPE_META_DATA_AS(BSQListReprType, iter->lroot)->getLength(iter->lroot);
    if((pos == ssize) | (ssize == 0))
    {
        iter->cbuff = nullptr;
    }
    else
    {
        GET_TYPE_META_DATA_AS(BSQListReprType, iter->lroot)->initializeIterPosition(iter, iter->lroot, pos);   
    }
}

void iteratorGetElement(const BSQListReprIterator* iter, void* into)
{
    iter->etype->storeValue(into, BSQListFlatKTypeAbstract::getDataBytes(iter->cbuff) + iter->cpos);
}

void incrementListIterator(BSQListReprIterator* iter)
{
    iter->lpos++;
    iter->cpos += iter->esize;
    
    if(iter->cpos == iter->maxpos)
    {
        initializeListIterPosition(iter, iter->lpos);
    }
}

std::string entityListReprDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    return "[ListRepr]";
}

void BSQListFlatKTypeAbstract::initializeIterPositionWSlice(BSQListReprIterator* iter, void* data, int64_t pos, int64_t maxpos) const
{
    iter->cbuff = data;
    iter->cpos = (int16_t)pos * iter->esize;
    iter->maxpos = (int16_t)maxpos * iter->esize;
}

uint64_t BSQListFlatKTypeAbstract::getLength(void* data) const
{
    return BSQListFlatKTypeAbstract::getElementCount(data);
}

void BSQListFlatKTypeAbstract::initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const
{
    iter->cbuff = data;
    iter->cpos = (int16_t)pos * iter->esize;
    iter->maxpos = (int16_t)BSQListFlatKTypeAbstract::getStorageBytesCount(data);
}

StorageLocationPtr BSQListFlatKTypeAbstract::getValueAtPosition(void* data, uint64_t pos, uint16_t esize) const
{
    return BSQListFlatKTypeAbstract::getDataBytes(data) + (pos * esize);
}

void* BSQListFlatKTypeAbstract::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == BSQListFlatKTypeAbstract::getElementCount(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);
  
    auto res = Allocator::GlobalAllocator.allocateDynamic(BSQListType::g_listTypeMap[this->tid].slice);
    ((BSQListSlice*)res)->lrepr = data;
    ((BSQListSlice*)res)->start = nstart;
    ((BSQListSlice*)res)->end = nend;

    Allocator::GlobalAllocator.popRoot();
    return data;
}

uint64_t BSQListSliceType::getLength(void* data) const
{
    auto sl = (BSQListSlice*)data;
    return sl->end - sl->start;
}

void BSQListSliceType::initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    kltype->initializeIterPositionWSlice(iter, sl->lrepr, pos + (int64_t)sl->start, (int64_t)sl->end);
}

StorageLocationPtr BSQListSliceType::getValueAtPosition(void* data, uint64_t pos, uint16_t esize) const 
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    return kltype->getValueAtPosition(sl->lrepr, pos + sl->start, esize);
}

void* BSQListSliceType::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->getLength(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);
      
    auto res = Allocator::GlobalAllocator.allocateDynamic(this);
    ((BSQListSlice*)res)->lrepr = ((BSQListSlice*)data)->lrepr;
    ((BSQListSlice*)res)->start = ((BSQListSlice*)data)->start + nstart;
    ((BSQListSlice*)res)->end = ((BSQListSlice*)data)->end - nend;

    Allocator::GlobalAllocator.popRoot();
    return data;
}

uint64_t BSQListConcatType::getLength(void* data) const
{
    auto cl = (BSQListConcat*)data;
    return cl->size;
}

void BSQListConcatType::initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const
{
    auto cl = (BSQListConcat*)data;
    auto l1size = (int64_t)cl->size;
    if(pos < l1size)
    {
        auto l1type = GET_TYPE_META_DATA_AS(BSQListReprType, cl->lrepr1);
        l1type->initializeIterPosition(iter, cl->lrepr1, pos);
    }
    else
    {
        auto l2type = GET_TYPE_META_DATA_AS(BSQListReprType, cl->lrepr2);
        l2type->initializeIterPosition(iter, cl->lrepr2, pos - l1size);
    }
}

StorageLocationPtr BSQListConcatType::getValueAtPosition(void* data, uint64_t pos, uint16_t esize) const 
{
    auto cl = (BSQListConcat*)data;

    auto l1size = (int64_t)cl->size;
    if((int64_t)pos < l1size)
    {
        auto l1type = GET_TYPE_META_DATA_AS(BSQListReprType, cl->lrepr1);
        return l1type->getValueAtPosition(cl->lrepr1, pos, esize);
    }
    else
    {
        auto l2type = GET_TYPE_META_DATA_AS(BSQListReprType, cl->lrepr2);
        return l2type->getValueAtPosition(cl->lrepr2, pos - l1size, esize);
    }
}

void* BSQListConcatType::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->getLength(data)))
    {
        return data;
    }

    auto l1type = GET_TYPE_META_DATA_AS(BSQListReprType, ((BSQListConcat*)data)->lrepr1);
    auto l2type = GET_TYPE_META_DATA_AS(BSQListReprType, ((BSQListConcat*)data)->lrepr2);

    Allocator::GlobalAllocator.pushRoot(&data);
        
    void* res = nullptr;
    auto l1size = l1type->getLength(((BSQListConcat*)data)->lrepr1);
    if(nend <= l1size)
    {
        res = l1type->slice_impl(((BSQListConcat*)data)->lrepr1, nstart, nend);
    }
    else if(l1size <= nstart)
    {
        res = l2type->slice_impl(((BSQListConcat*)data)->lrepr2, nstart - l1size, nend - l1size);
    }
    else
    {
        res = Allocator::GlobalAllocator.allocateDynamic(this);
        Allocator::GlobalAllocator.pushRoot(&res);

        ((BSQListConcat*)res)->lrepr1 = l1type->slice_impl(((BSQListConcat*)data)->lrepr1, nstart, l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->lrepr2 = l2type->slice_impl(((BSQListConcat*)data)->lrepr2, 0, nend - l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->size = nend - nstart;

        Allocator::GlobalAllocator.popRoot(); 
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}


std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQList l = SLPTR_LOAD_CONTENTS_AS(BSQList, data);

    if(l.size == 0)
    {
        return btype->name + "@{}";
    }
    else
    {

        BSQListReprIterator iter;
        dynamic_cast<const BSQListType*>(btype)->initializeIteratorBegin(&iter, data);

        auto etype = BSQType::g_typetable[dynamic_cast<const BSQListType*>(btype)->etype];
        void* estack = BSQ_STACK_SPACE_ALLOC(etype->allocinfo.inlinedatasize);
        etype->clearValue(estack);

        std::string ll = btype->name + "@{";

        registerIteratorGCRoots(&iter);
        GCStack::pushFrame(&estack, etype->allocinfo.inlinedmask);

        while(iteratorIsValid(&iter))
        {
            iteratorGetElement(&iter, estack);
            ll += etype->fpDisplay(etype, estack);
        }

        GCStack::popFrame();
        releaseIteratorGCRoots();

        ll += "}";
        return ll;
    }
}

bool entityListParse_impl(const BSQType* btype, json j, StorageLocationPtr sl)
{
    if(!j.is_array())
    {
        return false;
    }
    
    auto ltype = dynamic_cast<const BSQListType*>(btype);
    auto etype = BSQType::g_typetable[ltype->etype];
    const ListTypeConstructorInfo& glistalloc = BSQListType::g_listTypeMap[ltype->tid];

    auto vbuff = BSQ_STACK_SPACE_ALLOC(etype->allocinfo.inlinedatasize);

    //
    //TODO: we need to handle this
    //
    assert(j.size() <= 40);

    auto ct = j.size();
    if(ct == 0)
    {
        ltype->storeValue(sl, (StorageLocationPtr)&bsqemptylist);
    }
    else
    {
        const BSQListFlatKTypeAbstract* fltype = std::find_if(glistalloc.kcons, glistalloc.kcons + sizeof(glistalloc.kcons), [ct](const std::pair<size_t, BSQListFlatKTypeAbstract*>& pp) {
            return ct <= pp.first;
        })->second;

        auto tt = Allocator::GlobalAllocator.allocateDynamic(fltype);
        fltype->initializeCountInfo(tt, ct, ltype->esize);
        Allocator::GlobalAllocator.pushRoot(&tt);

        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(sl, tt);
        for (size_t i = 0; i < j.size(); ++i)
        {
            etype->consops.fpJSONParse(etype, j[i], &vbuff);
            etype->storeValue(SLPTR_INDEX_DATAPTR(fltype->getDataBytes(tt), i * ltype->esize), &vbuff);
        }

        BSQList ll = {tt, j.size()};
        ltype->storeValue(sl, &ll);

        Allocator::GlobalAllocator.popRoot();
    }

    return true;
}

std::map<BSQTypeID, ListTypeConstructorInfo> BSQListType::g_listTypeMap;

void BSQListType::initializeIteratorGivenPosition(BSQListReprIterator* iter, StorageLocationPtr sl, int64_t pos) const
{
    BSQList l = SLPTR_LOAD_CONTENTS_AS(BSQList, sl);

    iter->cbuff = nullptr;
    iter->cpos = 0;
    iter->maxpos = 0;

    iter->lroot = l.repr;
    iter->lpos = 0;

    iter->etype = BSQType::g_typetable[this->etype];
    iter->esize = this->esize; 

    if(l.size != 0)
    {
        initializeListIterPosition(iter, pos);
    }
}

void BSQListType::initializeIteratorBegin(BSQListReprIterator* iter, StorageLocationPtr sl) const
{
    BSQListType::initializeIteratorGivenPosition(iter, sl, 0);
}

StorageLocationPtr BSQListType::getValueAtPosition(StorageLocationPtr sl, uint64_t pos) const
{
    BSQList l = SLPTR_LOAD_CONTENTS_AS(BSQList, sl);
    assert(pos < l.size);

    auto ltype = GET_TYPE_META_DATA_AS(BSQListReprType, l.repr);
    return ltype->getValueAtPosition(l.repr, pos, this->esize);
}

BSQList BSQListType::concat2(StorageLocationPtr s1, StorageLocationPtr s2) const
{
    //
    //TODO: want to rebalance here later
    //

    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQListFlatK<16>));

    BSQList l1 = SLPTR_LOAD_CONTENTS_AS(BSQList, s1);
    BSQList l2 = SLPTR_LOAD_CONTENTS_AS(BSQList, s2);

    if(BSQListType::empty(l1) & BSQListType::empty(l2))
    {
        return bsqemptylist;
    }
    else if(BSQListType::empty(l1))
    {
        return l2;
    }
    else if(BSQListType::empty(l2))
    {
        return l1;
    }
    else
    {
        void* res = nullptr;
        if(l1.size + l2.size <= 16)
        {
            res = Allocator::GlobalAllocator.allocateSafe(BSQListType::g_listTypeMap[this->tid].list16);
            BSQListType::g_listTypeMap[this->tid].list16->initializeCountInfo(res, l1.size + l2.size, this->esize);
            uint8_t* curr = BSQListFlatKTypeAbstract::getDataBytes(res);

            BSQListReprIterator iter1;
            initializeIteratorBegin(&iter1, s1);
            while(iteratorIsValid(&iter1))
            {
                iteratorGetElement(&iter1, curr);
                curr += this->esize;
                incrementListIterator(&iter1);
            }

            BSQListReprIterator iter2;
            initializeIteratorBegin(&iter2, s2);
            while(iteratorIsValid(&iter2))
            {
                iteratorGetElement(&iter2, curr);
                curr += this->esize;
                incrementListIterator(&iter2);
            }
        }
        else
        {
            res = (BSQListConcat*)Allocator::GlobalAllocator.allocateSafe(BSQListType::g_listTypeMap[this->tid].concat);
            ((BSQListConcat*)res)->size = l1.size + l2.size;
            ((BSQListConcat*)res)->lrepr1 = l1.repr;
            ((BSQListConcat*)res)->lrepr2 = l2.repr;
        }

        return BSQList{res, l1.size + l2.size};
    }
}

BSQList BSQListType::slice(StorageLocationPtr l, uint64_t startpos, uint64_t endpos) const
{
    //
    //TODO: want to rebalance here later
    //

    if(startpos >= endpos)
    {
        return bsqemptylist;
    }
    else
    {
        Allocator::GlobalAllocator.ensureSpace(sizeof(BSQListFlatK<16>));

        BSQList ll = SLPTR_LOAD_CONTENTS_AS(BSQList, l);
        void* res;

        auto dist = endpos - startpos;
        if(dist <= 16)
        {
            res = Allocator::GlobalAllocator.allocateSafe(BSQListType::g_listTypeMap[this->tid].list16);
            BSQListType::g_listTypeMap[this->tid].list16->initializeCountInfo(res, dist, this->esize);

            uint8_t* curr = BSQListFlatKTypeAbstract::getDataBytes(res);

            BSQListReprIterator iter;
            this->initializeIteratorGivenPosition(&iter, l, (int64_t)startpos);

            for(uint64_t i = 0; i < dist; ++i)
            {
                iteratorGetElement(&iter, curr);

                curr += this->esize;
                incrementListIterator(&iter);
            }
        }
        else
        {
            auto ltype = GET_TYPE_META_DATA_AS(BSQListReprType, ll.repr);
            res = ltype->slice_impl(ll.repr, startpos, endpos);
        }

        return BSQList{res, dist};
    }
}

void BSQListType::hasPredCheck(StorageLocationPtr l, StorageLocationPtr vv, StorageLocationPtr resultsl, const std::function<void(const std::vector<StorageLocationPtr>&, StorageLocationPtr)>& fn) const
{
    SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, BSQFALSE);

    if(!BSQListType::empty(SLPTR_LOAD_CONTENTS_AS(BSQList, l)))
    {
        BSQListReprIterator iter;
        this->initializeIteratorBegin(&iter, l);
        registerIteratorGCRoots(&iter);

        std::vector<StorageLocationPtr> argv = {vv};
        BSQBool rr = BSQFALSE;
        while(iteratorIsValid(&iter))
        {
            iteratorGetElement(&iter, vv);
            fn(argv, &rr);
            if(rr) {
                SLPTR_STORE_CONTENTS_AS(BSQBool, resultsl, BSQTRUE);
                break;
            }

            incrementListIterator(&iter);
        }

        releaseIteratorGCRoots();
    }
}
