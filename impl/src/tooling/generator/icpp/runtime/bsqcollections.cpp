//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "./bsqcollections.h"
#include "./environment.h"

void registerIteratorGCRoots(BSQListIterator* iter)
{
    Allocator::GlobalAllocator.pushRoot(&(iter->lroot));
    Allocator::GlobalAllocator.pushRoot(&(iter->cbuff));
}

void releaseIteratorGCRoots(BSQListIterator* iter)
{
    Allocator::GlobalAllocator.popRoots<2>();
}

bool iteratorIsValid(const BSQListIterator* iter)
{
    return iter->cbuff != nullptr;
}

StorageLocationPtr iteratorGetElement(const BSQListIterator* iter)
{
    return BSQListFlatKTypeAbstract::getDataBytes(iter->cbuff) + iter->cpos;
}

void incrementListIterator(BSQListIterator* iter)
{
    iter->lpos++;
    iter->cpos += iter->esize;
    
    if(iter->cbuff == nullptr || iter->cpos == iter->maxpos)
    {
        auto ltype = GET_TYPE_META_DATA_AS(BSQListEntityType, iter->lroot);
        ltype->initializeListIterPosition(iter, iter->lroot, iter->lpos);
    }
}

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQListIterator iter;
    xxxx;
    registerIteratorGCRoots(&iter);

    std::string ll = ((BSQListEntityType*)btype)->name + "@{";
    xxx; //interior pointer roots??
    while(iteratorIsValid(&iter))
    {

    }
}

void BSQListEmptyType::initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    //NOP
}

StorageLocationPtr BSQListEmptyType::getValueAtPosition(void* data, uint64_t pos) const
{
    assert(false);
    return nullptr;
}

void* BSQListEmptyType::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    assert((nstart == 0) & (nend == 0));
    return data;
}

uint64_t BSQListFlatKTypeAbstract::getLength(void* data) const
{
    return BSQListFlatKTypeAbstract::getElementCount(data);
}

void BSQListFlatKTypeAbstract::initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    iter->cbuff = data;
    iter->cpos = pos * this->esize;
    iter->maxpos = BSQListFlatKTypeAbstract::getStorageBytesCount(data);
}

StorageLocationPtr BSQListFlatKTypeAbstract::getValueAtPosition(void* data, uint64_t pos) const
{
    return BSQListFlatKTypeAbstract::getDataBytes(data) + (pos * this->esize);
}

void* BSQListFlatKTypeAbstract::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->getLength(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);
  
    auto res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeListSlice);
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

void BSQListSliceType::initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    kltype->initializeListIterPosition(iter, sl->lrepr, pos + sl->start);
}

StorageLocationPtr BSQListSliceType::getValueAtPosition(void* data, uint64_t pos) const 
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    return kltype->getValueAtPosition(sl->lrepr, pos + sl->start);
}

void* BSQListSliceType::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->getLength(data)))
    {
        return data;
    }

    Allocator::GlobalAllocator.pushRoot(&data);
      
    auto res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeListSlice);
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

void BSQListConcatType::initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    auto cl = (BSQListConcat*)data;
    auto l1size = (int64_t)cl->size;
    if(pos < l1size)
    {
        auto l1type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr1);
        l1type->initializeListIterPosition(iter, cl->lrepr1, pos);
    }
    else
    {
        auto l2type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr2);
        l2type->initializeListIterPosition(iter, cl->lrepr2, pos - l1size);
    }
}

StorageLocationPtr BSQListConcatType::getValueAtPosition(void* data, uint64_t pos) const 
{
    auto cl = (BSQListConcat*)data;

    auto l1size = (int64_t)cl->size;
    if(pos < l1size)
    {
        auto l1type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr1);
        l1type->getValueAtPosition(cl->lrepr1, pos);
    }
    else
    {
        auto l2type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr2);
        l2type->getValueAtPosition(cl->lrepr2, pos - l1size);
    }
}

void* BSQListConcatType::slice(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == this->getLength(data)))
    {
        return data;
    }

    auto l1type = GET_TYPE_META_DATA_AS(BSQListEntityType, ((BSQListConcat*)data)->lrepr1);
    auto l2type = GET_TYPE_META_DATA_AS(BSQListEntityType, ((BSQListConcat*)data)->lrepr2);

    Allocator::GlobalAllocator.pushRoot(&data);
        
    void* res = nullptr;
    auto l1size = l1type->getLength(((BSQListConcat*)data)->lrepr1);
    if(nend <= l1size)
    {
        res = l1type->slice(((BSQListConcat*)data)->lrepr1, nstart, nend);
    }
    else if(l1size <= nstart)
    {
        res = l2type->slice(((BSQListConcat*)data)->lrepr2, nstart - l1size, nend - l1size);
    }
    else
    {
        res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeListConcat);
        Allocator::GlobalAllocator.pushRoot(&res);

        ((BSQListConcat*)res)->lrepr1 = l1type->slice(((BSQListConcat*)data)->lrepr1, nstart, l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->lrepr2 = l2type->slice(((BSQListConcat*)data)->lrepr2, 0, nend - l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->size = nend - nstart;

        Allocator::GlobalAllocator.popRoot(); 
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}
