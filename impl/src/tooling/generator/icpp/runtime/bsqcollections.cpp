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

void releaseIteratorGCRoots()
{
    Allocator::GlobalAllocator.popRoots<2>();
}

bool iteratorIsValid(const BSQListIterator* iter)
{
    return iter->cbuff != nullptr;
}

void initializeListIterPosition(BSQListIterator* iter, int64_t pos)
{
    auto ssize = (int64_t)GET_TYPE_META_DATA_AS(BSQListEntityType, iter->lroot)->getLength(iter->lroot);
    if((pos == ssize) | (ssize == 0))
    {
        iter->cbuff = nullptr;
    }
    else
    {
        GET_TYPE_META_DATA_AS(BSQListEntityType, iter->lroot)->initializeIterPosition(iter, iter->lroot, pos);   
    }
}

void iteratorGetElement(const BSQListIterator* iter, void* into, const BSQType* etype)
{
    etype->storeValue(into, BSQListFlatKTypeAbstract::getDataBytes(iter->cbuff) + iter->cpos);
}

void incrementListIterator(BSQListIterator* iter)
{
    iter->lpos++;
    iter->cpos += iter->esize;
    
    if(iter->cpos == iter->maxpos)
    {
        initializeListIterPosition(iter, iter->lpos);
    }
}

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data)
{
    BSQListIterator iter;
    initializeListIterPosition(&iter, );
    registerIteratorGCRoots(&iter);

    auto etype = ((BSQListEntityType*)btype)->etype;
    void* estack = BSQ_STACK_SPACE_ALLOC(etype->allocinfo.slfullsize);
    etype->clearValue(estack);

    GCStack::pushFrame(nullptr, 0, &estack, etype->allocinfo.slmask);

    std::string ll = ((BSQListEntityType*)btype)->name + "@{";
    while(iteratorIsValid(&iter))
    {
        iteratorGetElement(&iter, estack, etype);
        ll += etype->fpDisplay(etype, estack);
    }

    GCStack::popFrame();
    releaseIteratorGCRoots();
}

void BSQListEmptyType::initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    //NOP
}

StorageLocationPtr BSQListEmptyType::getValueAtPosition(void* data, uint64_t pos) const
{
    assert(false);
    return nullptr;
}

void* BSQListEmptyType::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
{
    assert((nstart == 0) & (nend == 0));
    return data;
}

void BSQListFlatKTypeAbstract::initializeIterPositionWSlice(BSQListIterator* iter, void* data, int64_t pos, int64_t maxpos) const
{
    iter->cbuff = data;
    iter->cpos = pos * this->esize;
    iter->maxpos = maxpos * this->esize;
}

uint64_t BSQListFlatKTypeAbstract::getLength(void* data) const
{
    return BSQListFlatKTypeAbstract::getElementCount(data);
}

void BSQListFlatKTypeAbstract::initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    iter->cbuff = data;
    iter->cpos = pos * this->esize;
    iter->maxpos = BSQListFlatKTypeAbstract::getStorageBytesCount(data);
}

StorageLocationPtr BSQListFlatKTypeAbstract::getValueAtPosition(void* data, uint64_t pos) const
{
    return BSQListFlatKTypeAbstract::getDataBytes(data) + (pos * this->esize);
}

void* BSQListFlatKTypeAbstract::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
{
    if((nstart == 0) & (nend == BSQListFlatKTypeAbstract::getElementCount(data)))
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

void BSQListSliceType::initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    kltype->initializeIterPositionWSlice(iter, sl->lrepr, pos + sl->start, sl->end);
}

StorageLocationPtr BSQListSliceType::getValueAtPosition(void* data, uint64_t pos) const 
{
    auto sl = (BSQListSlice*)data;
    auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
    return kltype->getValueAtPosition(sl->lrepr, pos + sl->start);
}

void* BSQListSliceType::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
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

void BSQListConcatType::initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const
{
    auto cl = (BSQListConcat*)data;
    auto l1size = (int64_t)cl->size;
    if(pos < l1size)
    {
        auto l1type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr1);
        l1type->initializeIterPosition(iter, cl->lrepr1, pos);
    }
    else
    {
        auto l2type = GET_TYPE_META_DATA_AS(BSQListEntityType, cl->lrepr2);
        l2type->initializeIterPosition(iter, cl->lrepr2, pos - l1size);
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

void* BSQListConcatType::slice_impl(void* data, uint64_t nstart, uint64_t nend) const
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
        res = l1type->slice_impl(((BSQListConcat*)data)->lrepr1, nstart, nend);
    }
    else if(l1size <= nstart)
    {
        res = l2type->slice_impl(((BSQListConcat*)data)->lrepr2, nstart - l1size, nend - l1size);
    }
    else
    {
        res = Allocator::GlobalAllocator.allocateDynamic(Environment::g_typeListConcat);
        Allocator::GlobalAllocator.pushRoot(&res);

        ((BSQListConcat*)res)->lrepr1 = l1type->slice_impl(((BSQListConcat*)data)->lrepr1, nstart, l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->lrepr2 = l2type->slice_impl(((BSQListConcat*)data)->lrepr2, 0, nend - l1type->getLength(((BSQListConcat*)data)->lrepr1));
        ((BSQListConcat*)res)->size = nend - nstart;

        Allocator::GlobalAllocator.popRoot(); 
    }

    Allocator::GlobalAllocator.popRoot();
    return res;
}

void BSQListEntityType::initializeIteratorBegin(BSQListIterator* iter, void* data)
{
    iter->lroot = data;
    iter->lpos = 0;
    iter->cbuff = nullptr;

    initializeListIterPosition(iter, 0);
}

void* BSQListEntityType::concat2(StorageLocationPtr s1, StorageLocationPtr s2)
{
    Allocator::GlobalAllocator.ensureSpace(sizeof(BSQListConcat) + sizeof(BSQListFlatK<64>));

    void* l1 = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(s1);
    const BSQListEntityType* l1type = GET_TYPE_META_DATA_AS(BSQListEntityType, l1);

    void* l2 = SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(s2);
    const BSQListEntityType* l2type = GET_TYPE_META_DATA_AS(BSQListEntityType, l2);

    if(BSQListEntityType::empty(l1) & BSQListEntityType::empty(l2))
    {
        return BSQListEntityType::getDefaultEmpty(xxxx);
    }
    else if(BSQListEntityType::empty(l1))
    {
        return l2;
    }
    else if(BSQListEntityType::empty(l2))
    {
        return l1;
    }
    else
    {
        auto len1 = l1type->getLength(l1);
        auto size1 = len1 * l1type->esize;
        auto len2 = l2type->getLength(l2);
        auto size2 = len2 * l2type->esize;;

        void* res;
        if(size1 + size2 < 64)
        {
            res = Allocator::GlobalAllocator.allocateSafe(sizeof(BSQListFlatK<64>), xxxx);
            uint8_t* curr = BSQListFlatKTypeAbstract::getDataBytes(res);

            ((BSQListFlatK<64>*)res)->ecount = len1 + len2;

            BSQListIterator iter1;
            initializeIteratorBegin(&iter1, l1);
            while(iteratorIsValid(&iter1))
            {
                iteratorGetElement(&iter1, curr, l1type->etype);
                curr += l1type->esize;
                incrementListIterator(&iter1);
            }

                BSQStringIterator iter2;
                BSQStringType::initializeIteratorBegin(&iter2, str2);
                while(iteratorIsValid(&iter2))
                {
                    *curr = iteratorGetUTF8Byte(&iter2);
                    curr++;
                    incrementStringIterator_utf8byte(&iter2);
                }

                res.u_data = crepr;
        }
            else
            {
                auto crepr = (BSQListConcat*)Allocator::GlobalAllocator.allocateSafe(sizeof(BSQListConcat), Environment::g_typeStringConcatRepr);
                crepr->size = len1 + len2;
                crepr->srepr1 = IS_INLINE_STRING(s1) ? BSQStringType::boxInlineString(str1.u_inlineString) : str1.u_data;
                crepr->srepr2 = IS_INLINE_STRING(s2) ? BSQStringType::boxInlineString(str2.u_inlineString) : str2.u_data;
                
                res.u_data = crepr;
            }

        return res;
    }
}

void* BSQListEntityType::slice(StorageLocationPtr str, uint64_t startpos, uint64_t endpos)
{

}
