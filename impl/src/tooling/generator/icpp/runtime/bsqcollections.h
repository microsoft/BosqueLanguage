//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"

struct BSQListIterator
{
    void* lroot;
    uint64_t esize;
    int64_t lpos;
    void* cbuff;
    int16_t cpos;
    int16_t maxpos;
};

void registerIteratorGCRoots(BSQListIterator* iter);
void releaseIteratorGCRoots(BSQListIterator* iter);

bool iteratorIsValid(const BSQListIterator* iter);

void* iteratorGetElement(const BSQListIterator* iter);
void incrementListIterator(BSQListIterator* iter);

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQListEntityType : public BSQEntityType
{
public:
    const uint64_t esize;

    //Constructor for leaf type
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, std::string name, uint64_t esize): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, {}, entityListDisplay_impl, name, {}, {}, {}), esize(esize) {;}

    //Constructor with ptrcount
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, uint64_t ptrcount, std::string name, uint64_t esize): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, ptrcount, {}, entityListDisplay_impl, name, {}, {}, {}), esize(esize) {;}

    //Constructor for general refmask
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, RefMask refmask, std::string name, uint64_t esize): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, refmask, {}, entityListDisplay_impl, name, {}, {}, {}), esize(esize) {;}
   
    virtual ~BSQListEntityType() {;}

    virtual uint64_t getLength(void* data) const = 0;
    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const = 0;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const = 0;

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const = 0;
};

struct BSQEmptyList
{
    //It is an empty list
};

class BSQListEmptyType : public BSQListEntityType
{
public:
    //Constructor for leaf type
    BSQListEmptyType(BSQTypeID tid, std::string name): BSQListEntityType(tid, 8, name, 8) {;}

    virtual ~BSQListEmptyType() {;}

    virtual uint64_t getLength(void* data) const override
    {
        return 0;
    }

    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override
    {
        //NOP
    }

    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override
    {
        assert((nstart == 0) & (nend == 0));
        return data;
    }
};

template <uint16_t k>
struct BSQListFlatK
{
    uint32_t bytes;
    uint32_t ecount;
    uint8_t data[k];
};

class BSQListFlatKTypeAbstract : public BSQListEntityType
{
public:
    //Constructor for leaf type
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, name, entrysize) {;}

    //Constructor with ptrcount
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, uint64_t ptrcount, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, ptrcount, name, entrysize) {;}

    //Constructor for general refmask
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, RefMask refmask, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, refmask, entrysize) {;}
   
    virtual ~BSQListFlatKTypeAbstract() {;}

    static uint64_t getStorageBytesCount(void* data)
    {
        return *((uint32_t*)data);
    }

    static uint64_t getElementCount(void* data)
    {
        return *((uint32_t*)(((uint8_t*)data) + sizeof(uint32_t)));
    }

    static StorageLocationPtr getDataInfo(void* data)
    {
        return (StorageLocationPtr)(((uint8_t*)data) + sizeof(uint32_t) + sizeof(uint32_t));
    }

    virtual uint64_t getLength(void* data) const override
    {
        return BSQListFlatKTypeAbstract::getElementCount(data);
    }

    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override
    {
        iter->cbuff = (void*)BSQListFlatKTypeAbstract::getDataInfo(data);
        iter->cpos = pos * this->esize;
        iter->maxpos = BSQListFlatKTypeAbstract::getStorageBytesCount(data);
    }

    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override
    {
        return BSQListFlatKTypeAbstract::getDataInfo(data) + (pos * this->esize);
    }

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override
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
};

template<uint16_t k>
class BSQListFlatKType : public BSQListFlatKTypeAbstract
{
public:
    //Constructor for leaf type
    BSQListFlatKType(BSQTypeID tid, std::string name, uint64_t entrysize): BSQListFlatKTypeAbstract(tid, BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>))), name) {;}

    //Constructor with ptrcount
    BSQListFlatKType(BSQTypeID tid, std::string name): BSQListFlatKTypeAbstract(tid, BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>))), k, name, BSQ_ALIGN_SIZE(void*)) {;}

    //Constructor for general refmask
    BSQListFlatKType(BSQTypeID tid, RefMask refmask, std::string name, uint64_t entrysize): BSQListFlatKTypeAbstract(tid, BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>))), refmask, entrysize) {;}
   
    virtual ~BSQListFlatKType() {;}
};

struct BSQListSlice
{
    void* lrepr; //a flat list
    uint64_t start;
    uint64_t end;
};

class BSQListSliceType : public BSQListEntityType
{
public:
    BSQListSliceType(BSQTypeID tid, std::string name, uint64_t esize): BSQListEntityType(tid, BSQ_ALIGN_SIZE(sizeof(BSQListSlice)), 1, name, esize) {;}
    virtual ~BSQListSliceType() {;}

    virtual uint64_t getLength(void* data) const override
    {
        auto sl = (BSQListSlice*)data;
        return sl->end - sl->start;
    }

    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override
    {
        auto sl = (BSQListSlice*)data;
        auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
        kltype->initializeListIterPosition(iter, sl->lrepr, pos + sl->start);
    }

    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override 
    {
        auto sl = (BSQListSlice*)data;
        auto kltype = GET_TYPE_META_DATA_AS(BSQListFlatKTypeAbstract, sl->lrepr);
        return kltype->getValueAtPosition(sl->lrepr, pos + sl->start);
    }

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override
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
};

struct BSQListConcat
{
    void* lrepr1;
    void* lrepr2;
    uint64_t size;
};

class BSQListConcatType : public BSQListEntityType
{
public:
    BSQListConcatType(BSQTypeID tid, std::string name, uint64_t esize): BSQListEntityType(tid, BSQ_ALIGN_SIZE(sizeof(BSQListConcat)), 2, name, esize) {;}
    virtual ~BSQListConcatType() {;}

    virtual uint64_t getLength(void* data) const override
    {
        auto cl = (BSQListConcat*)data;
        return cl->size;
    }

    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override
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

    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override 
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

    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override
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
};
