//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "../core/bsqmemory.h"

struct BSQListReprIterator
{
    void* lroot;
    uint64_t esize;
    int64_t lpos;
    void* cbuff;
    int16_t cpos;
    int16_t maxpos;
};

void registerIteratorGCRoots(BSQListReprIterator* iter);
void releaseIteratorGCRoots();

bool iteratorIsValid(const BSQListReprIterator* iter);
void initializeListIterPosition(BSQListReprIterator* iter, int64_t pos);

void iteratorGetElement(const BSQListReprIterator* iter, void* into, const BSQType* etype);
void incrementListIterator(BSQListReprIterator* iter);

std::string entityListReprDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQListReprType : public BSQRefType
{
public:
    const uint64_t esize;
    const BSQType* etype;

    BSQListReprType(uint64_t allocsize, RefMask heapmask, std::string name, const BSQType* etype):
        BSQRefType(BSQ_TYPE_ID_LISTREPR, allocsize, heapmask, {}, EMPTY_KEY_FUNCTOR_SET, entityListReprDisplay_impl, name), esize(etype->allocinfo.inlinedatasize), etype(etype)
    {;}

    virtual ~BSQListReprType() {;}

    virtual uint64_t getLength(void* data) const = 0;
    virtual void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const = 0;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const = 0;

    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const = 0;
};

template <uint16_t k>
struct BSQListFlatK
{
    uint32_t bytes;
    uint32_t ecount;
    uint8_t data[k];
};

class BSQListFlatKTypeAbstract : public BSQListReprType
{
public:
    BSQListFlatKTypeAbstract(uint64_t allocsize, RefMask heapmask, std::string name, const BSQType* etype): BSQListReprType(allocsize, heapmask, name, etype) {;}

    virtual ~BSQListFlatKTypeAbstract() {;}

    inline static uint64_t getStorageBytesCount(void* data)
    {
        return *((uint32_t*)data);
    }

    inline static uint64_t getElementCount(void* data)
    {
        return *((uint32_t*)(((uint8_t*)data) + sizeof(uint32_t)));
    }

    inline static uint8_t* getDataBytes(void* data)
    {
        return ((uint8_t*)data) + sizeof(uint32_t) + sizeof(uint32_t);
    }

    inline uint8_t* initializeWriteIter(void* l) const
    {
        return this->getDataBytes(l);
    }

    inline void advanceWriteIter(uint8_t** iter) const
    {
        *iter = *iter + this->esize;
    }

    inline void storeDataToPostion(uint8_t* iter, StorageLocationPtr slptr) const
    {
        GC_MEM_COPY(iter, slptr, this->esize);
    }

    void initializeIterPositionWSlice(BSQListReprIterator* iter, void* data, int64_t pos, int64_t maxpos) const;

    uint64_t getLength(void* data) const override final;
    void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override final;
    StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override final;
    void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override final;
};

template<uint16_t k>
class BSQListFlatKType : public BSQListFlatKTypeAbstract
{
public:
    BSQListFlatKType(std::string name, const BSQType* etype, RefMask heapmask): BSQListFlatKTypeAbstract(sizeof(BSQListFlatK<k>), heapmask, name, etype) {;}

    virtual ~BSQListFlatKType() {;}
};

struct BSQListSlice
{
    void* lrepr; //a flat list
    uint64_t start;
    uint64_t end;
};

class BSQListSliceType : public BSQListReprType
{
public:
    BSQListSliceType(std::string name, const BSQType* etype): BSQListReprType(sizeof(BSQListSlice), "2", name, etype) {;}
    virtual ~BSQListSliceType() {;}

    uint64_t getLength(void* data) const override final;
    void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override final;
    StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override final;
    void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override final;
};

struct BSQListConcat
{
    void* lrepr1;
    void* lrepr2;
    uint64_t size;
};

class BSQListConcatType : public BSQListReprType
{
public:
    BSQListConcatType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListReprType(sizeof(BSQListConcat), "22", name, etype) {;}
    virtual ~BSQListConcatType() {;}

    uint64_t getLength(void* data) const override final;
    void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override final;
    StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override final;
    void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override final;
};

struct BSQList
{
    void* repr;
    uint64_t size;
};

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQListType : public BSQStructType
{
public:
    BSQListType(BSQTypeID tid, std::string name, const BSQType* etype): BSQStructType(tid, sizeof(BSQList), "21", {}, EMPTY_KEY_FUNCTOR_SET, entityListDisplay_impl, name) 
    {
        static_assert(sizeof(BSQList) == 16);
    }

    virtual ~BSQListType() {;}

    inline static bool empty(BSQList data)
    {
        return data.size == 0;
    }

    inline static uint64_t getLength(BSQList data)
    {
        return data.size;
    }

    static void initializeIteratorGivenPosition(BSQListReprIterator* iter, void* data, int64_t pos);
    static void initializeIteratorBegin(BSQListReprIterator* iter, void* data);

    static void* concat2(StorageLocationPtr s1, StorageLocationPtr s2);
    static void* slice(StorageLocationPtr str, uint64_t startpos, uint64_t endpos);
};

