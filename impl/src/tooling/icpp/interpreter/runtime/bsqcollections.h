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

class BSQListReprType : public BSQEntityAbstractType
{
public:
    const uint64_t esize;
    const BSQType* etype;

    //Constructor for leaf type
    BSQListReprType(BSQTypeSizeInfo allocinfo, std::string name, const BSQType* etype)
    : BSQEntityAbstractType(BSQ_TYPE_ID_LISTREPR, BSQTypeKind::Ref, allocinfo, {}, entityListReprDisplay_impl, name, {}, {}, {}), esize(etype->allocinfo.inlinedatasize), etype(etype)
    {;}

    //Constructor for general refmask
    BSQListReprType(BSQTypeSizeInfo allocinfo, RefMask rmask, std::string name, const BSQType* etype)
    : BSQEntityAbstractType(BSQ_TYPE_ID_LISTREPR, BSQTypeKind::Ref, allocinfo, rmask, {}, entityListReprDisplay_impl, name, {}, {}, {}), esize(etype->allocinfo.inlinedatasize), etype(etype)
    {;}
   
    virtual ~BSQListReprType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }

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
    //Constructor for leaf type
    BSQListFlatKTypeAbstract(BSQTypeSizeInfo allocinfo, std::string name, const BSQType* etype): BSQListReprType(allocinfo, name, etype) {;}

    //Constructor for general refmask
    BSQListFlatKTypeAbstract(BSQTypeSizeInfo allocinfo, RefMask refmask, std::string name, const BSQType* etype): BSQListReprType(allocinfo, refmask, name, etype) {;}
   
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

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
};

template<uint16_t k>
class BSQListFlatKType : public BSQListFlatKTypeAbstract
{
public:
    //Constructor for leaf type
    BSQListFlatKType(std::string name, const BSQType* etype, RefMask kmask): BSQListFlatKTypeAbstract({ sizeof(BSQListFlatK<k>), sizeof(void*), sizeof(void*), "x" }, name, etype) {;}

    //Constructor for general refmask
    BSQListFlatKType(std::string name, const BSQType* etype, RefMask kmask): BSQListFlatKTypeAbstract({ sizeof(BSQListFlatK<k>), sizeof(void*), sizeof(void*), kmask }, "2", name, etype) {;}
   
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
    BSQListSliceType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListReprType(tid, {sizeof(BSQListSlice), sizeof(void*), sizeof(void*), "211"}, "2", name, etype) {;}
    virtual ~BSQListSliceType() {;}

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
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
    BSQListConcatType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListReprType(tid, {sizeof(BSQListConcat), sizeof(void*), sizeof(void*), "221"}, "2", name, etype) {;}
    virtual ~BSQListConcatType() {;}

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListReprIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
};

struct BSQList
{
    void* repr;
    uint64_t size;
};

class BSQListType : public BSQEntityAbstractType
{
public:
    //Constructor for leaf type
    BSQListType(BSQTypeID tid, std::string name, const BSQType* etype)
    : BSQEntityAbstractType(tid, {sizeof(BSQList), sizeof(BSQList), sizeof(BSQList), "221"}, "2", name, etype) {;}

    //Constructor for general refmask
    BSQListType(BSQTypeID tid, std::string name, const BSQType* etype)
    : BSQEntityAbstractType(tid, {sizeof(BSQListConcat), sizeof(BSQList), sizeof(BSQList), "221"}, "2", name, etype) {;}

    virtual ~BSQListType() {;}

    inline uint64_t getLength(BSQList data) const
    {
        return data.size;
    }

    static void initializeIteratorGivenPosition(BSQListReprIterator* iter, void* data, int64_t pos);
    static void initializeIteratorBegin(BSQListReprIterator* iter, void* data);

    static void* concat2(StorageLocationPtr s1, StorageLocationPtr s2);
    static void* slice(StorageLocationPtr str, uint64_t startpos, uint64_t endpos);
};

