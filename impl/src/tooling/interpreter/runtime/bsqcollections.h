//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "../core/bsqmemory.h"

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
void releaseIteratorGCRoots();

bool iteratorIsValid(const BSQListIterator* iter);
void initializeListIterPosition(BSQListIterator* iter, int64_t pos);

void iteratorGetElement(const BSQListIterator* iter, void* into, const BSQType* etype);
void incrementListIterator(BSQListIterator* iter);

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQListEntityType : public BSQEntityType
{
public:
    const uint64_t esize;
    const BSQType* etype;

    //Constructor for leaf type
    BSQListEntityType(BSQTypeID tid, BSQTypeSizeInfo allocinfo, std::string name, const BSQType* etype)
    : BSQEntityType(tid, BSQTypeKind::Ref, allocinfo, {}, entityListDisplay_impl, name, {}, {}, {}), esize(etype->allocinfo.slfullsize), etype(etype)
    {;}

    //Constructor with ptrcount
    BSQListEntityType(BSQTypeID tid, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::string name, const BSQType* etype)
    : BSQEntityType(tid, BSQTypeKind::Ref, allocinfo, ptrcount, {}, entityListDisplay_impl, name, {}, {}, {}), esize(etype->allocinfo.slfullsize), etype(etype)
    {;}

    //Constructor for general refmask
    BSQListEntityType(BSQTypeID tid, BSQTypeSizeInfo allocinfo, RefMask refmask, std::string name, const BSQType* etype)
    : BSQEntityType(tid, BSQTypeKind::Ref, allocinfo, refmask, {}, entityListDisplay_impl, name, {}, {}, {}), esize(etype->allocinfo.slfullsize), etype(etype)
    {;}
   
    virtual ~BSQListEntityType() {;}

    virtual uint64_t getLength(void* data) const = 0;
    virtual void initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const = 0;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const = 0;

    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const = 0;

    static void initializeIteratorGivenPosition(BSQListIterator* iter, void* data, int64_t pos);
    static void initializeIteratorBegin(BSQListIterator* iter, void* data);

    inline static bool empty(void* data)
    {
        return GET_TYPE_META_DATA_AS(BSQListEntityType, data)->getLength(data) == 0;
    }

    static void* concat2(StorageLocationPtr s1, StorageLocationPtr s2);
    static void* slice(StorageLocationPtr str, uint64_t startpos, uint64_t endpos);
};

struct BSQEmptyList
{
    //It is an empty list
};

class BSQListEmptyType : public BSQListEntityType
{
public:
    BSQEmptyList* lempty;

    //Constructor for leaf type
    BSQListEmptyType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListEntityType(tid, {sizeof(BSQEmptyList), sizeof(void*), sizeof(void*), "2"}, name, etype), lempty(nullptr) {;}

    virtual ~BSQListEmptyType() {;}

    BSQEmptyList* generateEmptyList() const
    {
        if(this->lempty == nullptr)
        {
            Allocator::GlobalAllocator.allocateEternal(this->allocinfo.heapsize, this);
        }

        return this->lempty;
    }

    virtual uint64_t getLength(void* data) const override
    {
        return 0;
    }

    virtual void initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
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
    BSQListFlatKTypeAbstract(BSQTypeID tid, BSQTypeSizeInfo allocinfo, std::string name, const BSQType* etype): BSQListEntityType(tid, allocinfo, name, etype) {;}

    //Constructor with ptrcount
    BSQListFlatKTypeAbstract(BSQTypeID tid, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::string name, const BSQType* etype): BSQListEntityType(tid, allocinfo, ptrcount, name, etype) {;}

    //Constructor for general refmask
    BSQListFlatKTypeAbstract(BSQTypeID tid, BSQTypeSizeInfo allocinfo, RefMask refmask, std::string name, const BSQType* etype): BSQListEntityType(tid, allocinfo, refmask, etype) {;}
   
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

    void initializeIterPositionWSlice(BSQListIterator* iter, void* data, int64_t pos, int64_t maxpos) const;

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
};

template<uint16_t k>
class BSQListFlatKType : public BSQListFlatKTypeAbstract
{
public:
    //Constructor for leaf type
    BSQListFlatKType(BSQTypeID tid, std::string name, const BSQType* etype, RefMask kmask): BSQListFlatKTypeAbstract(tid, { BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>)), sizeof(void*), sizeof(void*), kmask }, name, etype) {;}

    //Constructor with ptrcount
    BSQListFlatKType(BSQTypeID tid, uint64_t pcount, std::string name, const BSQType* etype, RefMask kmask): BSQListFlatKTypeAbstract(tid, { BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>)), sizeof(void*), sizeof(void*), kmask }, pcount, name, etype) {;}

    //Constructor for general refmask
    BSQListFlatKType(BSQTypeID tid, RefMask refmask, std::string name, const BSQType* etype, RefMask kmask): BSQListFlatKTypeAbstract(tid, { BSQ_ALIGN_SIZE(sizeof(BSQListFlatK<k>)), sizeof(void*), sizeof(void*), kmask }, refmask, etype) {;}
   
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
    BSQListSliceType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListEntityType(tid, {BSQ_ALIGN_SIZE(sizeof(BSQListSlice)), sizeof(void*), sizeof(void*), "2"}, 1, name, etype) {;}
    virtual ~BSQListSliceType() {;}

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
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
    BSQListConcatType(BSQTypeID tid, std::string name, const BSQType* etype): BSQListEntityType(tid, {BSQ_ALIGN_SIZE(sizeof(BSQListConcat)), sizeof(void*), sizeof(void*), "2"}, 2, name, etype) {;}
    virtual ~BSQListConcatType() {;}

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice_impl(void* data, uint64_t nstart, uint64_t nend) const override;
};
