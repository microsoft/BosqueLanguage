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

StorageLocationPtr iteratorGetElement(const BSQListIterator* iter);
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

    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
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

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
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

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
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

    virtual uint64_t getLength(void* data) const override;
    virtual void initializeListIterPosition(BSQListIterator* iter, void* data, int64_t pos) const override;
    virtual StorageLocationPtr getValueAtPosition(void* data, uint64_t pos) const override;
    virtual void* slice(void* data, uint64_t nstart, uint64_t nend) const override;
};
