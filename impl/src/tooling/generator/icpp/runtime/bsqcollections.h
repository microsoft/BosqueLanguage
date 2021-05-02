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
    int64_t lpos;
    void* cbuff;
    uint64_t entrysize;
    int16_t cpos;
    int16_t minpos;
    int16_t maxpos;
};

std::string entityListDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQListEntityType : public BSQEntityType
{
public:
    //Constructor for leaf type
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, std::string name): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, {}, entityListDisplay_impl, name, {}, {}, {}) {;}

    //Constructor with ptrcount
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, uint64_t ptrcount, std::string name): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, ptrcount, {}, entityListDisplay_impl, name, {}, {}, {}) {;}

    //Constructor for general refmask
    BSQListEntityType(BSQTypeID tid, uint64_t allocsize, RefMask refmask, std::string name): BSQEntityType(tid, BSQTypeKind::Ref, allocsize, refmask, {}, entityListDisplay_impl, name, {}, {}, {}) {;}
   
    virtual ~BSQListEntityType() {;}

    virtual BSQNat getLength(void* data) const = 0;
};

struct BSQEmptyList
{
    //It is an empty list
};

class BSQListEmptyType : public BSQListEntityType
{
public:
    //Constructor for leaf type
    BSQListEmptyType(BSQTypeID tid, std::string name): BSQListEntityType(tid, 8, name) {;}

    virtual ~BSQListEmptyType() {;}

    virtual BSQNat getLength(void* data) const override
    {
        return 0;
    }
};

template <uint16_t k>
struct BSQListFlatK
{
    uint32_t length;
    uint8_t data[k];
};

class BSQListFlatKTypeAbstract : public BSQListEntityType
{
public:
    const uint64_t entrysize;

    //Constructor for leaf type
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, name), entrysize(entrysize) {;}

    //Constructor with ptrcount
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, uint64_t ptrcount, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, ptrcount, name), entrysize(entrysize) {;}

    //Constructor for general refmask
    BSQListFlatKTypeAbstract(BSQTypeID tid, uint64_t allocsize, RefMask refmask, std::string name, uint64_t entrysize): BSQListEntityType(tid, allocsize, refmask), entrysize(entrysize) {;}
   
    static uint64_t getEntryCount(void* repr)
    {
        return *((uint64_t*)repr);
    }

    uint64_t getEntryByteCount(void* repr)
    {
        return *((uint64_t*)repr) * this->entrysize;
    }

    static uint8_t* getEntryData(void* repr)
    {
        return ((uint8_t*)repr) + sizeof(uint64_t);
    }
};

template<uint16_t k>
class BSQListFlatKType : public 
{
public:
    virtual BSQNat getLength(void* data) const override
    {
        return ((BSQListFlatContents<k>*)data)->length;
    }
};

struct BSQListSlice
{
    void* lrepr; //a flat list
    uint64_t start;
    uint64_t end;
};

struct BSQListConcatRepr
{
    void* lrepr1;
    void* lrepr2;
    uint64_t size;
};

