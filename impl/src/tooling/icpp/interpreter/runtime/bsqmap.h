//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqvalue.h"

#define MAP_LOAD_DATA(SL) SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SL)
#define MAP_LOAD_REPR_TYPE(SL) SLPTR_LOAD_HEAP_TYPE_AS(BSQMapTreeType, SL)

#define MAP_STORE_RESULT_REPR(R, SL) SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SL, R)
#define MAP_STORE_RESULT_EMPTY(SL) SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SL, nullptr)

struct BSQMapTreeRepr
{
    void* l;
    void* r;
    uint32_t tcount;
    uint32_t color; //TODO: when we balance
};

class BSQMapTreeType : public BSQRefType
{
public:
    const BSQTypeID keytype;
    const uint32_t keyoffset;

    const BSQTypeID valuetype;
    const uint32_t valueoffset;

    BSQMapTreeType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, BSQTypeID keytype, uint32_t keyoffset, BSQTypeID valuetype, uint32_t valueoffset)
    : BSQRefType(tid, allocsize, heapmask, {}, EMPTY_KEY_CMP, nullptr, name), keytype(keytype), keyoffset(keyoffset), valuetype(valuetype), valueoffset(valueoffset)
    {;}

    virtual ~BSQMapTreeType() {;}

    inline void initializeLeaf(void* repr, StorageLocationPtr ksl, const BSQType* ktype, StorageLocationPtr vsl, const BSQType* vtype) const
    {
        ((BSQMapTreeRepr*)repr)->l = nullptr;
        ((BSQMapTreeRepr*)repr)->r = nullptr;
        ((BSQMapTreeRepr*)repr)->tcount = 1;

        ktype->storeValue((StorageLocationPtr)((uint8_t*)repr + this->keyoffset), ksl);
        vtype->storeValue((StorageLocationPtr)((uint8_t*)repr + this->valueoffset), vsl);
    }

    inline void initializeLR(void* repr, StorageLocationPtr ksl, const BSQType* ktype, StorageLocationPtr vsl, const BSQType* vtype, void* l, void* r) const
    {
        ((BSQMapTreeRepr*)repr)->l = l;
        ((BSQMapTreeRepr*)repr)->r = r;

        auto lcount = (((BSQMapTreeRepr*)repr)->l != nullptr) ? ((BSQMapTreeRepr*)((BSQMapTreeRepr*)repr)->l)->tcount : 0;
        auto rcount = (((BSQMapTreeRepr*)repr)->r != nullptr) ? ((BSQMapTreeRepr*)((BSQMapTreeRepr*)repr)->r)->tcount : 0;

        ((BSQMapTreeRepr*)repr)->tcount = 1 + lcount + rcount;

        ktype->storeValue((StorageLocationPtr)((uint8_t*)repr + this->keyoffset), ksl);
        vtype->storeValue((StorageLocationPtr)((uint8_t*)repr + this->valueoffset), vsl);
    }

    inline static void* getLeft(void* repr)
    {
        return ((BSQMapTreeRepr*)repr)->l;
    }

    inline static void* getRight(void* repr)
    {
        return ((BSQMapTreeRepr*)repr)->r;
    }

    StorageLocationPtr getKeyLocation(void* repr) const
    {
        return (StorageLocationPtr)((uint8_t*)repr + this->keyoffset);
    }

    StorageLocationPtr getValueLocation(void* repr) const
    {
        return (StorageLocationPtr)((uint8_t*)repr + this->valueoffset);
    }

    inline static void* minElem(void* repr)
    {
        void* curr = repr;
        void* ll = BSQMapTreeType::getLeft(curr);

        while(ll != nullptr)
        {
            curr = ll;
            ll = BSQMapTreeType::getLeft(curr);
        }

        return curr;
    }

    inline static void* maxElem(void* repr)
    {
        void* curr = repr;
        void* rr = BSQMapTreeType::getRight(curr);

        while(rr != nullptr)
        {
            curr = rr;
            rr = BSQMapTreeType::getRight(curr);
        }

        return curr;
    }
};

class BSQMapSpineIterator : public BSQCollectionIterator
{
public:
    BSQMapSpineIterator(const BSQType* mreprtype, void* mroot): BSQCollectionIterator()
    {
        if(mroot != nullptr) 
        {
            this->lcurr = mroot;
        }
    }
    
    virtual ~BSQMapSpineIterator() {;}

    inline bool valid() const
    {
        return this->lcurr != nullptr;
    }

    inline void moveLeft()
    {
        assert(this->valid());

        this->iterstack.push_back(this->lcurr);
        this->lcurr = static_cast<BSQMapTreeRepr*>(this->lcurr)->l;
    }

    inline void moveRight()
    {
        assert(this->valid());

        this->iterstack.push_back(this->lcurr);
        this->lcurr = static_cast<BSQMapTreeRepr*>(this->lcurr)->r;
    }

    inline void pop()
    {
        assert(this->valid());

        this->lcurr = this->iterstack.back();
        this->iterstack.pop_back();
    }
};

struct BSQMapTypeFlavor
{
    const BSQTypeID mtype;
    const BSQTypeID mreprtype;

    const BSQType* keytype;
    const BSQType* valuetype;

    const BSQMapTreeType* treetype;
};

//MAP
class BSQMapType : public BSQType
{
public:
    const BSQTypeID ktype; //type of K in the map
    const BSQTypeID vtype; //type of V in the map

    BSQMapType(BSQTypeID tid, DisplayFP fpDisplay, std::string name, BSQTypeID ktype, BSQTypeID vtype): 
        BSQType(tid, BSQTypeLayoutKind::Collection, {8, 8, 8, nullptr, "5"}, {gcProcessHeapOperator_collectionImpl, gcDecOperator_collectionImpl, gcEvacuateOperator_collectionImpl}, {}, EMPTY_KEY_CMP, fpDisplay, name),
        ktype(ktype), vtype(vtype) 
    {;}

    virtual ~BSQMapType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, src);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }
};
