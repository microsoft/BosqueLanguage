//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqvalue.h"

#define MAP_LOAD_TYPE_INFO(SL) SLPTR_LOAD_UNION_INLINE_TYPE(SL)
#define MAP_LOAD_TYPE_INFO_REPR(SL) SLPTR_LOAD_UNION_INLINE_TYPE_AS(BSQMapReprType, SL)
#define MAP_LOAD_DATA(SL) SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL))

#define MAP_STORE_RESULT_REPR(R, SL) SLPTR_STORE_UNION_INLINE_TYPE(SLPTR_LOAD_HEAP_TYPE(R), SL); SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL), R)
#define MAP_STORE_RESULT_EMPTY(SL) SLPTR_STORE_UNION_INLINE_TYPE(BSQWellKnownType::g_typeNone, SL); SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL), BSQNoneValue)

struct BSQMapTreeRepr
{
    void* l;
    void* r;
    BSQNat count;
};

class BSQMapTreeType : public BSQRefType
{
public:
    const BSQTypeID keytype;
    const uint32_t keyoffset;

    const BSQTypeID valuetype;
    const uint32_t valueoffset;

    BSQMapTreeType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, BSQTypeID keytype, uint32_t keyoffset, BSQTypeID valuetype, uint32_t valueoffset)
    : BSQRefType(tid, allocsize, heapmask, {}, EMPTY_KEY_CMP, entityMapReprDisplay_impl, name), keytype(keytype), keyoffset(keyoffset), valuetype(valuetype), valueoffset(valueoffset)
    {;}

    virtual ~BSQMapTreeType() {;}

    inline static void* getLeft(void* repr)
    {
        return ((BSQMapTreeRepr*)repr)->l;
    }

    inline static void* getRight(void* repr)
    {
        return ((BSQMapTreeRepr*)repr)->r;
    }

    inline static BSQNat getCount(void* repr)
    {
        return ((BSQMapTreeRepr*)repr)->count;
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

struct BSQMapTypeFlavor
{
    const BSQTypeID ltype;

    const BSQType* keytype;
    const BSQType* valuetype;
    const BSQType* tupletype;

    const BSQMapTreeType* treetype;
};

//MAP
class BSQMapType : public BSQType
{
public:
    const BSQTypeID ktype; //type of K in the map
    const BSQTypeID vtype; //type of V in the map
    const BSQTypeID etype; //type of [K, V]

    BSQMapType(BSQTypeID tid, DisplayFP fpDisplay, std::string name, BSQTypeID ktype, BSQTypeID vtype, BSQTypeID etype): 
        BSQType(tid, BSQTypeLayoutKind::Struct, {16, 16, 16, nullptr, "12"}, STRUCT_STD_GC_FUNCTOR_SET, {}, EMPTY_KEY_CMP, fpDisplay, name),
        ktype(ktype), vtype(vtype), etype(etype)
    {;}

    virtual ~BSQMapType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, 16);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        BSQ_MEM_COPY(trgt, src, 16);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }
};
