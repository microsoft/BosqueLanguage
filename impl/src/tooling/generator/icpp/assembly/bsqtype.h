//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../core/bsqmemory.h"

enum class BSQTypeKind : uint32_t
{
    Invalid = 0x0,
    Fixed,
    Struct,
    Ref,
    InlineUnion,
    HeapUnion
};

class BSQType
{
public:
    const BSQTypeID tid;
    const BSQTypeKind tkind;
    
    const uint64_t allocsize; //memory size of data (with alignment)
    
    RefMask refmask;
    const uint64_t ptrcount; //if this is a packed object the number of pointers at the front

    GCDecOperatorFP fpDecObj;
    GCClearMarkOperatorFP fpClearObj;
    GCProcessOperatorFP fpProcessObjRoot;
    GCProcessOperatorFP fpProcessObjHeap;

    const bool isLeafType; //if refmask == nullptr && ptrcount == 0

    const std::map<BSQVirtualInvokeID, BSQInvokeID> vtable; //TODO: This is slow indirection but nice and simple
    const std::set<BSQTypeID> subtypes;

    DisplayFP fpDisplay;

    const std::wstring name;

    template <bool isRoot>
    GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }

    virtual void slclear(StorageLocationPtr dst) const = 0;
    virtual void slcopy(StorageLocationPtr dst, StorageLocationPtr src) const = 0;

    virtual StorageLocationPtr slindex(StorageLocationPtr src, size_t offset) const
    {
        return SLPTR_INDEX(src, offset);
    }

    virtual void* getExtraTypeInfo() const
    {
        return nullptr;
    }
};

template <typename T>
class BSQFixedLayoutType : public BSQType
{
public:
    virtual void slclear(StorageLocationPtr dst) const override 
    {
        SLPTR_STORE_CONTENTS_AS(T, dst, {0});
    }

    virtual void slcopy(StorageLocationPtr dst, StorageLocationPtr src) const override 
    {
        SLPTR_STORE_CONTENTS_AS(T, dst, SLPTR_LOAD_CONTENTS_AS(T, src));
    }
};

class BSQStructType : public BSQType
{
public:
    virtual void slclear(StorageLocationPtr dst) const override 
    {
        GC_MEM_ZERO(dst, this->allocsize);
    }

    virtual void slcopy(StorageLocationPtr dst, StorageLocationPtr src) const override 
    {
        GC_MEM_COPY(dst, src, this->allocsize);
    }
};

class BSQRefType : public BSQType
{
public:
    virtual void slclear(StorageLocationPtr dst) const override 
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(dst, nullptr);
    }

    virtual void slcopy(StorageLocationPtr dst, StorageLocationPtr src) const override 
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(dst, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr slindex(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX(SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src), offset);
    }
};

////
//Concrete types

struct BSQTupleTypeInfo
{
    BSQTupleIndex maxIndex;
    std::vector<BSQType*> ttypes;
    std::vector<size_t> idxoffsets;
};

class BSQStructTupleType : public BSQStructType
{
public:
    const BSQTupleTypeInfo tinfo;
};

class BSQRefTupleType : public BSQRefType
{
public:
    const BSQTupleTypeInfo tinfo;
};

struct BSQRecordTypeInfo
{
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQType*> rtypes;
    const std::vector<size_t> propertyoffsets;
};

class BSQStructRecordType : public BSQStructType
{
public:
    const BSQRecordTypeInfo rinfo;
};

class BSQRefRecordType : public BSQRefType
{
public:
    const BSQRecordTypeInfo rinfo;
};

struct BSQEntityTypeInfo
{
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQType*> etypes;
    const std::vector<size_t> fieldoffsets;
};

//Has subtypes for the special builtin entity types
template <typename T>
class BSQFixedEntityType : public BSQFixedLayoutType<T>
{
public:
};

class BSQStructEntityType : public BSQStructType
{
public:
    const BSQEntityTypeInfo rinfo;
};

class BSQRefEntityType : public BSQRefType
{
public:
    const BSQEntityTypeInfo rinfo;
};

class BSQEphemeralListType : public BSQStructType
{
public:
    const std::vector<BSQType*> etypes;
    const std::vector<size_t> idxoffsets;
};

////
//Abstract types

class BSQInlineUnionType : BSQStructType
{
public:
};

class BSQHeapUnionType : BSQRefType
{
public:
};

