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
    Register,
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

    KeyEqualFP fpKeyEqual;
    KeyLessFP fpKeyLess;

    DisplayFP fpDisplay;

    const std::wstring name;

    template <bool isRoot>
    GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }
};

////
//Concrete types

class BSQTupleType : public BSQType
{
public:
    BSQTupleIndex maxIndex;
    std::vector<BSQType*> ttypes;
    std::vector<size_t> idxoffsets;
};

class BSQRecordType : public BSQType
{
public:
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQType*> rtypes;
    const std::vector<size_t> propertyoffsets;
};

class BSQEntityType : public BSQType
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQType*> etypes;
    const std::vector<size_t> fieldoffsets;
};

class BSQEphemeralListType : public BSQType
{
public:
    const std::vector<BSQType*> etypes;
    const std::vector<size_t> idxoffsets;
};

////
//Abstract types

class BSQInlineUnionType : public BSQType
{
public:
    inline uint64_t getAllocSizePlusType() const
    {
        return this->allocsize + sizeof(BSQType*);
    }
};

class BSQHeapUnionType : public BSQType
{
public:
};

