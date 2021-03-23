//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../core/bsqmemory.h"

enum class BSQTypeKind : uint8_t
{
    Invalid = 0x0,
    Tuple,
    Record,
    SpecialEntity,
    StdEntity,
    Ephemeral,
    AbstractTuple,
    AbstractRecord,
    Concept,
    InlineUnion,
    HeapUnion
};

class BSQType
{
public:
    const BSQTypeID tid;
    const BSQTypeKind tkind;

    const BSQGCKind gckind;
    const uint64_t allocsize; //memory size of data (with alignment)

    const RefMask* refmask;
    const uint64_t ptrcount; //if this is a packed object the number of pointers at the front

    GCDecOperatorFP fpDecObj;
    GCClearMarkOperatorFP fpClearObj;
    GCProcessOperatorFP fpProcessObjRoot;
    GCProcessOperatorFP fpProcessObjHeap;

    DisplayFP fpDisplay;

    const std::wstring name;

    template <bool isRoot>
    GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }

    virtual void slclear(StorageLocationPtr dst) const = 0;
    virtual void slcopy(StorageLocationPtr dst, StorageLocationPtr src) const = 0;

    virtual void slconvert(StorageLocationPtr dst, StorageLocationPtr src) const = 0;
};

////
//Concrete types

class BSQConcreteType : public BSQType
{

};

class BSQTupleType : public BSQConcreteType
{
public:
    const bool isValue;
    const BSQTupleIndex maxIndex;
};

class BSQRecordType : public BSQConcreteType
{
public:
    static std::map<BSQRecordPropertyID, std::wstring> pnames;

    const bool isValue;
    const std::vector<BSQRecordPropertyID> properties;
};

//Has subtypes for the special builtin entity types
class BSQSpecialEntityType : public BSQConcreteType
{
public:
    const bool isValue;
};

class BSQStdEntityType : public BSQConcreteType
{
public:
    const bool isValue;
};

class BSQEphemeralListType : public BSQConcreteType
{
public:
};

////
//Abstract types

class BSQAbstractType : public BSQType
{

};

class BSQAbstractTupleType : public BSQAbstractType
{
public:
    const bool isValue;
};

class BSQAbstractRecordType : public BSQAbstractType
{
public:
    const bool isValue;
};

class BSQConceptType : public BSQAbstractType
{
public:
    const bool isValue;
};

class BSQUnionType : public BSQAbstractType
{
public:
};

class BSQInlineUnionType : public BSQUnionType
{
public:
    //should always be a "value" of [type data] even when data is a ptr
};

class BSQHeapUnionType : public BSQUnionType
{
public:
};



