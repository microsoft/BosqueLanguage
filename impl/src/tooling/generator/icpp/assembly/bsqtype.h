//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#define PTR_FIELD_MASK_SCALAR '1'
#define PTR_FIELD_MASK_PTR '2'
#define PTR_FIELD_MASK_UNION '4'
#define PTR_FIELD_MASK_END (char)0

typedef uint32_t BSQTypeID;
typedef uint32_t BSQAbstractTypeID;
typedef uint32_t BSQTupleIndex;
typedef uint32_t BSQRecordPropertyID;

enum class BSQTypeKind : uint8_t
{
    Invalid = 0x0,
    Tuple,
    Record,
    SpecialEntity,
    StdEntity
};

enum class BSQGCKind : uint8_t
{
    Invalid = 0x0,
    Leaf,
    Packed,
    Mixed
};

class BSQType;

typedef const char* RefMask;

typedef void (*GCDecOperatorFP)(const BSQType*, void**);
typedef void (*GCClearMarkOperatorFP)(const BSQType*, void**);
typedef void (*GCProcessOperatorFP)(const BSQType*, void**);

typedef void* (*UnionBoxToValue)(void*);
typedef void (*UnionUnboxFromValue)(void*, void*);

typedef std::wstring (*DisplayFP)(void*);

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
};

class BSQTupleType : public BSQType
{
public:
    const BSQTupleIndex maxIndex;
    const bool isValue;
};

class BSQRecordType : public BSQType
{
public:
    static std::map<BSQRecordPropertyID, std::wstring> pnames;

    const std::vector<BSQRecordPropertyID> properties;
    const bool isValue;
};

class BSQSpecialEntityType : public BSQType
{
public:
    const bool isValue;
};

class BSQStdEntityType : public BSQType
{
public: 
    const bool isValue;
};
