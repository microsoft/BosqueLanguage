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

////
//Standard memory function pointer definitions
void gcDecOperator_packedImpl(const BSQType* btype, void** data);
void gcDecOperator_maskImpl(const BSQType* btype, void** data);

void gcClearOperator_packedImpl(const BSQType* btype, void** data);
void gcClearOperator_maskImpl(const BSQType* btype, void** data);

void gcProcessRootOperator_packedImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_maskImpl(const BSQType* btype, void** data);

void gcProcessHeapOperator_packedImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data);

////
//BSQType abstract base class
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

    const std::string name;

    template <bool isRoot>
    GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }

private:
    //Constructor that everyone delegates to
    BSQType(
        BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, uint64_t ptrcount,
        GCDecOperatorFP fpDecObj, GCClearMarkOperatorFP fpClearObj, GCProcessOperatorFP fpProcessObjRoot, GCProcessOperatorFP fpProcessObjHeap,
        bool isLeafType, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes,
        KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay,
        std::string name
    ) 
    : tid(tid), tkind(tkind), allocsize(allocsize), refmask(refmask), ptrcount(ptrcount), 
    fpDecObj(fpDecObj), fpClearObj(fpClearObj), fpProcessObjRoot(fpProcessObjRoot), fpProcessObjHeap(fpProcessObjHeap),
    isLeafType(isLeafType), vtable(vtable), subtypes(subtypes),
    fpKeyEqual(fpKeyEqual), fpKeyLess(fpKeyLess), fpDisplay(fpDisplay),
    name(name)
    {;}

public:
    //Constructor abstract types
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::string name)
    : BSQType(tid, tkind, allocsize, nullptr, 0, nullptr, nullptr, nullptr, nullptr, true, {}, {}, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor for leaf type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name)
    : BSQType(tid, tkind, allocsize, nullptr, 0, nullptr, nullptr, nullptr, nullptr, true, vtable, subtypes, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor for key leaf type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name)
    : BSQType(tid, tkind, allocsize, nullptr, 0, nullptr, nullptr, nullptr, nullptr, true, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor with ptrcount
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocsize, nullptr, ptrcount, gcDecOperator_packedImpl, gcClearOperator_packedImpl, gcProcessRootOperator_packedImpl, gcProcessHeapOperator_packedImpl, false, vtable, subtypes, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor with key ptrcount
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocsize, nullptr, ptrcount, gcDecOperator_packedImpl, gcClearOperator_packedImpl, gcProcessRootOperator_packedImpl, gcProcessHeapOperator_packedImpl, false, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor for general refmask
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocsize, refmask, 0, gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl, false, vtable, subtypes, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor with key general refmask
    BSQType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocsize, refmask, 0, gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl, false, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    virtual ~BSQType() {;}
};

////
//Concrete types

std::string tupleDisplay_impl(const BSQType* btype, void** data);

class BSQTupleType : public BSQType
{
public:
    const BSQTupleIndex maxIndex;
    const std::vector<BSQType*> ttypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for key leaf type
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with ptrcount
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with key ptrcount
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for general refmask
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with key general refmask
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQType*> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name),
    maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQTupleType() {;}
};

std::string recordDisplay_impl(const BSQType* btype, void** data);

class BSQRecordType : public BSQType
{
public:
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQType*> rtypes;
    const std::vector<size_t> propertyoffsets;

    //Constructor for leaf type
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor for key leaf type
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, fpKeyEqual, fpKeyLess, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with ptrcount
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                 std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with key ptrcount
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, fpKeyEqual, fpKeyLess, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor for general refmask
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with key general refmask
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQType*> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, fpKeyEqual, fpKeyLess, recordDisplay_impl, name),
    properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    virtual ~BSQRecordType() {;}
};

std::string entityDisplay_impl(const BSQType* btype, void** data);

class BSQEntityType : public BSQType
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQType*> ftypes;
    const std::vector<size_t> fieldoffsets;

    //Constructor for leaf type
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor for key leaf type
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with ptrcount
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name,
                 std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with key ptrcount
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor for general refmask
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with key general refmask
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::set<BSQTypeID> subtypes, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQType*> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocsize, refmask, vtable, subtypes, fpKeyEqual, fpKeyLess, fpDisplay, name),
    fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    virtual ~BSQEntityType() {;}
};

std::string ephemeralDisplay_impl(const BSQType* btype, void** data);

class BSQEphemeralListType : public BSQType
{
public:
    const std::vector<BSQType*> etypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::string name,
                std::vector<BSQType*> etypes, std::vector<size_t> idxffsets)
    : BSQType(tid, tkind, allocsize, {}, {}, entityDisplay_impl, name),
    etypes(etypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with ptrcount
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, uint64_t ptrcount, std::string name,
                 std::vector<BSQType*> etypes, std::vector<size_t> idxffsets)
    : BSQType(tid, tkind, allocsize, ptrcount, {}, {}, entityDisplay_impl, name),
    etypes(etypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for general refmask
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, RefMask refmask, std::string name,
                std::vector<BSQType*> etypes, std::vector<size_t> idxffsets)
    : BSQType(tid, tkind, allocsize, refmask, {}, {}, entityDisplay_impl, name),
    etypes(etypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQEphemeralListType() {;}
};

////
//Abstract types

class BSQInlineUnionType : public BSQType
{
public:
    BSQInlineUnionType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::string name)
    : BSQType(tid, tkind, allocsize, name)
    {;}

    virtual ~BSQInlineUnionType() {;}

    inline uint64_t getAllocSizePlusType() const
    {
        return this->allocsize + sizeof(BSQType*);
    }
};

class BSQHeapUnionType : public BSQType
{
public:
    BSQHeapUnionType(BSQTypeID tid, BSQTypeKind tkind, uint64_t allocsize, std::string name)
    : BSQType(tid, tkind, allocsize, name)
    {;}

    virtual ~BSQHeapUnionType() {;}
};

