//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

////
//Standard memory function pointer definitions
void gcDecOperator_maskImpl(const BSQType* btype, void** data);
void gcDecOperator_stringImpl(const BSQType* btype, void** data);
void gcDecOperator_bignumImpl(const BSQType* btype, void** data);

void gcClearOperator_maskImpl(const BSQType* btype, void** data);
void gcClearOperator_stringImpl(const BSQType* btype, void** data);
void gcClearOperator_bignumImpl(const BSQType* btype, void** data);

void gcProcessRootOperator_maskImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_stringImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data);

void gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data);

class BSQTypeSizeInfo
{
public:
    const uint64_t heapsize;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    const uint64_t inlinedatasize; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref and heap union -- and word size for BSQBool)
    const uint64_t assigndatasize; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    const RefMask slmask; //The mask to use to traverse this object (even if this isn't a mixed obj -- e.g. it may be embedded in a mixed obj and we need to use this)   
};

struct BSQTypeVTableEntry
{
    BSQVirtualInvokeID vkey;
    BSQInvokeID ikey;
};

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;

    const BSQTypeID tid;
    const BSQTypeKind tkind;
    
    const BSQTypeSizeInfo allocinfo; //memory size information
    
    RefMask refmask;
    GCDecOperatorFP fpDecObj;
    GCClearMarkOperatorFP fpClearObj;
    GCProcessOperatorFP fpProcessObjRoot;
    GCProcessOperatorFP fpProcessObjHeap;

    const bool isLeafType; //if refmask == nullptr && ptrcount == 0

    const BSQTypeVTableEntry* vtable; //TODO: This is slow indirection but nice and simple
    const size_t vtableCount;

    KeyEqualFP fpKeyEqual;
    KeyLessFP fpKeyLess;

    DisplayFP fpDisplay;

    const std::string name;

private:
    //Constructor that everyone delegates to
    BSQType(
        BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask,
        GCDecOperatorFP fpDecObj, GCClearMarkOperatorFP fpClearObj, GCProcessOperatorFP fpProcessObjRoot, GCProcessOperatorFP fpProcessObjHeap,
        bool isLeafType, BSQTypeVTableEntry* vtable, size_t vtableCount,
        KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay,
        std::string name
    ) 
    : tid(tid), tkind(tkind), allocinfo(allocinfo), refmask(refmask), 
    fpDecObj(fpDecObj), fpClearObj(fpClearObj), fpProcessObjRoot(fpProcessObjRoot), fpProcessObjHeap(fpProcessObjHeap),
    isLeafType(isLeafType), vtable(vtable), vtableCount(vtableCount),
    fpKeyEqual(fpKeyEqual), fpKeyLess(fpKeyLess), fpDisplay(fpDisplay),
    name(name)
    {;}

public:
    //Constructor for leaf type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, DisplayFP fpDisplay, std::string name)
    : BSQType(tid, tkind, allocinfo, nullptr, nullptr, nullptr, nullptr, nullptr, true, vtable, vtableCount, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor for key leaf type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name)
    : BSQType(tid, tkind, allocinfo, nullptr, nullptr, nullptr, nullptr, nullptr, true, vtable, vtableCount, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor for general refmask
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, BSQTypeVTableEntry* vtable, size_t vtableCount, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocinfo, refmask, gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl, false, vtable, vtableCount, nullptr, nullptr, fpDisplay, name)
    {;}

    //Constructor with key general refmask
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, tkind, allocinfo, refmask, gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl, false, vtable, vtableCount, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor for string type
    BSQType(BSQTypeSizeInfo allocinfo, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name) 
    : BSQType(BSQ_TYPE_ID_STRING, BSQTypeKind::String, allocinfo, nullptr, gcDecOperator_stringImpl, gcClearOperator_stringImpl, gcProcessRootOperator_stringImpl, gcProcessHeapOperator_stringImpl, false, nullptr, 0, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor for bignum type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name) 
    : BSQType(tid, BSQTypeKind::BigNum, allocinfo, nullptr, gcDecOperator_bignumImpl, gcClearOperator_bignumImpl, gcProcessRootOperator_bignumImpl, gcProcessHeapOperator_bignumImpl, false, nullptr, 0, fpKeyEqual, fpKeyLess, fpDisplay, name)
    {;}

    //Constructor abstract type
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, DisplayFP fpDisplay, std::string name)
    : BSQType(tid, tkind, allocinfo, nullptr, nullptr, nullptr, nullptr, nullptr, false, nullptr, 0, nullptr, nullptr, fpDisplay, name)
    {;}

    virtual ~BSQType() 
    {
        if(this->vtable != nullptr)
        {
            delete[] this->vtable;
        }
    }

    virtual void clearValue(StorageLocationPtr trgt) const;
    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const;
    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const;
};

////////////////////////////////
//Storage Operators

template <bool isRoot>
GCProcessOperatorFP getProcessFP(const BSQType* tt)
{
    static_assert(false);
}

template <>
GCProcessOperatorFP getProcessFP<true>(const BSQType* tt)
{
    return tt->fpProcessObjRoot;
}

template <>
inline GCProcessOperatorFP getProcessFP<false>(const BSQType* tt)
{
    return tt->fpProcessObjHeap;
}

////
//Concrete types

std::string tupleDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQTupleAbstractType : public BSQType
{
public:
    const BSQTupleIndex maxIndex;
    const std::vector<BSQTypeID> ttypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQTupleAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, vtableCount, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for key leaf type
    BSQTupleAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, vtableCount, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for general refmask
    BSQTupleAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask,BSQTypeVTableEntry* vtable, size_t vtableCount, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, vtableCount, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with key general refmask
    BSQTupleAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, vtableCount, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQTupleAbstractType() {;}
};

class BSQTupleRefType : public BSQTupleAbstractType
{
public:
    //Constructor for leaf type
    BSQTupleRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQTupleAbstractType(tid, tkind, allocinfo, vtable, vtableCount, name, maxIndex, ttypes, idxoffsets)
    {;}

    //Constructor for key leaf type
    BSQTupleRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQTupleAbstractType(tid, tkind, allocinfo, vtable, vtableCount, fpKeyEqual, fpKeyLess, name, maxIndex, ttypes, idxoffsets)
    {;}

    //Constructor for general refmask
    BSQTupleRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, BSQTypeVTableEntry* vtable, size_t vtableCount, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQTupleAbstractType(tid, tkind, allocinfo, refmask, vtable, vtableCount, name, maxIndex, ttypes, idxoffsets)
    {;}

    //Constructor with key general refmask
    BSQTupleRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, BSQTypeVTableEntry* vtable, size_t vtableCount, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQTupleAbstractType(tid, tkind, allocinfo, refmask, vtable, vtableCount, fpKeyEqual, fpKeyLess, name, maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleRefType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const
    {
        return SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(src), offset));
    }
};

class BSQTupleStructType : public BSQType
{
public:
    const BSQTupleIndex maxIndex;
    const std::vector<BSQTypeID> ttypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for key leaf type
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name, 
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with ptrcount
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with key ptrcount
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for general refmask
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with key general refmask
    BSQTupleType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, fpKeyEqual, fpKeyLess, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQTupleType() {;}
};

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRecordType : public BSQType
{
public:
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQTypeID> rtypes;
    const std::vector<size_t> propertyoffsets;

    //Constructor for leaf type
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor for key leaf type
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, fpKeyEqual, fpKeyLess, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with ptrcount
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name,
                 std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with key ptrcount
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, fpKeyEqual, fpKeyLess, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor for general refmask
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    //Constructor with key general refmask
    BSQRecordType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, std::string name,
                std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, fpKeyEqual, fpKeyLess, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    virtual ~BSQRecordType() {;}
};

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEntityType : public BSQType
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQTypeID> ftypes;
    const std::vector<size_t> fieldoffsets;

    //Constructor for leaf type
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor for key leaf type
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, vtable, fpKeyEqual, fpKeyLess, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with ptrcount
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, DisplayFP fpDisplay, std::string name,
                 std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with key ptrcount
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, vtable, fpKeyEqual, fpKeyLess, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor for general refmask
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor with key general refmask
    BSQEntityType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name,
                std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, vtable, fpKeyEqual, fpKeyLess, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    //Constructor for special string action
    BSQEntityType(BSQTypeSizeInfo allocinfo, KeyEqualFP fpKeyEqual, KeyLessFP fpKeyLess, DisplayFP fpDisplay, std::string name)
    : BSQType(allocinfo, fpKeyEqual, fpKeyLess, fpDisplay, name), fields({}), ftypes({}), fieldoffsets({})
    {;}

    virtual ~BSQEntityType() {;}
};

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEphemeralListType : public BSQType
{
public:
    const std::vector<BSQTypeID> etypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, {}, entityDisplay_impl, name), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    //Constructor with ptrcount
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, uint64_t ptrcount, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, ptrcount, {}, entityDisplay_impl, name), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    //Constructor for general refmask
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, RefMask refmask, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets)
    : BSQType(tid, tkind, allocinfo, refmask, {}, entityDisplay_impl, name), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQEphemeralListType() {;}
};

////
//Abstract types

class BSQAbstractType : public BSQType
{
public:
    const std::set<BSQTypeID> subtypes;

    BSQAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, DisplayFP fpDisplay, std::string name, std::set<BSQTypeID> subtypes)
    : BSQType(tid, tkind, allocinfo, fpDisplay, name), subtypes(subtypes)
    {;}
};

std::string inlineUnionDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQInlineUnionType : public BSQAbstractType
{
public:
    BSQInlineUnionType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::string name, std::set<BSQTypeID> subtypes)
    : BSQAbstractType(tid, tkind, allocinfo, inlineUnionDisplay_impl, name, subtypes)
    {;}

    virtual ~BSQInlineUnionType() {;}
};

std::string heapUnionDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQHeapUnionType : public BSQAbstractType
{
public:
    BSQHeapUnionType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, std::string name, std::set<BSQTypeID> subtypes)
    : BSQAbstractType(tid, tkind, allocinfo, heapUnionDisplay_impl, name, subtypes)
    {;}

    virtual ~BSQHeapUnionType() {;}
};

//Forward type decls for special types we want to refer to in the ops

