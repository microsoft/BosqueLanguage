//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#include <vector>
#include <map>

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

struct BSQTypeSizeInfo
{
    const uint64_t heapsize;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    const uint64_t inlinedatasize; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref and heap union -- and word size for BSQBool)
    const uint64_t assigndatasize; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    const RefMask heapmask; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    const RefMask inlinedmask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must traverse full object
};

struct GCFunctorSet
{
    GCDecOperatorFP fpDecObj;
    GCClearMarkOperatorFP fpClearObj;
    GCProcessOperatorFP fpProcessObjRoot;
    GCProcessOperatorFP fpProcessObjHeap;
};

constexpr GCFunctorSet LEAF_GC_FUNCTOR_SET{ nullptr, nullptr, nullptr, nullptr };
constexpr GCFunctorSet STD_GC_FUNCTOR_SET{ gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl };

struct KeyFunctorSet
{
    KeyEqualFP fpKeyEqual;
    KeyLessFP fpKeyLess;
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
    
    const BSQTypeSizeInfo allocinfo;
    const GCFunctorSet gcops;

    KeyFunctorSet keyops;
    const std::map<BSQVirtualInvokeID, BSQInvokeID> vtable; //TODO: This is slow indirection but nice and simple

    DisplayFP fpDisplay;
    const std::string name;

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name): 
        tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), vtable(vtable), keyops(keyops), fpDisplay(fpDisplay), name(name)
    {;}

    virtual ~BSQType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const = 0;
    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const = 0;

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;

    void vcallExtractFromUnion(StorageLocationPtr src, uint8_t* into) const
    {
        auto tt = SLPTR_LOAD_UNION_INLINE_TYPE(src);
        tt->storeValue((StorageLocationPtr)into, src);
    }
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
    return tt->gcops.fpProcessObjRoot;
}

template <>
inline GCProcessOperatorFP getProcessFP<false>(const BSQType* tt)
{
    return tt->gcops.fpProcessObjHeap;
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

    BSQTupleAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQType(tid, tkind, allocinfo, gcops, vtable, keyops, tupleDisplay_impl, name), maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQTupleAbstractType() {;}
};

class BSQTupleRefType : public BSQTupleAbstractType
{
public:
    //Constructor for leaf type
    BSQTupleRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQTupleAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, name, maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleRefType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(src), offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
    }
};

class BSQTupleStructType : public BSQTupleAbstractType
{
public:
    //Constructor for leaf type
    BSQTupleStructType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQTupleAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, name, maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleStructType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        BSQ_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(src, offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        BSQ_MEM_COPY(trgt, udata, this->allocinfo.assigndatasize);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        BSQ_MEM_COPY(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src, this->allocinfo.assigndatasize);
    }
};

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRecordAbstractType : public BSQType
{
public:
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQTypeID> rtypes;
    const std::vector<size_t> propertyoffsets;

    //Constructor for leaf type
    BSQRecordAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQType(tid, tkind, allocinfo, gcops, vtable, keyops, recordDisplay_impl, name), properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    virtual ~BSQRecordAbstractType() {;}
};

class BSQRecordRefType : public BSQRecordAbstractType
{
public:
    //Constructor for leaf type
    BSQRecordRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQRecordAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, name, properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordRefType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(src), offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
    }
};

class BSQRecordStructType : public BSQRecordAbstractType
{
public:
    //Constructor for leaf type
    BSQRecordStructType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQRecordAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, name, properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordStructType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        BSQ_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(src, offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        BSQ_MEM_COPY(trgt, udata, this->allocinfo.assigndatasize);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        BSQ_MEM_COPY(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src, this->allocinfo.assigndatasize);
    }
};

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEntityAbstractType : public BSQType
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQTypeID> ftypes;
    const std::vector<size_t> fieldoffsets;

    //Constructor for leaf type
    BSQEntityAbstractType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name, std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets):
        BSQType(tid, tkind, allocinfo, gcops, vtable, keyops, fpDisplay, name), fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    virtual ~BSQEntityAbstractType() {;}
};


class BSQEntityRefType : public BSQEntityAbstractType
{
public:
    //Constructor for leaf type
    BSQEntityRefType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name, std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets):
        BSQEntityAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, fpDisplay, name, fields, ftypes, fieldoffsets)
    {;}

    virtual ~BSQEntityRefType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(src), offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
    }
};

class BSQEntityStructType : public BSQEntityAbstractType
{
public:
    //Constructor for leaf type
    BSQEntityStructType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name, std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets): 
        BSQEntityAbstractType(tid, tkind, allocinfo, gcops, vtable, keyops, fpDisplay, name, fields, ftypes, fieldoffsets)
    {;}

    virtual ~BSQEntityStructType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        BSQ_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(src, offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        BSQ_MEM_COPY(trgt, udata, this->allocinfo.assigndatasize);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        BSQ_MEM_COPY(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src, this->allocinfo.assigndatasize);
    }
};

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEphemeralListType : public BSQType
{
public:
    const std::vector<BSQTypeID> etypes;
    const std::vector<size_t> idxoffsets;

    //Constructor for leaf type
    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets): 
        BSQType(tid, tkind, allocinfo, gcops, {}, {0}, entityDisplay_impl, name), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQEphemeralListType() {;}

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        BSQ_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        return SLPTR_INDEX_DATAPTR(src, offset);
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
       assert(false);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }
};


std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQUnionType : public BSQType
{
public:
    const std::vector<BSQTypeID> subtypes;

    BSQUnionType(BSQTypeID tid, BSQTypeKind tkind, BSQTypeSizeInfo allocinfo, DisplayFP fpDisplay, std::string name, std::vector<BSQTypeID> subtypes): 
        BSQType(tid, tkind, allocinfo, {0}, {}, {0}, unionDisplay_impl, name), subtypes(subtypes)
    {;}

    ~BSQUnionType() {;}

    virtual bool isStructStorage() const
    {
        assert(false);
        return true;
    }

    virtual void clearValue(StorageLocationPtr trgt) const override
    {
        assert(false);
    }

    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }

    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override
    {
        assert(false);
        return nullptr;
    }

    virtual void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
       assert(false);
    }

    virtual void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override
    {
        assert(false);
    }
};


