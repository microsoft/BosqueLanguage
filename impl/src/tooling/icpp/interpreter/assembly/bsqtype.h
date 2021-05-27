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
void** gcDecOperator_registerImpl(const BSQType* btype, void** data);
void** gcDecOperator_maskImpl(const BSQType* btype, void** data);
void** gcDecOperator_stringImpl(const BSQType* btype, void** data);
void** gcDecOperator_bignumImpl(const BSQType* btype, void** data);

void** gcClearOperator_registerImpl(const BSQType* btype, void** data);
void** gcClearOperator_maskImpl(const BSQType* btype, void** data);
void** gcClearOperator_stringImpl(const BSQType* btype, void** data);
void** gcClearOperator_bignumImpl(const BSQType* btype, void** data);

void** gcProcessRootOperator_registerImpl(const BSQType* btype, void** data);
void** gcProcessRootOperator_maskImpl(const BSQType* btype, void** data);
void** gcProcessRootOperator_stringImpl(const BSQType* btype, void** data);
void** gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data);

void** gcProcessHeapOperator_registerImpl(const BSQType* btype, void** data);
void** gcProcessHeapOperator_maskImpl(const BSQType* btype, void** data);
void** gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data);
void** gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data);

struct BSQTypeSizeInfo
{
    const uint64_t heapsize;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    const uint64_t inlinedatasize; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
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
constexpr GCFunctorSet REGISTER_FUNCTOR_SET{ gcDecOperator_registerImpl, gcClearOperator_registerImpl, gcProcessRootOperator_registerImpl, gcProcessHeapOperator_registerImpl };
constexpr GCFunctorSet MASK_GC_FUNCTOR_SET{ gcDecOperator_maskImpl, gcClearOperator_maskImpl, gcProcessRootOperator_maskImpl, gcProcessHeapOperator_maskImpl };

struct KeyFunctorSet
{
    KeyEqualFP fpKeyEqual;
    KeyLessFP fpKeyLess;
};

constexpr KeyFunctorSet EMPTY_KEY_FUNCTOR_SET{ nullptr, nullptr };

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;
    static std::map<BSQRecordPropertyID, std::string> g_propertymap;
    static std::map<BSQFieldID, std::string> g_fieldmap;

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

    static void vcallExtractFromUnion(StorageLocationPtr src, uint8_t* into)
    {
        auto tt = SLPTR_LOAD_UNION_INLINE_TYPE(src);
        tt->storeValue((StorageLocationPtr)into, src);
    }
};

class BSQStructType : public BSQType
{
public:
    BSQStructType(BSQTypeID tid, uint64_t datasize, RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name): 
        BSQType(tid, BSQTypeKind::Struct, { datasize, datasize, datasize, nullptr, imask }, MASK_GC_FUNCTOR_SET, vtable, keyops, fpDisplay, name)
    {;}

    virtual ~BSQStructType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        BSQ_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final 
    {
        return SLPTR_INDEX_DATAPTR(src, offset);
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        BSQ_MEM_COPY(trgt, udata, this->allocinfo.assigndatasize);
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        BSQ_MEM_COPY(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src, this->allocinfo.assigndatasize);
    }
};

class BSQRefType : public BSQType
{
public:
    BSQRefType(BSQTypeID tid, uint64_t heapsize, RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name):  
        BSQType(tid, BSQTypeKind::Ref, { heapsize, sizeof(void*), sizeof(void*), heapmask, "2" }, heapmask == nullptr ? LEAF_GC_FUNCTOR_SET : MASK_GC_FUNCTOR_SET, vtable, keyops, fpDisplay, name)
    {;}

    virtual ~BSQRefType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, nullptr);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(src));
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        return SLPTR_INDEX_DATAPTR(SLPTR_LOAD_HEAP_DATAPTR(src), offset);
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
    }
};

template <typename T>
class BSQRegisterType : public BSQType
{
public:
    BSQRegisterType(BSQTypeID tid, uint64_t datasize, RefMask imask, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name): 
        BSQType(tid, BSQTypeKind::Register, { std::max((uint64_t)sizeof(void*), datasize), std::max((uint64_t)sizeof(void*), datasize), datasize, nullptr, imask }, REGISTER_GC_FUNCTOR_SET, {}, keyops, fpDisplay, name)
    {;}

    virtual ~BSQRegisterType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, sizeof(T));
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, src));
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(T, src));
    }
};

template <typename T>
class BSQBigNumType : public BSQType
{
public:
    BSQBigNumType(BSQTypeID tid, uint64_t datasize, RefMask imask, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name): 
        BSQBigNumType(tid, BSQTypeKind::BigNum, { datasize, datasize, datasize, nullptr, imask }, REGISTER_GC_FUNCTOR_SET, {}, keyops, fpDisplay, name)
    {;}

    virtual ~BSQBigNumType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, sizeof(T));
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, src));
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(T, src));
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

class BSQTupleInfo
{
public:
    BSQTupleIndex maxIndex;
    std::vector<BSQTypeID> ttypes;
    std::vector<size_t> idxoffsets;

    BSQTupleInfo(BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        maxIndex(maxIndex), ttypes(ttypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQTupleInfo() {;}
};

class BSQTupleRefType : public BSQRefType, public BSQTupleInfo
{
public:
    BSQTupleRefType(BSQTypeID tid, uint64_t heapsize, RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQRefType(tid, heapsize, heapmask, vtable, keyops, tupleDisplay_impl, name),
        BSQTupleInfo(maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleRefType() {;}
};

class BSQTupleStructType : public BSQStructType, public BSQTupleInfo
{
public:
    BSQTupleStructType(BSQTypeID tid, uint64_t datasize, RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQStructType(tid, datasize, imask, vtable, keyops, tupleDisplay_impl, name),
        BSQTupleInfo(maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleStructType() {;}
};

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRecordInfo
{
public:
    const std::vector<BSQRecordPropertyID> properties;
    const std::vector<BSQTypeID> rtypes;
    const std::vector<size_t> propertyoffsets;

    BSQRecordInfo(std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        properties(properties), rtypes(rtypes), propertyoffsets(propertyoffsets)
    {;}

    virtual ~BSQRecordInfo() {;}
};

class BSQRecordRefType : public BSQRefType, public BSQRecordInfo
{
public:
    BSQRecordRefType(BSQTypeID tid, uint64_t heapsize, RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQRefType(tid, heapsize, heapmask, vtable, keyops, recordDisplay_impl, name),
        BSQRecordInfo(properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordRefType() {;}
};

class BSQRecordStructType : public BSQStructType, public BSQRecordInfo
{
public:
    BSQRecordStructType(BSQTypeID tid, uint64_t datasize, RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQStructType(tid, datasize, imask, vtable, keyops, recordDisplay_impl, name),
        BSQRecordInfo(properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordStructType() {;}
};

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEntityInfo
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<BSQTypeID> ftypes;
    const std::vector<size_t> fieldoffsets;

    BSQEntityInfo(std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets):
        fields(fields), ftypes(ftypes), fieldoffsets(fieldoffsets)
    {;}

    virtual ~BSQEntityInfo() {;}
};


class BSQEntityRefType : public BSQRefType, public BSQEntityInfo
{
public:
    BSQEntityRefType(BSQTypeID tid, uint64_t heapsize, RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, std::string name, std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets):
        BSQRefType(tid, heapsize, heapmask, vtable, keyops, entityDisplay_impl, name),
        BSQEntityInfo(fields, ftypes, fieldoffsets)
    {;}

    virtual ~BSQEntityRefType() {;}
};

class BSQEntityStructType : public BSQStructType, public BSQEntityInfo
{
public:
    BSQEntityStructType(BSQTypeID tid, uint64_t datasize, RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyFunctorSet keyops, DisplayFP fpDisplay, std::string name, std::vector<BSQFieldID> fields, std::vector<BSQTypeID> ftypes, std::vector<size_t> fieldoffsets): 
        BSQStructType(tid, datasize, imask, vtable, keyops, entityDisplay_impl, name),
        BSQEntityInfo(fields, ftypes, fieldoffsets)
    {;}

    virtual ~BSQEntityStructType() {;}
};

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEphemeralListType : public BSQStructType
{
public:
    const std::vector<BSQTypeID> etypes;
    const std::vector<size_t> idxoffsets;

    BSQEphemeralListType(BSQTypeID tid, BSQTypeKind tkind, uint64_t datasize, RefMask imask, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets): 
        BSQStructType(tid, datasize, imask, {}, EMPTY_KEY_FUNCTOR_SET, ephemeralDisplay_impl, name), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQEphemeralListType() {;}
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

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, this->allocinfo.assigndatasize);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        BSQ_MEM_COPY(trgt, src, this->allocinfo.assigndatasize);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }

    void extractFromUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
       assert(false);
    }

    void injectIntoUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        assert(false);
    }
};


