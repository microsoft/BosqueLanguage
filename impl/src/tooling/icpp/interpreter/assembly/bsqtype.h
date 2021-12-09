//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#include <vector>
#include <map>

////////////////////////////////
//Storage location ops

#define SLPTR_LOAD_CONTENTS_AS(T, L) (*((T*)L))
#define SLPTR_STORE_CONTENTS_AS(T, L, V) *((T*)L) = V

#define SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(L) (*((void**)L))
#define SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(L, V) *((void**)L) = V

#define SLPTR_LOAD_UNION_INLINE_TYPE(L) (*((const BSQType**)L))
#define SLPTR_LOAD_UNION_INLINE_TYPE_AS(T, L) (*((const BSQType**)L))
#define SLPTR_LOAD_UNION_INLINE_DATAPTR(L) ((void*)(((uint8_t*)L) + sizeof(const BSQType*)))

#define SLPTR_STORE_UNION_INLINE_TYPE(T, L) *((const BSQType**)L) = T

#define SLPTR_LOAD_HEAP_TYPE_ANY(L) ((*((void**)L) == nullptr) ? BSQType::g_typeNone : GET_TYPE_META_DATA(*((void**)L)))
#define SLPTR_LOAD_HEAP_TYPE_SOME(L) GET_TYPE_META_DATA(*((void**)L))
#define SLPTR_LOAD_HEAP_TYPE_AS(T, L) ((const T*)SLPTR_LOAD_HEAP_TYPE_SOME(*((void**)L)))

#define SLPTR_LOAD_HEAP_DATAPTR(L) (*((void**)L))

#define SLPTR_INDEX_DATAPTR(SL, I) ((void*)(((uint8_t*)SL) + I))

#define SLPTR_LOAD_CONCRETE_TYPE_FROM_UNION(SRCTYPE, SRC) (SRCTYPE->isInline() ? SLPTR_LOAD_UNION_INLINE_TYPE(SRC) : SLPTR_LOAD_HEAP_TYPE_SOME(SRC))

#define BSQ_MEM_ZERO(TRGTL, SIZE) GC_MEM_ZERO(TRGTL, SIZE)
#define BSQ_MEM_COPY(TRGTL, SRCL, SIZE) GC_MEM_COPY(TRGTL, SRCL, SIZE)

////
//Standard memory function pointer definitions

void gcProcessRootOperator_nopImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_inlineImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_refImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_stringImpl(const BSQType* btype, void** data);
void gcProcessRootOperator_bignumImpl(const BSQType* btype, void** data);

void gcProcessHeapOperator_nopImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_inlineImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_refImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data);
void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data);

void gcDecOperator_nopImpl(const BSQType* btype, void** data);
void gcDecOperator_inlineImpl(const BSQType* btype, void** data);
void gcDecOperator_refImpl(const BSQType* btype, void** data);
void gcDecOperator_stringImpl(const BSQType* btype, void** data);
void gcDecOperator_bignumImpl(const BSQType* btype, void** data);

void gcClearOperator_nopImpl(const BSQType* btype, void** data);
void gcClearOperator_inlineImpl(const BSQType* btype, void** data);
void gcClearOperator_refImpl(const BSQType* btype, void** data);
void gcClearOperator_stringImpl(const BSQType* btype, void** data);
void gcClearOperator_bignumImpl(const BSQType* btype, void** data);

void gcMakeImmortalOperator_nopImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_inlineImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_refImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_stringImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_bignumImpl(const BSQType* btype, void** data);

struct BSQTypeSizeInfo
{
    const uint64_t heapsize;   //number of bytes needed to represent the data (no type ptr) when storing in the heap
    const uint64_t inlinedatasize; //number of bytes needed in storage location for this (includes type tag for inline union -- is the size of a pointer for ref -- and word size for BSQBool)
    const uint64_t assigndatasize; //number of bytes needed to copy when assigning this to a location -- 1 for BSQBool -- others should be same as inlined size

    const RefMask heapmask; //The mask to used to traverse this object during gc (if it is heap allocated) -- null if this is a leaf object -- partial if tailing scalars
    const RefMask inlinedmask; //The mask used to traverse this object as part of inline storage (on stack or inline in an object) -- must cover full size of data
};

struct GCFunctorSet
{
    GCProcessOperatorFP fpProcessObjRoot;
    GCProcessOperatorFP fpProcessObjHeap;
    GCProcessOperatorFP fpDecObj;
    GCProcessOperatorFP fpClearObj;
    GCProcessOperatorFP fpMakeImmortal;
};

constexpr GCFunctorSet REF_GC_FUNCTOR_SET{ gcProcessRootOperator_refImpl, gcProcessHeapOperator_refImpl, gcDecOperator_refImpl, gcClearOperator_refImpl, gcMakeImmortalOperator_refImpl };
constexpr GCFunctorSet STRUCT_LEAF_GC_FUNCTOR_SET{ gcProcessRootOperator_nopImpl, gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcClearOperator_nopImpl, gcMakeImmortalOperator_nopImpl };
constexpr GCFunctorSet STRUCT_STD_GC_FUNCTOR_SET{ gcProcessRootOperator_inlineImpl, gcProcessHeapOperator_inlineImpl, gcDecOperator_inlineImpl, gcClearOperator_inlineImpl, gcMakeImmortalOperator_inlineImpl };
constexpr GCFunctorSet REGISTER_GC_FUNCTOR_SET{ gcProcessRootOperator_nopImpl, gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcClearOperator_nopImpl, gcMakeImmortalOperator_nopImpl };

typedef int (*KeyCmpFP)(const BSQType* btype, StorageLocationPtr, StorageLocationPtr);
constexpr KeyCmpFP EMPTY_KEY_CMP = nullptr;

class BSQField
{
public:
    static const BSQField** g_fieldtable;

    const BSQFieldID fkey;
    const std::string fname;

    const BSQTypeID declaredType;
    const bool isOptional;

    BSQField(BSQFieldID fkey, std::string fname, BSQTypeID declaredType, bool isOptional): 
        fkey(fkey), fname(fname), declaredType(declaredType), isOptional(isOptional)
    {;}
};

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;

    //Well known types
    static const BSQType* g_typeNone;
    static const BSQType* g_typeNothing;
    static const BSQType* g_typeBool;
    static const BSQType* g_typeNat;
    static const BSQType* g_typeInt;
    static const BSQType* g_typeBigNat;
    static const BSQType* g_typeBigInt;
    static const BSQType* g_typeFloat;
    static const BSQType* g_typeDecimal;
    static const BSQType* g_typeRational;

    static const BSQType* g_typeStringKRepr16;
    static const BSQType* g_typeStringKRepr32;
    static const BSQType* g_typeStringKRepr64;
    static const BSQType* g_typeStringKRepr96;
    static const BSQType* g_typeStringKRepr128;
    static const std::pair<size_t, const BSQType*> g_typeStringKCons[5];

    static const BSQType* g_typeStringTreeRepr;
    static const BSQType* g_typeStringSliceRepr;

    static const BSQType* g_typeString;

    static const BSQType* g_typeByteBufferLeaf;
    static const BSQType* g_typeByteBufferNode;
    static const BSQType* g_typeByteBuffer;
    static const BSQType* g_typeISOTime;
    static const BSQType* g_typeLogicalTime;
    static const BSQType* g_typeUUID;
    static const BSQType* g_typeContentHash;
    static const BSQType* g_typeRegex;

    const BSQTypeID tid;
    const BSQTypeLayoutKind tkind;
    
    const BSQTypeSizeInfo allocinfo;
    const GCFunctorSet gcops;

    KeyCmpFP fpkeycmp;
    const std::map<BSQVirtualInvokeID, BSQInvokeID> vtable; //TODO: This is slow indirection but nice and simple

    DisplayFP fpDisplay;
    const std::string name;

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name): 
        tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), vtable(vtable), fpkeycmp(fpkeycmp), fpDisplay(fpDisplay), name(name)
    {;}

    virtual ~BSQType() {;}

    inline bool isLeaf() const
    {
        return this->allocinfo.heapmask == nullptr;
    }

    virtual void clearValue(StorageLocationPtr trgt) const = 0;
    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const = 0;

    virtual void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
    virtual void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
};

template <typename T>
class BSQRegisterType : public BSQType
{
public:
    BSQRegisterType(BSQTypeID tid, uint64_t datasize, const RefMask imask, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name): 
        BSQType(tid, BSQTypeLayoutKind::Register, { std::max((uint64_t)sizeof(void*), datasize), std::max((uint64_t)sizeof(void*), datasize), datasize, nullptr, imask }, REGISTER_GC_FUNCTOR_SET, {}, fpkeycmp, fpDisplay, name)
    {;}

    virtual ~BSQRegisterType() {;}

    void storeValueDirect(StorageLocationPtr trgt, T v) const
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, v);
    }

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

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), SLPTR_LOAD_CONTENTS_AS(T, src));
    }
};

class BSQRefType : public BSQType
{
public:
    BSQRefType(BSQTypeID tid, uint64_t heapsize, const RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name):  
        BSQType(tid, BSQTypeLayoutKind::Ref, { heapsize, sizeof(void*), sizeof(void*), heapmask, "2" }, REF_GC_FUNCTOR_SET, vtable, fpkeycmp, fpDisplay, name)
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

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final;
    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final;
};

class BSQStructType : public BSQType
{
public:
    BSQStructType(BSQTypeID tid, uint64_t datasize, const RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name, bool norefs): 
        BSQType(tid, BSQTypeLayoutKind::Struct, { datasize, datasize, datasize, nullptr, imask }, norefs ? STRUCT_LEAF_GC_FUNCTOR_SET : STRUCT_STD_GC_FUNCTOR_SET, vtable, fpkeycmp, fpDisplay, name)
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

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final;
    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final;
};

template <typename T>
class BSQBigNumType : public BSQType
{
public:
    BSQBigNumType(BSQTypeID tid, uint64_t datasize, const RefMask imask, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name): 
        BSQType(tid, BSQTypeKind::BigNum, { datasize, datasize, datasize, nullptr, imask }, REGISTER_GC_FUNCTOR_SET, {}, fpkeycmp, fpDisplay, __std_fs_read_name_from_reparse_data_buffer)
    {;}

    virtual ~BSQBigNumType() {;}

    void storeValueDirect(StorageLocationPtr trgt, T v) const
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, v);
    }

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
        BSQ_INTERNAL_ASSERT(false);
        return nullptr;
    }

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_CONTENTS_AS(T, trgt, SLPTR_LOAD_CONTENTS_AS(T, SLPTR_LOAD_UNION_INLINE_DATAPTR(src)));
    }

    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
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
    BSQ_INTERNAL_ASSERT(false);
    return nullptr;
}

template <>
inline GCProcessOperatorFP getProcessFP<true>(const BSQType* tt)
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
    BSQTupleRefType(BSQTypeID tid, uint64_t heapsize, const RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets):
        BSQRefType(tid, heapsize, heapmask, vtable, EMPTY_KEY_CMP, tupleDisplay_impl, name),
        BSQTupleInfo(maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleRefType() {;}
};

class BSQTupleStructType : public BSQStructType, public BSQTupleInfo
{
public:
    BSQTupleStructType(BSQTypeID tid, uint64_t datasize, RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, BSQTupleIndex maxIndex, std::vector<BSQTypeID> ttypes, std::vector<size_t> idxoffsets, bool norefs):
        BSQStructType(tid, datasize, imask, vtable, EMPTY_KEY_CMP, tupleDisplay_impl, name, norefs),
        BSQTupleInfo(maxIndex, ttypes, idxoffsets)
    {;}

    virtual ~BSQTupleStructType() {;}
};

std::string recordDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQRecordInfo
{
public:
    static std::map<BSQRecordPropertyID, std::string> g_propertynamemap;

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
    BSQRecordRefType(BSQTypeID tid, uint64_t heapsize, const RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets):
        BSQRefType(tid, heapsize, heapmask, vtable, EMPTY_KEY_CMP, recordDisplay_impl, name),
        BSQRecordInfo(properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordRefType() {;}
};

class BSQRecordStructType : public BSQStructType, public BSQRecordInfo
{
public:
    BSQRecordStructType(BSQTypeID tid, uint64_t datasize, const RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, std::vector<BSQRecordPropertyID> properties, std::vector<BSQTypeID> rtypes, std::vector<size_t> propertyoffsets, bool norefs):
        BSQStructType(tid, datasize, imask, vtable, EMPTY_KEY_CMP, recordDisplay_impl, name, norefs),
        BSQRecordInfo(properties, rtypes, propertyoffsets)
    {;}

    virtual ~BSQRecordStructType() {;}
};

std::string entityDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEntityInfo
{
public:
    const std::vector<BSQFieldID> fields;
    const std::vector<size_t> fieldoffsets;
    const std::optional<BSQVirtualInvokeID> consfunc;
    const std::vector<BSQFieldID> consfields;

    BSQEntityInfo(std::vector<BSQFieldID> fields, std::vector<size_t> fieldoffsets, std::optional<BSQInvokeID> consfunc, std::vector<BSQFieldID> consfields):
        fields(fields), fieldoffsets(fieldoffsets), consfunc(consfunc), consfields(consfields)
    {;}

    virtual ~BSQEntityInfo() {;}
};

class BSQEntityRefType : public BSQRefType, public BSQEntityInfo
{
public:
    BSQEntityRefType(BSQTypeID tid, uint64_t heapsize, const RefMask heapmask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, std::vector<BSQFieldID> fields, std::vector<size_t> fieldoffsets, std::optional<BSQInvokeID> consfunc, std::vector<BSQFieldID> consfields):
        BSQRefType(tid, heapsize, heapmask, vtable, EMPTY_KEY_CMP, entityDisplay_impl, name),
        BSQEntityInfo(fields, fieldoffsets, consfunc, consfields)
    {;}

    virtual ~BSQEntityRefType() {;}
};

class BSQEntityStructType : public BSQStructType, public BSQEntityInfo
{
public:
    BSQEntityStructType(BSQTypeID tid, uint64_t datasize, const RefMask imask, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, std::string name, bool norefs, std::vector<BSQFieldID> fields, std::vector<size_t> fieldoffsets, std::optional<BSQInvokeID> consfunc, std::vector<BSQFieldID> consfields): 
        BSQStructType(tid, datasize, imask, vtable, EMPTY_KEY_CMP, entityDisplay_impl, name, norefs),
        BSQEntityInfo(fields, fieldoffsets, consfunc, consfields)
    {;}

    virtual ~BSQEntityStructType() {;}
};

std::string ephemeralDisplay_impl(const BSQType* btype, StorageLocationPtr data);

class BSQEphemeralListType : public BSQStructType
{
public:
    const std::vector<BSQTypeID> etypes;
    const std::vector<size_t> idxoffsets;

    BSQEphemeralListType(BSQTypeID tid, uint64_t datasize, const RefMask imask, std::string name, std::vector<BSQTypeID> etypes, std::vector<size_t> idxoffsets, bool norefs): 
        BSQStructType(tid, datasize, imask, {}, nullptr, ephemeralDisplay_impl, name, norefs), etypes(etypes), idxoffsets(idxoffsets)
    {;}

    virtual ~BSQEphemeralListType() {;}
};

std::string unionDisplay_impl(const BSQType* btype, StorageLocationPtr data);
int unionInlineKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);
int unionRefKeyCmp_impl(const BSQType* btype, StorageLocationPtr data1, StorageLocationPtr data2);

class BSQUnionType : public BSQType
{
public:
    const std::vector<BSQTypeID> subtypes;

     BSQUnionType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, KeyCmpFP fpkeycmp, std::string name, std::vector<BSQTypeID> subtypes): 
        BSQType(tid, tkind, allocinfo, {0}, {}, fpkeycmp, unionDisplay_impl, name), subtypes(subtypes)
    {;}

    virtual ~BSQUnionType() {;}

    virtual bool isInline() const = 0;
};

class BSQUnionInlineType : public BSQUnionType
{
public:
    BSQUnionInlineType(BSQTypeID tid, uint64_t datasize, const RefMask imask, std::string name, std::vector<BSQTypeID> subtypes): 
        BSQUnionType(tid, BSQTypeLayoutKind::UnionInline, { datasize, datasize, datasize, nullptr, imask }, unionInlineKeyCmp_impl, name, subtypes)
    {;}

    virtual ~BSQUnionInlineType() {;}

    bool isInline() const override final
    {
        return true;
    }

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
       return (SLPTR_LOAD_UNION_INLINE_TYPE(src))->indexStorageLocationOffset(SLPTR_LOAD_UNION_INLINE_DATAPTR(src), offset);
    }

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
       assert(false);
    }

    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        assert(false);
    }
};

class BSQUnionRefType : public BSQUnionType
{
public:
    BSQUnionRefType(BSQTypeID tid, std::string name, std::vector<BSQTypeID> subtypes): 
        BSQUnionType(tid, BSQTypeLayoutKind::UnionRef, { sizeof(void*), sizeof(void*), sizeof(void*), nullptr, "2" }, unionRefKeyCmp_impl, name, subtypes)
    {;}

    virtual ~BSQUnionRefType() {;}

    bool isInline() const override final
    {
        return false;
    }

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

    void extractFromInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        auto udata = SLPTR_LOAD_UNION_INLINE_DATAPTR(src);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(trgt, SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(udata));
    }

    void injectIntoInlineUnion(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        SLPTR_STORE_UNION_INLINE_TYPE(this, trgt);
        SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(trgt), src);
    }
};


