//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <cstdint>
#include <string>

#define BSQ_MEM_ALIGNMENT 8
#define BSQ_ALIGN_SIZE(ASIZE) (((ASIZE) + 0x7) & 0xFFFFFFFFFFFFFFFC)


//Note POD => API
typedef size_t DATA_KIND_FLAG;
#define DATA_KIND_CLEAR_FLAG 0x0
#define DATA_KIND_API_FLAG 0x1
#define DATA_KIND_POD_FLAG 0x3
#define DATA_KIND_PARSABLE_FLAG 0x4
#define DATA_KIND_ALL_FLAG (DATA_KIND_API_FLAG | DATA_KIND_POD_FLAG | DATA_KIND_PARSABLE_FLAG)
#define DATA_KIND_UNKNOWN_FLAG 0xFF

#define DATA_KIND_COMPUTE(KF, COMP) (((KF) == DATA_KIND_UNKNOWN_FLAG) ? (COMP) : (KF)

#define PTR_FIELD_MASK_SCALAR '1'
#define PTR_FIELD_MASK_PTR '2'
#define PTR_FIELD_MASK_UNION '4'
#define PTR_FIELD_MASK_END (char)0

#define META_DATA_LOAD_DECL(X) const_cast<MetaData*>(&(X))

#define META_DATA_DECLARE_NO_PTR(NAME, TYPE, FLAG, SIZE, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, 0, nullptr, Allocator::MetaData_ComputeSize_Simple, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, DNAME, false }
#define META_DATA_DECLARE_NO_PTR_KEY(NAME, TYPE, FLAG, SIZE, LESSFP, EQFP, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, 0, nullptr, Allocator::MetaData_ComputeSize_Simple, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, DNAME, false }

#define META_DATA_DECLARE_NO_PTR_COLLECTION(NAME, TYPE, FLAG, SIZE, ESIZE, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, ESIZE, -1, 0, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, DNAME, false }
#define META_DATA_DECLARE_NO_PTR_KEY_COLLECTION(NAME, TYPE, FLAG, SIZE, ESIZE, LESSFP, EQFP, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, ESIZE, -1, 0, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, DNAME, false }

#define META_DATA_DECLARE_PTR_PACKED(NAME, TYPE, FLAG, SIZE, PCOUNT, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, PCOUNT, nullptr, Allocator::MetaData_ComputeSize_Simple, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }
#define META_DATA_DECLARE_PTR_PACKED_KEY(NAME, TYPE, FLAG, SIZE, PCOUNT, LESSFP, EQFP, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, PCOUNT, nullptr, Allocator::MetaData_ComputeSize_Simple, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_Packed<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }

#define META_DATA_DECLARE_PTR_PACKED_COLLECTON_DIRECT(NAME, TYPE, FLAG, SIZE, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, sizeof(void*), sizeof(void*) / sizeof(void*), 1, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }
#define META_DATA_DECLARE_PTR_PACKED_COLLECTION_DIRECT_KEY(NAME, TYPE, FLAG, SIZE, LESSFP, EQFP, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, sizeof(void*), sizeof(void*) / sizeof(void*), 1, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_PackedEntries_Direct<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }

#define META_DATA_DECLARE_PTR_PACKED_COLLECTON(NAME, TYPE, FLAG, SIZE, ESIZE, PCOUNT, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, ESIZE, ESIZE / sizeof(void*), PCOUNT, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }
#define META_DATA_DECLARE_PTR_PACKED_COLLECTION_KEY(NAME, TYPE, FLAG, SIZE, ESIZE, PCOUNT, LESSFP, EQFP, CUNIONFP, DISPLAY, DNAME) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, ESIZE, ESIZE / sizeof(void*), PCOUNT, nullptr, Allocator::MetaData_ComputeSize_SimpleCollection, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_Dec>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_Clear>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_ProcessRoot>, Allocator::MetaData_GCOperatorFP_PackedEntries<Allocator::GCOperator_ProcessHeap>, DISPLAY, DNAME, true }

namespace BSQ
{
enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE%%
};

class MetaData;

typedef const char* RefMask;

typedef size_t (*MemSizeFP)(const MetaData*, void*);

typedef bool (*MetaData_RelationalOpFP)(void*, void*);

typedef void (*MetaData_GCDecOperatorFP)(const MetaData*, void**);
typedef void (*MetaData_GCClearMarkOperatorFP)(const MetaData*, void**);
typedef void (*MetaData_GCProcessOperatorFP)(const MetaData*, void**);

typedef void* (*MetaData_UnionBoxToValue)(void*);
typedef void (*MetaData_UnionUnboxFromValue)(void*, void*);

typedef std::wstring (*MetaData_DisplayFP)(void* obj);

/*
//
//TODO use this pattern to setup a vtable object that can be accessed quickly -- this should include vcalls, vfields, vupdates, and vmerges
//
int foo(int x);
typedef int (*foo_ptr)(int);

struct foometa
{
    foo_ptr vfoo;
};

constexpr foometa fm = {foo};
*/

class MetaData
{
public:
    MIRNominalTypeEnum nominaltype;
    uint32_t dataflag;

    uint32_t datasize; //size of the object in it's raw state (excluding any headers)
    int32_t sizeentry; //if this is a container then this is the size of each contained element (0) if not a container
    int32_t sizeadvance; //if this is a container then this is the size (in void* increments) that each entry represents

    uint32_t ptrcount; //if this is a simple packed layout (or contents are simple packed layouts) then this is the number of pointers
    RefMask refmask; //if this is a mixed layout (or contents are mixed layouts) then this is the mask to use

    //Less and Equal operations for the object when it is in boxed form (or null if they are not supported)
    MetaData_RelationalOpFP less;
    MetaData_RelationalOpFP eq;

    //How to do gc ops on the object
    MetaData_GCDecOperatorFP decObj;
    MetaData_GCClearMarkOperatorFP clearObj;
    MetaData_GCProcessOperatorFP processObjRoot;
    MetaData_GCProcessOperatorFP processObjHeap;

    //display function pointer
    MetaData_DisplayFP displayFP;
    const wchar_t* displayname;

    //true if this may have reference fields that need to be processed
    bool hasRefs;

    //true if when stored in a union this is a pointer representation to the heap object
    bool isPtrReprInUnion;

    MetaData_UnionBoxToValue unionBoxToVal;
    MetaData_UnionUnboxFromValue unionUnboxFromVal;

    void* vtable;

    inline bool isFixedMetaData() const
    {
        return this->sizeentry == 0;
    }

    inline size_t getMemorySize(void* obj)
    {
        if(this->isFixedMetaData())
        {
            return this->datasize;
        }
        else
        {   
            size_t elemcount = *((size_t*)obj);
            return this->datasize + BSQ_ALIGN_SIZE(elemcount * this->sizeadvance);
        }
    }

    template <bool isRoot>
    inline MetaData_GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }

    template <>
    inline MetaData_GCProcessOperatorFP getProcessFP<true>() const
    {
        return this->processObjRoot;
    }

    template <>
    inline MetaData_GCProcessOperatorFP getProcessFP<false>() const
    {
        return this->processObjHeap;
    }
};

//%%METADATA_STRUCT_DECLS%%
}

//%%SPECIAL_NAME_BLOCK_BEGIN%%
#define MIRNominalTypeEnum_None MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Bool MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Int MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_BigInt MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Float64 MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_String MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_UUID MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ByteBuffer MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Regex MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Tuple MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Record MIRNominalTypeEnum::Invalid
//%%SPECIAL_NAME_BLOCK_END%%
