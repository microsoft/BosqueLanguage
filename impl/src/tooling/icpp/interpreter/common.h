//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <setjmp.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>
#include <regex>

//TODO: mimalloc
//#include <mimalloc.h>

#define MI_SMALL_SIZE_MAX 2048

inline void* mi_zalloc(size_t bytes)
{
    void* res = malloc(bytes);
    std::fill((uint8_t*)res, ((uint8_t*)res) + bytes, (uint8_t)0);

    return res;
}

inline void* mi_zalloc_small(size_t bytes)
{
    void* res = malloc(bytes);
    std::fill((uint8_t*)res, ((uint8_t*)res) + bytes, (uint8_t)0);

    return res;
}

inline void mi_free(void* mem)
{
    free(mem);
}

////////////////////////////////
//Various sizes
#define BSQ_MAX_STACK 2048

////////////////////////////////
//Asserts

#define BSQ_INTERNAL_ASSERT(C) if(!(C)) { assert(false); }

#ifdef BSQ_DEBUG_BUILD
#define HANDLE_BSQ_ABORT(MSG, F, L, C) { printf("\"%s\" in %s on line %i\n", MSG, F, (int)L); fflush(stdout); longjmp(Environment::g_entrybuff, C); }
#else
#define HANDLE_BSQ_ABORT() { printf("ABORT\n"); longjmp(Environment::g_entrybuff, 5); }
#endif

#ifdef BSQ_DEBUG_BUILD
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT(MSG, (F)->c_str(), L, 2);
#else
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT();
#endif

#ifdef BSQ_DEBUG_BUILD
#define BSQ_LANGUAGE_ABORT(MSG, F, L) HANDLE_BSQ_ABORT(MSG, (F)->c_str(), L, 3)
#else
#define BSQ_LANGUAGE_ABORT(MSG, F, L) HANDLE_BSQ_ABORT()
#endif

////////////////////////////////
//Memory allocator

#if defined(MEM_STATS)
#define ENABLE_MEM_STATS
#define MEM_STATS_OP(X) X
#define MEM_STATS_ARG(X) X
#else
#define MEM_STATS_OP(X)
#define MEM_STATS_ARG(X)
#endif

//Program should not contain any allocations larger than this in a single block 
#define BSQ_ALLOC_MAX_BLOCK_SIZE MI_SMALL_SIZE_MAX

//Min and max bump allocator size
#define BSQ_MIN_NURSERY_SIZE 1048576
#define BSQ_MAX_NURSERY_SIZE 16777216

#define BSQ_MAX_BIG_ALLOC_COUNT 500

//Allocation routines
#ifdef __APPLE__
#define BSQ_STACK_SPACE_ALLOC(SIZE) (SIZE == 0 ? nullptr : alloca(SIZE))
#else
#define BSQ_STACK_SPACE_ALLOC(SIZE) (SIZE == 0 ? nullptr : _alloca(SIZE))
#endif

#define BSQ_BUMP_SPACE_ALLOC(SIZE) mi_zalloc(SIZE)
#define BSQ_BUMP_SPACE_RELEASE(M) mi_free(M)

#define BSQ_FREE_LIST_ALLOC_SMALL(SIZE) mi_zalloc_small(SIZE)
#define BSQ_FREE_LIST_ALLOC(SIZE) mi_zalloc(SIZE)
#define BSQ_FREE_LIST_RELEASE(SIZE, M) mi_free(M)

#define GC_REF_LIST_BLOCK_SIZE_SMALL 32
#define GC_REF_LIST_BLOCK_SIZE_DEFAULT 128

//Header word layout
//high [RC - 40 bits] [MARK - 1 bit] [YOUNG - 1 bit] [TYPEID - 22 bits]

#define GC_MARK_BIT 0x800000
#define GC_YOUNG_BIT 0x400000
#define GC_MARK_MASK 0xFFFFFFFFFF7FFFFF
#define GC_RC_MASK 0xFFFFFFFFFF000000
#define GC_TYPE_ID_MASK 0x3FFFFF
#define GC_REACHABLE_MASK (GC_RC_MASK | GC_MARK_BIT)
#define GC_CLEAR_MARK_MASK (GC_RC_MASK | GC_TYPE_ID_MASK)

typedef uint64_t GC_META_DATA_WORD;
#define GC_MASK_RC(W) (W & GC_RC_MASK)
#define GC_EXTRACT_MARK(W) (W & GC_MARK_BIT)
#define GC_MASK_MARK(W) (W & GC_MARK_MASK)
#define GC_EXTRACT_TYPEID(W) (W & 0x7FFFFF)

#define GC_GET_META_DATA_ADDR(M) ((GC_META_DATA_WORD*)((uint8_t*)M - sizeof(GC_META_DATA_WORD)))
#define GC_LOAD_META_DATA_WORD(ADDR) (*((GC_META_DATA_WORD*)ADDR))
#define GC_SET_META_DATA_WORD(ADDR, W) (*((GC_META_DATA_WORD*)ADDR) = W)

#define GC_TEST_IS_UNREACHABLE(W) (W & GC_REACHABLE_MASK)
#define GC_TEST_IS_ZERO_RC(W) ((W & GC_RC_MASK) == 0)
#define GC_TEST_IS_YOUNG(W) (W & GC_YOUNG_BIT)
#define GC_CLEAR_MARK_BIT(W) (W & GC_CLEAR_MARK_MASK)
#define GC_SET_MARK_BIT(W) (W | GC_MARK_BIT)

#define GC_RC_ETERNAL_INIT ((GC_META_DATA_WORD)0x1000000)
#define GC_RC_ONE ((GC_META_DATA_WORD)0x1000000)
#define GC_INC_RC(W) (W + GC_RC_ONE)
#define GC_DEC_RC(W) (W - GC_RC_ONE)

#define GC_INIT_YOUNG(ADDR, TID) GC_SET_META_DATA_WORD(ADDR, GC_YOUNG_BIT | TID)
#define GC_INIT_OLD_ROOT(ADDR, W) GC_SET_META_DATA_WORD(ADDR, GC_MARK_BIT | GC_EXTRACT_TYPEID(W))
#define GC_INIT_OLD_HEAP(ADDR, W) GC_SET_META_DATA_WORD(ADDR, GC_RC_ONE | GC_EXTRACT_TYPEID(W))

//Access type info + special forwarding pointer mark
#define GET_TYPE_META_DATA_FROM_WORD(W) (*(BSQType::g_typetable + GC_EXTRACT_TYPEID(W)))
#define GET_TYPE_META_DATA_FROM_ADDR(ADDR) GET_TYPE_META_DATA_FROM_WORD(GC_LOAD_META_DATA_WORD(ADDR))
#define GET_TYPE_META_DATA(M) GET_TYPE_META_DATA_FROM_ADDR(GC_GET_META_DATA_ADDR(M))
#define GET_TYPE_META_DATA_AS(T, M) (dynamic_cast<const T*>(GET_TYPE_META_DATA(M)))

#define GC_SET_TYPE_META_DATA_FORWARD_SENTINAL(ADDR) *(ADDR) = 0
#define GC_IS_TYPE_META_DATA_FORWARD_SENTINAL(W) ((W) == 0)
#define GC_GET_FORWARD_PTR(M) *((void**)M)
#define GC_SET_FORWARD_PTR(M, P) *((void**)M) = (void*)P

//Misc operations
#define COMPUTE_REAL_BYTES(M) (GET_TYPE_META_DATA(M)->allocinfo.heapsize + sizeof(GC_META_DATA_WORD))

#define GC_MEM_COPY(DST, SRC, BYTES) std::copy((uint8_t*)SRC, ((uint8_t*)SRC) + BYTES, (uint8_t*)DST)
#define GC_MEM_ZERO(DST, BYTES) std::fill((uint8_t*)DST, ((uint8_t*)DST) + BYTES, (uint8_t)0)

////////////////////////////////
//Storage location ops

//Generic pointer to a storage location that holds a value
typedef void* StorageLocationPtr;

#define IS_INLINE_STRING(S) (*(((uint8_t*)(S)) + 15) != 0)
#define IS_INLINE_BIGNUM(N) false

////////////////////////////////
//Type and GC interaction decls

class BSQType;

enum class BSQTypeKind : uint32_t
{
    Invalid = 0x0,
    Register,
    Struct,
    String,
    BigNum,
    Ref,
    UnionInline,
    UnionRef
};

#define MAX_STRUCT_SIZE 40

#define PTR_FIELD_MASK_SCALAR '1'
#define PTR_FIELD_MASK_PTR '2'
#define PTR_FIELD_MASK_STRING '3'
#define PTR_FIELD_MASK_BIGNUM '4'
#define PTR_FIELD_MASK_UNION '5'
#define PTR_FIELD_MASK_END (char)0

typedef const char* RefMask;

typedef void** (*GCDecOperatorFP)(const BSQType*, void**);
typedef void** (*GCClearMarkOperatorFP)(const BSQType*, void**);
typedef void** (*GCProcessOperatorFP)(const BSQType*, void**);

typedef std::string (*DisplayFP)(const BSQType*, StorageLocationPtr);

typedef uint32_t BSQTypeID;
typedef uint32_t BSQTupleIndex;
typedef uint32_t BSQRecordPropertyID;
typedef uint32_t BSQFieldID;
typedef uint32_t BSQInvokeID;
typedef uint32_t BSQVirtualInvokeID;
typedef uint32_t BSQConstantID;

#define BSQ_TYPE_ID_NONE 0
#define BSQ_TYPE_ID_BOOL 1
#define BSQ_TYPE_ID_NAT 2
#define BSQ_TYPE_ID_INT 3
#define BSQ_TYPE_ID_BIGNAT 4
#define BSQ_TYPE_ID_BIGINT 5
#define BSQ_TYPE_ID_FLOAT 6
#define BSQ_TYPE_ID_DECIMAL 7
#define BSQ_TYPE_ID_RATIONAL 8
#define BSQ_TYPE_ID_STRINGITERATOR 9
#define BSQ_TYPE_ID_STRING 10
#define BSQ_TYPE_ID_BYTEBUFFER 11
#define BSQ_TYPE_ID_ISOTIME 12
#define BSQ_TYPE_ID_LOGICALTIME 13
#define BSQ_TYPE_ID_UUID 14
#define BSQ_TYPE_ID_CONTENTHASH 15
#define BSQ_TYPE_ID_REGEX 16

#define BSQ_TYPE_ID_STRINGREPR 30
#define BSQ_TYPE_ID_LISTREPR 30

#define BSQ_TYPE_ID_BUILTIN_MAX 100

enum class BSQPrimitiveImplTag
{
    Invalid = 0x0,

    validator_accepts,

    string_empty,
    string_append,

    list_size,
    list_empty,
    list_unsafe_get,
    list_fill,
    list_concat2,
    list_haspredcheck,
    list_haspredcheck_idx,
    list_findindexof,
    list_findindexoflast,
    list_findindexof_idx,
    list_findindexoflast_idx,
    list_filter,
    list_filter_idx,
    list_filtertotype,
    list_casttotype,
    list_slice,
    list_map,
    list_map_idx
};
