//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>
#include <regex>

#include <vector>
#include <stack>
#include <queue>
#include <deque>
#include <set>
#include <map>

#include <initializer_list>
#include <algorithm>
#include <numeric>
#include <execution>

#define BSQ_INTERNAL_ASSERT(C) if(!(C)) { assert(false); }

#ifdef BSQ_DEBUG_BUILD
#define HANDLE_BSQ_ABORT(MSG, F, L) { wprintf(L"\"%s\" in %s on line %i\n", MSG, F, L); fflush(stdout); exit(1); }
#else
#define HANDLE_BSQ_ABORT() { printf("ABORT\n"); exit(1); }
#endif

#ifdef BSQ_DEBUG_BUILD
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT(MSG, F, L);
#else
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT();
#endif

#ifdef BSQ_DEBUG_BUILD
#define BSQ_LANGUAGE_ABORT(MSG, F, L) HANDLE_BSQ_ABORT(MSG, F, L)
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

//Compute addresses aligned at the given size
#define BSQ_MEM_ALIGNMENT 8
#define BSQ_MEM_ALIGNMENT_MASK 0x7
#define BSQ_ALIGN_SIZE(ASIZE) (((ASIZE) + BSQ_MEM_ALIGNMENT_MASK) & 0xFFFFFFFFFFFFFFF8)

//Program should not contain any allocations larger than this in a single block
#define BSQ_ALLOC_MAX_BLOCK_SIZE 2048

//Min and max bump allocator size
#define BSQ_MIN_NURSERY_SIZE 1048576
#define BSQ_MAX_NURSERY_SIZE 16777216

//Create and release bump space or stack allocations
#ifdef __APPLE__
#define BSQ_BUMP_SPACE_ALLOC(SIZE) aligned_alloc(SIZE, BSQ_MEM_ALIGNMENT)
#define BSQ_STACK_SPACE_ALLOC(SIZE) alloca(SIZE)
#else
#define BSQ_BUMP_SPACE_ALLOC(SIZE) _aligned_malloc(SIZE, BSQ_MEM_ALIGNMENT)
#define BSQ_STACK_SPACE_ALLOC(SIZE) _alloca(SIZE)
#endif

#define BSQ_BUMP_SPACE_RELEASE(SIZE, M) free(M)

//Allocate and release free list values + stack allocate
#ifdef __APPLE__
#define BSQ_FREE_LIST_ALLOC(SIZE) aligned_alloc(SIZE, BSQ_MEM_ALIGNMENT)
#define BSQ_STACK_ALLOCATE(SIZE) alloca(SIZE)
#else
#define BSQ_FREE_LIST_ALLOC(SIZE) _aligned_malloc(SIZE, BSQ_MEM_ALIGNMENT)
#define BSQ_STACK_ALLOCATE(SIZE) _alloca(SIZE)
#endif

#define BSQ_FREE_LIST_RELEASE(SIZE, M) free(M)

//Access type info + special forwarding pointer mark
#define TYPE_INFO_FORWARD_SENTINAL nullptr
#define GET_TYPE_META_DATA(M) ((BSQType*)((uint8_t*)M - sizeof(BSQType*)))
#define GET_TYPE_META_DATA_AS(T, M) ((const T*)GET_TYPE_META_DATA(M))
#define SET_TYPE_META_DATA_FORWARD_SENTINAL(M) *((void**)((uint8_t*)M - sizeof(BSQType*))) = TYPE_INFO_FORWARD_SENTINAL

#define GET_FORWARD_PTR(M) *((void**)M)
#define SET_FORWARD_PTR(M, P) *((void**)M) = (void *)P

//Ref Counting Metadata and operations
typedef uint64_t RCMeta;

#define GC_RC_CLEAR ((uint64_t)0)
#define GC_RC_ETERNAL_INIT ((uint64_t)1)
#define GC_RC_MARK_FROM_ROOT ((uint64_t)(1 << 60))

#define GC_COUNT_GET_MASK 0xFFFFFFFFFFFF
#define GC_MARK_GET_MASK 0xFFFF000000000000

#define GET_RC_HEADER(M) ((RCMeta*)((uint8_t*)M) - (sizeof(RCMeta) + sizeof(BSQType*)))
#define GET_RC_COUNT(M) (*GET_RC_HEADER(M) & GC_COUNT_GET_MASK)
#define GET_RC_MARK(M) (*GET_RC_HEADER(M) & GC_MARK_GET_MASK)

#define INC_RC_HEADER(M) ((*GET_RC_HEADER(M))++)
#define DEC_AND_CHECK_RC_HEADER(M) ((*GET_RC_HEADER(M))-- == GC_RC_CLEAR) 
#define MARK_HEADER_SET(M) (*GET_RC_HEADER(M) = (GET_RC_COUNT(M) | GC_RC_MARK_FROM_ROOT))
#define MARK_HEADER_CLEAR(M) (*GET_RC_HEADER(M) = GC_RC_CLEAR)

//Check if an object is unreachable
#define IS_UNREACHABLE(M) (*GET_RC_HEADER(M) == GC_RC_CLEAR)

//Misc operations
#define IS_BUMP_ALLOCATION(M, BSTART, BEND) ((BSTART <= (uintptr_t)M) & ((uintptr_t)M < BEND))

#define GET_SLAB_BASE(M) ((void*)((uint8_t *)M - sizeof(BSQType*)))
#define GET_FREE_LIST_BASE(M) ((void*)((uint8_t *)M - (sizeof(RCMeta) + sizeof(BSQType*))))

#define COMPUTE_FREE_LIST_BYTES(M) (GET_TYPE_META_DATA(M)->allocinfo.heapsize + sizeof(RCMeta) + sizeof(BSQType*))

#ifdef __APPLE__
#define GC_MEM_COPY(DST, SRC, BYTES) memcpy(DST, SRC, BYTES)
#else
#define GC_MEM_COPY(DST, SRC, BYTES) memcpy_s(DST, BYTES, SRC, BYTES)
#endif

#define GC_MEM_ZERO(DST, BYTES) std::fill((uint8_t*)DST, ((uint8_t*)DST) + BYTES, 0)

////////////////////////////////
//Storage location ops

//Generic pointer to a storage location that holds a value
typedef void* StorageLocationPtr;

#define SLPTR_LOAD_CONTENTS_AS(T, L) (*((T*)L))
#define SLPTR_STORE_CONTENTS_AS(T, L, V) *((T*)L) = V

#define SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(L) (*((void**)L))
#define SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(L, V) *((void**)L) = V

#define SLPTR_LOAD_UNION_INLINE_TYPE(L) (*((const BSQType**)L))
#define SLPTR_LOAD_UNION_INLINE_DATAPTR(L) ((void*)(((uint8_t*)L) + sizeof(BSQType*)))

#define SLPTR_LOAD_UNION_HEAP_TYPE(L) GET_TYPE_META_DATA(*((void**)L))
#define SLPTR_LOAD_UNION_HEAP_DATAPTR(L) (*((void**)L))

#define SLPTR_INDEX_INLINE(SL, I) ((void*)(((uint8_t*)SL) + I))
#define SLPTR_INDEX_HEAP(SL, I) SLPTR_INDEX_INLINE(SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SL), I)

#define SLPTR_STORE_UNION_INLINE_TYPE(L, T) (*((const BSQType**)L) = T)

#define SLPTR_COPY_CONTENTS(TRGTL, SRCL, SIZE) GC_MEM_COPY(TRGTL, SRCL, SIZE)

typedef bool (*KeyEqualFP)(StorageLocationPtr, StorageLocationPtr);
typedef bool (*KeyLessFP)(StorageLocationPtr, StorageLocationPtr);

#define IS_INLINE_STRING(S) (*(((uint8_t*)(S)) + 15) != 0)

////////////////////////////////
//Type and GC interaction decls

class BSQType;

#define PTR_FIELD_MASK_SCALAR '1'
#define PTR_FIELD_MASK_PTR '2'
#define PTR_FIELD_MASK_STRING '3'
#define PTR_FIELD_MASK_UNION '4'
#define PTR_FIELD_MASK_END (char)0

typedef const char* RefMask;

typedef void (*GCDecOperatorFP)(const BSQType*, void**);
typedef void (*GCClearMarkOperatorFP)(const BSQType*, void**);
typedef void (*GCProcessOperatorFP)(const BSQType*, void**);

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
#define BSQ_TYPE_ID_CRYPTOHASH 15
#define BSQ_TYPE_ID_REGEX 16

#define BSQ_TYPE_ID_LIST 20

#define BSQ_TYPE_ID_STRINGREPR 30

#define BSQ_TYPE_ID_BUILTIN_MAX 50

enum class BSQPrimitiveImplTag
{
    Invalid = 0x0,
    validator_accepts,
    string_empty,
    string_append
};
