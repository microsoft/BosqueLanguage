//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"

class Allocator;

struct GCStackEntry
{
    void** refframep;
    uint32_t refslots;

    void** mixedframep;
    RefMask mask;
};

class GCStack
{
public:
    static GCStackEntry frames[8192];
    static uint32_t stackp;

    inline static void pushFrame(void** reffp, uint32_t refslots, void** structfp, RefMask mask)
    {
        if (GCStack::stackp >= 8192)
        {
            printf("Out-Of-Stack\n");
            exit(1);
        }

        GCStack::frames[GCStack::stackp++] = { reffp, refslots, structfp, mask };
    }

    inline static void popFrame()
    {
        GCStack::stackp--;
    }
};

class GCOperator
{
private:
    Allocator *alloc;

public:
    GCOperator(Allocator *alloc) : alloc(alloc) { ; }

    void collect();
};

//A class that implements our bump pointer nursery space
class NewSpaceAllocator
{
private:
    //We inline the fields for the current/end of the block that we are allocating from
    uint8_t *m_currPos;
    uint8_t *m_endPos;

    size_t m_allocsize;
    uint8_t *m_block;

    GCOperator gc;

#ifdef ENABLE_MEM_STATS
    size_t totalalloc;
#endif

    void setAllocBlock(size_t asize)
    {
        this->m_allocsize = asize;
        this->m_block = (uint8_t*)BSQ_BUMP_SPACE_ALLOC(asize);
        GC_MEM_ZERO(this->m_block, asize);

        this->m_currPos = this->m_block;
        this->m_endPos = this->m_block + asize;
    }

    void resizeAllocatorAsNeeded(size_t rcalloc)
    {
        bool shouldgrow = this->m_allocsize < BSQ_MAX_NURSERY_SIZE && this->m_allocsize < rcalloc * 0.5;
        bool shouldshrink = BSQ_MIN_NURSERY_SIZE < this->m_allocsize && rcalloc < this->m_allocsize;

        if (!(shouldgrow || shouldshrink))
        {
            GC_MEM_ZERO(this->m_block, this->m_allocsize);
        }
        else
        {
            free(this->m_block);
            if (shouldgrow)
            {
                this->setAllocBlock(2 * this->m_allocsize);
            }
            else
            {
                this->setAllocBlock(this->m_allocsize / 2);
            }
        }
    }

public:
    NewSpaceAllocator(Allocator* alloc) : m_block(nullptr), gc(alloc)
    {
        MEM_STATS_OP(this->totalalloc = 0);

        this->setAllocBlock(BSQ_MIN_NURSERY_SIZE);
    }

    ~NewSpaceAllocator()
    {
        BSQ_BUMP_SPACE_RELEASE(this->m_allocsize, this->m_block);
    }

    inline uintptr_t getBumpStartAddr() const { return (uintptr_t)this->m_block; }
    inline uintptr_t getBumpEndAddr() const { return (uintptr_t)this->m_currPos; }

    void postGCProcess(size_t rcmem)
    {
        this->resizeAllocatorAsNeeded(rcmem);

        this->m_currPos = this->m_block;
        this->m_endPos = this->m_block + this->m_allocsize;
    }

    size_t currentAllocatedBytes() const
    {
        return (this->m_currPos - this->m_block);
    }

    //Return do a GC and return uint8_t* of given rsize from the bumplist implementation
    uint8_t* allocateBumpSlow(size_t rsize)
    {
        //Note this is technically UB!!!!
        MEM_STATS_OP(this->totalalloc += (this->m_currPos - this->m_block));

        this->gc.collect();

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }

    //Return uint8_t* of given asize + sizeof(MetaData*)
    inline uint8_t* allocateDynamicSize(size_t asize)
    {
        size_t rsize = asize + sizeof(BSQType*);
        assert(rsize & BSQ_MEM_ALIGNMENT_MASK == 0x0);
        assert(rsize < BSQ_ALLOC_MAX_BLOCK_SIZE);

        uint8_t *res = this->m_currPos;
        this->m_currPos += rsize;

        //Note this is technically UB!!!!
        if (this->m_currPos <= this->m_endPos)
        {
            return res;
        }
        else
        {
            return this->allocateBumpSlow(rsize);
        }
    }

    inline void ensureSpace(size_t required)
    {
        if (this->m_currPos + required > this->m_endPos)
        {
            this->gc.collect();
        }
    }

    inline uint8_t* allocateSafe(size_t asize)
    {
        size_t rsize = asize + sizeof(BSQType*);
        assert(rsize & BSQ_MEM_ALIGNMENT_MASK == 0x0);
        assert(this->m_currPos + rsize <= this->m_endPos);

        uint8_t *res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
};

//A class that implements our old reference counting space
class OldSpaceAllocator
{
private:
    //
    //We may want to tie into a nicer free list impl here
    //

    size_t livealloc;

#ifdef ENABLE_MEM_STATS
    size_t totalalloc;
#endif

public:
    OldSpaceAllocator() : livealloc(0)
    {
        MEM_STATS_OP(this->totalalloc = 0);
    }

    ~OldSpaceAllocator()
    {
        ;
    }

    inline size_t currentAllocatedBytes() const
    {
        return this->livealloc;
    }

    inline uint8_t* allocateSizeFixed(size_t size)
    {
        size_t tsize = sizeof(RCMeta) + sizeof(BSQType*) + size;
        assert(tsize & BSQ_MEM_ALIGNMENT_MASK == 0x0);

        MEM_STATS_OP(this->totalalloc += tsize);

        uint8_t *rr = (uint8_t *)BSQ_FREE_LIST_ALLOC(tsize);
        *((RCMeta*)rr) = GC_RC_CLEAR;

        this->livealloc += tsize;

        return (rr + sizeof(RCMeta));
    }

    inline void release(void *m)
    {
        size_t bytes = COMPUTE_FREE_LIST_BYTES(m);
        this->livealloc -= bytes;
    }
};

class Allocator
{
public:
    static Allocator GlobalAllocator;

private:
    NewSpaceAllocator nsalloc;
    OldSpaceAllocator osalloc;

    std::deque<void**> tempRoots;

    std::vector<void*> maybeZeroCounts;

    uintptr_t bstart;
    uintptr_t bend;
    std::queue<void*> worklist;

    std::queue<void*> releaselist;

#ifdef ENABLE_MEM_STATS
    size_t gccount;
    size_t promotedbytes;
    size_t maxheap;
#endif

    ////////
    //Operations GC mark and move
    template <bool isRoot>
    void* moveBumpObjectToRCSpace(void* obj)
    {
        const BSQType* ometa = GET_TYPE_META_DATA(obj);
        size_t osize = ometa->allocsize;
        void* nobj = this->osalloc.allocateSizeFixed(osize);

        MEM_STATS_OP(this->promotedbytes += ometa->datasize + sizeof(MetaData *));

        GC_MEM_COPY(nobj, GET_TYPE_META_DATA(obj), osize + sizeof(BSQType*));
        if (!ometa->isLeafType)
        {
            this->worklist.push(nobj);
        }

        void* robj = (void*)((uint8_t*)nobj + sizeof(BSQType*));
        if constexpr (isRoot)
        {
            MARK_HEADER_SET(robj);
            this->maybeZeroCounts.push_back(robj);
        }
        else
        {
            INC_RC_HEADER(robj);
        }

        SET_TYPE_META_DATA_FORWARD_SENTINAL(obj);
        SET_FORWARD_PTR(obj, robj);

        return robj;
    }

public:
    template <bool isRoot>
    inline static void gcProcessSlot(void** slot)
    {
        void*v = *slot;
        if (v != nullptr)
        {
            if (IS_BUMP_ALLOCATION(v, Allocator::GlobalAllocator.bstart, Allocator::GlobalAllocator.bend))
            {
                *slot = Allocator::GlobalAllocator.moveBumpObjectToRCSpace<isRoot>(v);
            }
            else
            {
                if constexpr (isRoot)
                {
                    MARK_HEADER_SET(v);
                }
                else
                {
                    INC_RC_HEADER(v);
                }
            }
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlots(void** slots, size_t limit)
    {
        void** cslot = slots;
        void* end = slots + limit;

        while (cslot != end)
        {
            Allocator::gcProcessSlot<isRoot>(cslot++);
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlotWithString(void** slot)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcProcessSlot(slot);
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots++));
        umeta->getProcessFP<isRoot>()(umeta, slots);
    }

    template <bool isRoot>
    inline static void gcProcessSlotsWithMask(void** slots, RefMask mask)
    {
        void** cslot = slots;
        RefMask cmaskop = mask;

        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_SCALAR:
                    cslot++;
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcProcessSlot<isRoot>(cslot++);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcProcessSlotWithString<isRoot>(cslot++);
                    break;
                default:
                    Allocator::gcProcessSlotsWithUnion<isRoot>(cslot++);
                    break;
            }
        }
    }

    ////////
    //Operations GC decrement
    inline static void gcDecrement(void* obj)
    {
        if (obj != nullptr)
        {
            if (DEC_AND_CHECK_RC_HEADER(obj))
            {
                Allocator::GlobalAllocator.releaselist.push(obj);
            }
        }
    }

    inline static void gcDecrementSlots(void** slots, size_t limit)
    {
        void **cslot = slots;
        void *end = slots + limit;

        while (cslot != end)
        {
            Allocator::gcDecrement(*cslot++);
        }
    }

    inline static void gcDecrementString(void** slot)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcDecrement(*slot);
        }
    }

    inline static void gcDecrementSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots++));
        umeta->fpDecObj(umeta, slots);
    }

    inline static void gcDecSlotsWithMask(void** slots, const char* mask)
    {
        void** cslot = slots;
        const char* cmaskop = mask;

        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_SCALAR:
                    cslot++;
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcDecrement(*cslot++);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcDecrementString(cslot++);
                    break;
                default:
                    Allocator::gcDecrementSlotsWithUnion(cslot++);
                    break;
            }
        }
    }

    ////////
    //Operations GC mark clear
    inline static void gcClearMark(void *obj)
    {
        if (obj != nullptr)
        {
            MARK_HEADER_CLEAR(obj);
        }
    }

    inline static void gcClearMarkSlots(void** slots, size_t limit)
    {
        void **cslot = slots;
        void *end = slots + limit;

        while (cslot != end)
        {
            Allocator::gcClearMark(*cslot++);
        }
    }

    inline static void gcClearMarkString(void** slot)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcClearMark(*slot);
        }
    }

    inline static void gcClearMarkSlotsWithUnion(void** slots)
    {
        const BSQType *umeta = ((const BSQType*)(*slots++));
        umeta->fpClearObj(umeta, slots);
    }

    inline static void gcClearMarkSlotsWithMask(void** slots, const char* mask)
    {
        void** cslot = slots;
        const char* cmaskop = mask;

        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_SCALAR:
                    cslot++;
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcClearMark(*cslot++);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcClearMarkString(cslot++);
                    break;
                default:
                    Allocator::gcClearMarkSlotsWithUnion(cslot++);
                    break;
            }
        }
    }

private:
    ////////
    //GC algorithm
    static void processRoots()
    {
        for (size_t i = 0; i < GCStack::stackp; ++i)
        {
            void** slots = GCStack::frames[i].refframep;
            uint32_t slotct = GCStack::frames[i].refslots;
            for (size_t j = 0; j < slotct; ++j)
            {
                Allocator::gcProcessSlot<true>(slots + j);
            }

            if (GCStack::frames[i].mixedframep != nullptr)
            {
                Allocator::gcProcessSlotsWithMask<true>(GCStack::frames[i].mixedframep, GCStack::frames[i].mask);
            }
        }

        for (auto iter = Allocator::GlobalAllocator.tempRoots.begin(); iter != Allocator::GlobalAllocator.tempRoots.end(); ++iter)
        {
            Allocator::gcProcessSlot<true>(*iter);
        }
    }

    void processHeap()
    {
        while (!this->worklist.empty())
        {
            void* obj = this->worklist.front();
            this->worklist.pop();

            const BSQType* umeta = GET_TYPE_META_DATA(obj);

            assert(!umeta->isLeafType);

            if(umeta->ptrcount != 0)
            {
                Allocator::gcProcessSlots<false>((void**)obj, umeta->ptrcount);
            }
            else if(umeta->refmask != nullptr)
            {
                Allocator::gcProcessSlotsWithMask<false>((void**)obj, umeta->refmask);
            }
            else
            {
                umeta->getProcessFP<false>()(umeta, (void**)obj);
            }
        }
    }

    void checkMaybeZeroCountList()
    {
        auto biter = this->maybeZeroCounts.begin();
        auto eiter = this->maybeZeroCounts.end();
        for (auto iter = biter; iter < eiter; iter++)
        {
            if (IS_UNREACHABLE(*iter))
            {
                this->releaselist.push(*iter);
                *iter = nullptr;
            }
            else
            {
                if (GET_RC_COUNT(*iter) != 0)
                {
                    *iter = nullptr;
                }
            }
        }

        if (!this->releaselist.empty())
        {
            this->maybeZeroCounts.erase(biter, std::remove(biter, eiter, nullptr));
        }
    }

    void processRelease()
    {
        while (!this->releaselist.empty())
        {
            void* obj = this->releaselist.front();
            this->releaselist.pop();

            const BSQType* umeta = GET_TYPE_META_DATA(obj);
            if (!umeta->isLeafType)
            {
                umeta->fpDecObj(umeta, (void**)obj);
            }

            this->osalloc.release(obj);
        }
    }

    void clearAllMarkRoots()
    {
        for (size_t i = 0; i < GCStack::stackp; ++i)
        {
            void **slots = GCStack::frames[i].refframep;
            uint32_t slotct = GCStack::frames[i].refslots;
            for (size_t j = 0; j < slotct; ++j)
            {
                Allocator::gcClearMark(slots + j);
            }

            if (GCStack::frames[i].mixedframep != nullptr)
            {
                Allocator::gcClearMarkSlotsWithMask(GCStack::frames[i].mixedframep, GCStack::frames[i].mask);
            }
        }

        for (auto iter = Allocator::GlobalAllocator.tempRoots.begin(); iter != Allocator::GlobalAllocator.tempRoots.end(); ++iter)
        {
            Allocator::gcClearMark(**iter);
        }
    }

public:
    Allocator() : nsalloc(this), osalloc(), maybeZeroCounts(), bstart(0), bend(0), worklist(), releaselist()
    {
        this->maybeZeroCounts.reserve(256);

        MEM_STATS_OP(this->gccount = 0);
        MEM_STATS_OP(this->promotedbytes = 0);
        MEM_STATS_OP(this->maxheap = 0);
    }

    ~Allocator()
    {
        ;
    }

    inline uint8_t* allocateDynamic(const BSQType* mdata)
    {
        size_t asize = BSQ_ALIGN_SIZE(mdata->allocsize);
        uint8_t* alloc = this->nsalloc.allocateDynamicSize(asize);

        *((const BSQType**)alloc) = mdata;
        uint8_t* res = (alloc + sizeof(BSQType*));

        return res;
    }

    inline void ensureSpace(size_t required)
    {
        this->nsalloc.ensureSpace(BSQ_ALIGN_SIZE(required) + sizeof(BSQType*));
    }

    inline uint8_t* allocateSafe(size_t allocsize, BSQType* mdata)
    {
        size_t asize = BSQ_ALIGN_SIZE(allocsize);
        uint8_t* alloc = this->nsalloc.allocateSafe(asize);

        *((BSQType**)alloc) = mdata;
        uint8_t* res = (alloc + sizeof(BSQType*));

        return res;
    }

    void pushRoot(void** mem)
    {
        this->tempRoots.push_back(mem);
    }

    void popRoot()
    {
        this->tempRoots.pop_back();
    }

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->nsalloc.currentAllocatedBytes() + this->osalloc.currentAllocatedBytes()));

        //mark and move all live objects out of new space
        this->processRoots();
        this->processHeap();

        //Look at all the possible unreachable roots in the old space and collect (recursively) them as needed
        this->checkMaybeZeroCountList();
        this->processRelease();

        //Reset the mark colors on the roots
        this->clearAllMarkRoots();

        //Adjust the new space size if needed and reset/free the newspace allocators
        this->nsalloc.postGCProcess(this->osalloc.currentAllocatedBytes());
    }
};
