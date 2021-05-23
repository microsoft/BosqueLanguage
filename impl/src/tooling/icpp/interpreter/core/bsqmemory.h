//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"

struct GCStackEntry
{
    void** framep;
    RefMask mask;
};

class GCStack
{
public:
    static GCStackEntry frames[2048];
    static uint32_t stackp;

    inline static void pushFrame(void** framep, RefMask mask)
    {
        if (GCStack::stackp >= 8192)
        {
            printf("Out-Of-Stack\n");
            exit(1);
        }

        GCStack::frames[GCStack::stackp++] = { framep, mask };
    }

    inline static void popFrame()
    {
        GCStack::stackp--;
    }
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

    std::deque<void*> m_bigallocs;

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
        bool shouldgrow = this->m_allocsize < BSQ_MAX_NURSERY_SIZE && this->m_allocsize < rcalloc / 2;
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
    NewSpaceAllocator() : m_block(nullptr), m_bigallocs()
    {
        MEM_STATS_OP(this->totalalloc = 0);

        this->setAllocBlock(BSQ_MIN_NURSERY_SIZE);
    }

    ~NewSpaceAllocator()
    {
        BSQ_BUMP_SPACE_RELEASE(this->m_block);
    }

    void postGCProcess(size_t rcmem)
    {
        this->resizeAllocatorAsNeeded(rcmem);

        this->m_currPos = this->m_block;
        this->m_endPos = this->m_block + this->m_allocsize;
    }

    size_t currentAllocatedBytes(bool includebig) const
    {
        size_t bigalloc = 0;
        if(includebig)
        {
            for(auto iter = this->m_bigallocs.cbegin(); iter != this->m_bigallocs.cend(); ++iter)
            {
                bigalloc += (GET_TYPE_META_DATA(*iter))->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);
            }
        }

        return bigalloc + (size_t)(this->m_currPos - this->m_block);
    }

    //Return do a GC and return uint8_t* of given rsize from the bumplist implementation
    uint8_t* allocateDynamicSizeSlow(size_t rsize);

    //Return uint8_t* of given asize + sizeof(MetaData*)
    inline uint8_t* allocateDynamicSize(size_t asize)
    {
        size_t rsize = asize + sizeof(GC_META_DATA_WORD);

        //Note this is technically UB!!!!
        if((rsize <= BSQ_ALLOC_MAX_BLOCK_SIZE) & (this->m_currPos <= this->m_endPos))
        {
            uint8_t *res = this->m_currPos;
            this->m_currPos += rsize;

            return res;
        }
        else
        {
            return this->allocateDynamicSizeSlow(rsize);
        }
    }

    void ensureSpace_slow();

    inline void ensureSpace(size_t required)
    {
        if (this->m_currPos + required > this->m_endPos)
        {
            this->ensureSpace_slow();
        }
    }

    inline uint8_t* allocateSafe(size_t asize)
    {
        size_t rsize = asize + sizeof(BSQType*);
        assert(this->m_currPos + rsize <= this->m_endPos);

        uint8_t *res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
};

class Allocator
{
public:
    static Allocator GlobalAllocator;

private:
    NewSpaceAllocator nsalloc;

    std::deque<void**> tempRoots;
    std::deque<void*> maybeZeroCounts;

    std::queue<void*> worklist;
    std::queue<void*> releaselist;

#ifdef ENABLE_MEM_STATS
    size_t liveoldspace;

    size_t gccount;
    size_t promotedbytes;
    size_t maxheap;
#endif

    template <bool isRoot>
    void* moveBumpObjectToRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        void* nobj = BSQ_FREE_LIST_ALLOC_SMALL(osize);

        MEM_STATS_OP(this->liveoldspace += osize);
        MEM_STATS_OP(this->promotedbytes += osize);

        GC_MEM_COPY(nobj, addr, osize);
        if (!ometa->isLeafType)
        {
            this->worklist.push(nobj);
        }

        void* robj = (void*)((uint8_t*)nobj + sizeof(GC_META_DATA_WORD));
        if constexpr (isRoot)
        {
            GC_SET_META_DATA_WORD(nobj, GC_SET_MARK_BIT(w));
            this->maybeZeroCounts.push_back(robj);
        }
        else
        {
            GC_SET_META_DATA_WORD(nobj, GC_INC_RC(w));
        }

        GC_SET_TYPE_META_DATA_FORWARD_SENTINAL(addr);
        GC_SET_FORWARD_PTR(obj, robj);

        return robj;
    }

    template <bool isRoot>
    void moveLargeAllocObjectToRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        MEM_STATS_OP(this->liveoldspace += osize);

        if (!ometa->isLeafType)
        {
            this->worklist.push(obj);
        }

        GC_SET_META_DATA_WORD(obj, GC_SET_MARK_BIT(w));
        if constexpr (isRoot)
        {
            this->maybeZeroCounts.push_back(obj);
        }
        else
        {
            GC_SET_META_DATA_WORD(addr, GC_INC_RC(w));
        }
    }

public:
    template <bool isRoot>
    inline static void gcProcessSlot(void** slot)
    {
        void*v = *slot;
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD w = GC_DEC_RC(GC_LOAD_META_DATA_WORD(addr));
            if (GC_TEST_IS_YOUNG(w))
            {
                const BSQType* ometa = GET_TYPE_META_DATA_FROM_WORD(w);
                size_t osize = ometa->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);

                if(osize <= BSQ_ALLOC_MAX_BLOCK_SIZE)
                {
                    *slot = Allocator::GlobalAllocator.moveBumpObjectToRCSpace<isRoot>(v, addr, w, ometa, osize);
                }
                else
                {
                    Allocator::GlobalAllocator.moveLargeAllocObjectToRCSpace<isRoot>(v, addr, w, ometa, osize);
                }
            }
            else
            {
                if constexpr (isRoot)
                {
                    GC_SET_META_DATA_WORD(addr, GC_SET_MARK_BIT(w));
                }
                else
                {
                    GC_SET_META_DATA_WORD(addr, GC_INC_RC(w));
                }
            }
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlotWithString(void** slot)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcProcessSlot<isRoot>(slot);
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlotWithBigNum(void** slot)
    {
        if (!IS_INLINE_BIGNUM(slot))
        {
            Allocator::gcProcessSlot<isRoot>(slot);
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
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcProcessSlotWithBigNum<isRoot>(cslot++);
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
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
            GC_META_DATA_WORD w = GC_DEC_RC(GC_LOAD_META_DATA_WORD(addr));
            GC_SET_META_DATA_WORD(addr, w);

            if (GC_TEST_IS_UNREACHABLE(w))
            {
                Allocator::GlobalAllocator.releaselist.push(obj);
            }
        }
    }

    inline static void gcDecrementString(void** slot)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcDecrement(*slot);
        }
    }

    inline static void gcDecrementBigNum(void** slot)
    {
        if (!IS_INLINE_BIGNUM(slot))
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
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcDecrementBigNum(cslot++);
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
            Allocator::gcProcessSlotsWithMask<true>(GCStack::frames[i].framep, GCStack::frames[i].mask);
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

            Allocator::gcProcessSlotsWithMask<false>((void**)obj, umeta->refmask);
        }
    }

    void sweep()
    {
        xxxx;
    }

    void checkMaybeZeroCountList(std::vector<void*>::iterator zclend)
    {
        auto biter = this->maybeZeroCounts.begin();
        for (auto iter = biter; iter < zclend; iter++)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(*iter);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

            if (GC_TEST_IS_UNREACHABLE(w))
            {
                this->releaselist.push(*iter);
                *iter = nullptr;
            }
            else
            {
                if (GC_TEST_IS_ZERO_RC(w))
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
    Allocator() : nsalloc(), osalloc(), maybeZeroCounts(), bstart(0), bend(0), worklist(), releaselist()
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
        size_t asize = BSQ_ALIGN_SIZE(mdata->allocinfo.heapsize);
        uint8_t* alloc = this->nsalloc.allocateDynamicSize(asize);

        *((const BSQType**)alloc) = mdata;
        uint8_t* res = (alloc + sizeof(BSQType*));

        return res;
    }

    inline void ensureSpace(size_t required)
    {
        this->nsalloc.ensureSpace(BSQ_ALIGN_SIZE(required) + sizeof(BSQType*));
    }

    inline uint8_t* allocateSafe(size_t allocsize, const BSQType* mdata)
    {
        size_t asize = BSQ_ALIGN_SIZE(allocsize);
        uint8_t* alloc = this->nsalloc.allocateSafe(asize);

        *((const BSQType**)alloc) = mdata;
        uint8_t* res = (alloc + sizeof(BSQType*));

        return res;
    }

    uint8_t* allocateEternal(size_t allocsize, const BSQType* mdata)
    {
        size_t tsize = sizeof(RCMeta) + sizeof(BSQType*) + size;
        assert((tsize & BSQ_MEM_ALIGNMENT_MASK) == 0x0);

        MEM_STATS_OP(this->totalalloc += tsize);

        uint8_t* rr = (uint8_t*)BSQ_FREE_LIST_ALLOC(tsize);
        *((RCMeta*)rr) = GC_RC_ETERNAL_INIT;

        this->livealloc += tsize;

        return (rr + sizeof(RCMeta));
    }

    template<typename T>
    void pushRoot(T** mem)
    {
        this->tempRoots.push_back((void**)((void*)mem));
    }

    void popRoot()
    {
        this->tempRoots.pop_back();
    }

    template<size_t ct>
    void popRoots()
    {
        this->tempRoots.erase(this->tempRoots.end() - ct, this->tempRoots.end());
    }

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->nsalloc.currentAllocatedBytes() + this->osalloc.currentAllocatedBytes()));

        //mark and move all live objects out of new space
        this->processRoots();
        this->processHeap();

        //Sweep young roots and look possible unreachable old roots in the old with collect them as needed -- new zero counts are rotated in
        auto zclend = this->maybeZeroCounts.end();
        this->sweep();
        this->checkMaybeZeroCountList(zclend);

        //Process release recursively (should be mimalloc heartbeat later)
        this->processRelease();

        //Adjust the new space size if needed and reset/free the newspace allocators
        this->nsalloc.postGCProcess(this->osalloc.currentAllocatedBytes());
    }
};
