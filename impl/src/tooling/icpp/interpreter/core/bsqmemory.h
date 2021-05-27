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

template <size_t bsize>
class GCRefListIterator
{
public:
    void** crl;
    size_t cpos;

    GCRefListIterator() : crl(nullptr), cpos(0) {;}
    ~GCRefListIterator() {;}

    inline void* get() const
    {
        return this->crl[this->cpos];
    }

    inline void copyFrom(const GCRefListIterator& other)
    {
        this->crl[this->cpos] = other.get();
    }
};

template <size_t bsize>
class GCRefList
{
private:
    void** headrl;
    void** tailrl;
    size_t spos;
    size_t epos;

public:
    GCRefList() : headrl(nullptr), tailrl(nullptr), spos(1), epos(1) 
    {
        this->headrl = (void**)mi_zalloc_small(bsize * sizeof(void*));
        this->tailrl = this->headrl;
    }

    ~GCRefList()
    {
        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            mi_free(tmp);
        }
    }

    void assignFrom(GCRefList& other)
    {
        assert(this != &other);

        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            mi_free(tmp);
        }

        this->headrl = other.headrl;
        this->tailrl = other.tailrl;
        this->spos = other.spos;
        this->epos = other.epos;

        other.headrl = this->headrl = (void**)mi_zalloc_small(bsize * sizeof(void*));
        other.tailrl = other.headrl;
        other.spos = 1;
        other.epos = 1;
    }

    bool reset()
    {
        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            mi_free(tmp);
        }

        this->headrl = (void**)mi_zalloc_small(bsize * sizeof(void*));
        this->tailrl = this->headrl;
        this->spos = 1;
        this->epos = 1;
    }

    bool empty() const
    {
        return (this->headrl == this->tailrl && this->spos == this->epos);
    }

    void enqueSlow(void* v);

    inline void enque(void* v)
    {
        if(this->epos < bsize)
        {
            this->tailrl[this->epos++] = v;
        }
        else
        {
            this->enqueSlow(v);
        }
    }

    void* dequeSlow();

    inline void* deque()
    {
        assert(!this->empty());

        if(this->spos < bsize)
        {
            return this->tailrl[this->spos++];
        }
        else
        {
            this->dequeSlow(v);
        }
    }

    void iterBegin(GCRefListIterator<bsize>& iter) const
    {
        iter.crl = this->headrl;
        iter.cpos = this->spos;
    }

    inline bool iterHasMore(const GCRefListIterator<bsize>& iter) const
    {
        return (iter.crl != this->tailrl) | (iter.cpos != this->epos);
    }

    void iterAdvanceSlow(GCRefListIterator<bsize>& iter) const;

    inline void iterAdvance(GCRefListIterator<bsize>& iter) const
    {
       if(iter.cpos < bsize)
        {
            return iter.cpos++;
        }
        else
        {
            this->iterAdvanceSlow(iter);
        }
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

    GCRefList<GC_REF_LIST_BLOCK_SIZE_DEFAULT> m_bigallocs;
    size_t m_bigallocsCount;

#ifdef ENABLE_MEM_STATS
    size_t totalbumpalloc;
    size_t totalbigalloc;
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
        bool shouldgrow = this->m_allocsize < BSQ_MAX_NURSERY_SIZE && this->m_allocsize < rcalloc / 3;
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
    NewSpaceAllocator() : m_block(nullptr), m_bigallocs(), m_bigallocsCount(0)
    {
        MEM_STATS_OP(this->totalbumpalloc = 0);
        MEM_STATS_OP(this->totalbigalloc = 0);

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

        this->m_bigallocs.reset();
        this->m_bigallocsCount = 0;
    }

    size_t currentBigAllocCount() const
    {
        return this->m_bigallocsCount;
    }

    size_t currentAllocatedBigBytes() const
    {
        size_t bigalloc = 0;

        GCRefListIterator<GC_REF_LIST_BLOCK_SIZE_DEFAULT> iter;
        this->m_bigallocs.iterBegin(iter);
        while(this->m_bigallocs.iterHasMore(iter))
        {
            bigalloc += (GET_TYPE_META_DATA(iter.get()))->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);
        }
        
        return bigalloc;
    }

    size_t currentAllocatedSlabBytes() const
    {
        return (size_t)(this->m_currPos - this->m_block);
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
        size_t rsize = asize + sizeof(GC_META_DATA_WORD);
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

    GCRefList<GC_REF_LIST_BLOCK_SIZE_SMALL> tempRoots;
    GCRefList<GC_REF_LIST_BLOCK_SIZE_DEFAULT> maybeZeroCounts;
    GCRefList<GC_REF_LIST_BLOCK_SIZE_DEFAULT> newMaybeZeroCounts;

    GCRefList<GC_REF_LIST_BLOCK_SIZE_DEFAULT> worklist;
    GCRefList<GC_REF_LIST_BLOCK_SIZE_DEFAULT> releaselist;

    size_t liveoldspace;

    xxx; //add globals buffer + mask -- then add make enternal, we can call this after const eval and then detach buffer from GC

#ifdef ENABLE_MEM_STATS
    size_t gccount;
    size_t promotedbytes;
    size_t maxheap;
#endif

    template <bool isRoot>
    void* moveBumpObjectToRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        void* nobj = BSQ_FREE_LIST_ALLOC_SMALL(osize);

        this->liveoldspace += osize;
        MEM_STATS_OP(this->promotedbytes += osize);

        GC_MEM_COPY(nobj, addr, osize);
        if (!ometa->isLeafType)
        {
            this->worklist.push(nobj);
        }

        if constexpr (isRoot)
        {
            GC_INIT_OLD_ROOT(nobj, w);
            this->newMaybeZeroCounts.push_back(robj);
        }
        else
        {
            GC_INIT_OLD_HEAP(nobj, w);
        }

        GC_SET_TYPE_META_DATA_FORWARD_SENTINAL(addr);

        void* robj = (void*)((uint8_t*)nobj + sizeof(GC_META_DATA_WORD));
        GC_SET_FORWARD_PTR(obj, robj);

        return robj;
    }

    template <bool isRoot>
    void moveLargeAllocObjectToRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        this->liveoldspace += osize;

        if (!ometa->isLeafType)
        {
            this->worklist.push(obj);
        }

        if constexpr (isRoot)
        {
            GC_INIT_OLD_ROOT(obj, w);
            this->newMaybeZeroCounts.push_back(obj);
        }
        else
        {
            GC_INIT_OLD_HEAP(nobj, w);
        }
    }

public:
    template <bool isRoot>
    inline static void gcProcessSlot(void** slot)
    {
        void* v = *slot;
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);
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
                if(GC_IS_TYPE_META_DATA_FORWARD_SENTINAL(w))
                {
                    *slot = GC_GET_FORWARD_PTR(v);
                    addr = GC_GET_META_DATA_ADDR(*slot);
                    w = GC_LOAD_META_DATA_WORD(addr);
                }
            
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
        if (!IS_INLINE_STRING(*slot))
        {
            Allocator::gcProcessSlot<isRoot>(slot);
        }
    }

    template <bool isRoot>
    inline static void gcProcessSlotWithBigNum(void** slot)
    {
        if (!IS_INLINE_BIGNUM(*slot))
        {
            Allocator::gcProcessSlot<isRoot>(slot);
        }
    }

    template <bool isRoot>
    inline static void** gcProcessSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->getProcessFP<isRoot>()(umeta, slots + 1);
    }

    template <bool isRoot>
    inline static void** gcProcessSlotsWithMask(void** slots, RefMask mask)
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
                    cslot = Allocator::gcProcessSlotsWithUnion<isRoot>(cslot);
                    break;
            }
        }

        return cslot;
    }

    ////////
    //Operations GC decrement
    inline static void gcDecrement(void* v)
    {
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD w = GC_DEC_RC(GC_LOAD_META_DATA_WORD(addr));
            GC_SET_META_DATA_WORD(addr, w);

            if (GC_TEST_IS_UNREACHABLE(w))
            {
                Allocator::GlobalAllocator.releaselist.enque(v);
            }
        }
    }

    inline static void gcDecrementString(void* v)
    {
        if (!IS_INLINE_STRING(v))
        {
            Allocator::gcDecrement(v);
        }
    }

    inline static void gcDecrementBigNum(void* v)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            Allocator::gcDecrement(v);
        }
    }

    inline static void** gcDecrementSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpDecObj(umeta, slots + 1);
    }

    inline static void** gcDecSlotsWithMask(void** slots, RefMask mask)
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
                    Allocator::gcDecrement(*cslot++);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcDecrementString(*cslot++);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcDecrementBigNum(*cslot++);
                    break;
                default:
                    cslot = Allocator::gcDecrementSlotsWithUnion(cslot);
                    break;
            }
        }

        return cslot;
    }

    ////////
    //Operations GC mark clear
    inline static void gcClearMark(void* v)
    {
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD w = GC_CLEAR_MARK_BIT(GC_LOAD_META_DATA_WORD(addr));
            GC_SET_META_DATA_WORD(addr, w);
        }
    }

    inline static void gcClearMarkString(void* v)
    {
        if (!IS_INLINE_STRING(v))
        {
            Allocator::gcClearMark(v);
        }
    }

    inline static void gcClearMarkBigNum(void* v)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            Allocator::gcClearMark(v);
        }
    }

    inline static void** gcClearMarkSlotsWithUnion(void** slots)
    {
        const BSQType *umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpClearObj(umeta, slots + 1);
    }

    inline static void** gcClearMarkSlotsWithMask(void** slots, RefMask mask)
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
                    Allocator::gcClearMark(*cslot++);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcClearMarkString(*cslot++);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcClearMarkBigNum(*cslot++);
                    break;
                default:
                    cslot = Allocator::gcClearMarkSlotsWithUnion(cslot);
                    break;
            }
        }

        return cslot;
    }

private:
    ////////
    //GC algorithm
    static void processRoots()
    {
        for(size_t i = 0; i < GCStack::stackp; ++i)
        {
            Allocator::gcProcessSlotsWithMask<true>(GCStack::frames[i].framep, GCStack::frames[i].mask);
        }

        GCRefListIterator<GC_REF_LIST_BLOCK_SIZE_SMALL> iter;
        Allocator::GlobalAllocator.tempRoots.iterBegin(iter);
        while(Allocator::GlobalAllocator.tempRoots.iterHasMore(iter))
        {
            Allocator::gcProcessSlot<true>((void**)iter.get());
        }
    }

    void processHeap()
    {
        while (!this->worklist.empty())
        {
            void* obj = this->worklist.deque();

            const BSQType* umeta = GET_TYPE_META_DATA(obj);
            assert(umeta->allocinfo.heapmask != nullptr);

            Allocator::gcProcessSlotsWithMask<false>((void**)obj, umeta->allocinfo.heapmask);
        }
    }

    void checkMaybeZeroCountList()
    {
        GCRefListIterator<GC_REF_LIST_BLOCK_SIZE_DEFAULT> iter;
        this->maybeZeroCounts.iterBegin(iter);
        while(this->maybeZeroCounts.iterHasMore(iter))
        {
            auto obj = iter.get();
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

            if (GC_TEST_IS_UNREACHABLE(w))
            {
                this->releaselist.enque(obj);
            }
            else
            {
                if(GC_TEST_IS_ZERO_RC(w))
                {
                    this->newMaybeZeroCounts.enque(obj);
                }
            }
        }

        this->maybeZeroCounts.assignFrom(this->newMaybeZeroCounts);
    }

    void processRelease()
    {
        size_t freelimit = (3 * (this->nsalloc.currentAllocatedSlabBytes() + this->nsalloc.currentAllocatedBigBytes()) / 2);
        size_t biglimit = (3 * this->nsalloc.currentBigAllocCount()) / 2;

        size_t freecount = 0;
        size_t bigcount = 0;
        while (!this->releaselist.empty())
        {
            if((freelimit <= freecount) | (biglimit <= bigcount))
            {
                break;
            } 

            void* obj = this->releaselist.deque();

            const BSQType* umeta = GET_TYPE_META_DATA(obj);
            if (umeta->allocinfo.heapmask != nullptr)
            {
                umeta->gcops.fpDecObj(umeta, (void**)obj);
            }

            size_t asize = umeta->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);
            if(asize <= BSQ_ALLOC_MAX_BLOCK_SIZE)
            {
                freecount += asize;
            }
            else
            {
                bigcount++;
            }

            this->liveoldspace -= asize;
            BSQ_FREE_LIST_RELEASE(asize, GC_GET_META_DATA_ADDR(obj));
        }
    }

    void clearAllMarkRoots()
    {
        for (size_t i = 0; i < GCStack::stackp; ++i)
        {
            Allocator::gcClearMarkSlotsWithMask(GCStack::frames[i].framep, GCStack::frames[i].mask);
        }

        GCRefListIterator<GC_REF_LIST_BLOCK_SIZE_SMALL> iter;
        Allocator::GlobalAllocator.tempRoots.iterBegin(iter);
        while(Allocator::GlobalAllocator.tempRoots.iterHasMore(iter))
        {
            Allocator::gcClearMark(*((void**)iter.get()));
        }
    }

public:
    Allocator() : nsalloc(), tempRoots(), maybeZeroCounts(), newMaybeZeroCounts(), worklist(), releaselist(), liveoldspace(0)
    {
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
        size_t asize = mdata->allocinfo.heapsize;
        uint8_t* alloc = this->nsalloc.allocateDynamicSize(asize);

        GC_INIT_YOUNG(alloc, mdata->tid);
        uint8_t* res = (alloc + sizeof(GC_META_DATA_WORD));

        return res;
    }

    inline void ensureSpace(size_t required)
    {
        this->nsalloc.ensureSpace(required);
    }

    inline void ensureSpace(const BSQType* mdata)
    {
        this->nsalloc.ensureSpace(mdata->allocinfo.heapsize + sizeof(GC_META_DATA_WORD));
    }

    inline uint8_t* allocateSafe(const BSQType* mdata)
    {
        uint8_t* alloc = this->nsalloc.allocateSafe(mdata->allocinfo.heapsize);

        GC_INIT_YOUNG(alloc, mdata->tid);
        uint8_t* res = (alloc + sizeof(GC_META_DATA_WORD));

        return res;
    }

    uint8_t* allocateEternal(const BSQType* mdata)
    {
        size_t tsize = mdata->allocinfo.heapsize + sizeof(GC_META_DATA_WORD);
        MEM_STATS_OP(this->totalalloc += tsize);
        MEM_STATS_OP(this->livealloc += tsize);

        uint8_t* rr = (uint8_t*)BSQ_FREE_LIST_ALLOC(tsize);
        GC_INIT_ETERNAL(rr, mdata->tid);

        return (rr + sizeof(GC_META_DATA_WORD));
    }

    template<typename T>
    void pushRoot(T** mem)
    {
        this->tempRoots.enque((void**)((void*)mem));
    }

    void popRoot()
    {
        this->tempRoots.deque();
    }

    template<size_t ct>
    void popRoots()
    {
        for(size_t i = 0; i < ct; ++i)
        {
            this->tempRoots.deque();
        }
    }

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->nsalloc.currentAllocatedSlabBytes() + this->nsalloc.currentAllocatedBigBytes() + this->liveoldspace));

        //mark and move all live objects out of new space
        this->processRoots();
        this->processHeap();

        //Sweep young roots and look possible unreachable old roots in the old with collect them as needed -- new zero counts are rotated in
        this->checkMaybeZeroCountList();

        //Process release recursively
        this->processRelease();

        //Clear any marks
        this->clearAllMarkRoots();

        //Adjust the new space size if needed and reset/free the newspace allocators
        this->nsalloc.postGCProcess(this->liveoldspace);
    }
};
