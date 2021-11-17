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
    static GCStackEntry frames[BSQ_MAX_STACK];
    static uint32_t stackp;

    inline static void pushFrame(void** framep, RefMask mask)
    {
        if (GCStack::stackp < BSQ_MAX_STACK) [[likely]]
        {
            GCStack::frames[GCStack::stackp++] = { framep, mask };
        }
        else [[unlikely]]
        {
            printf("Out-Of-Stack\n");
            exit(1);
        }
    }

    inline static void popFrame()
    {
        GCStack::stackp--;
    }
};

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
        this->headrl = (void**)mi_zalloc_small(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
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

        other.headrl = (void**)mi_zalloc_small(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
        other.tailrl = other.headrl;
        other.spos = 1;
        other.epos = 1;
    }

    void reset()
    {
        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            mi_free(tmp);
        }

        this->headrl = (void**)mi_zalloc_small(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
        this->tailrl = this->headrl;
        this->spos = 1;
        this->epos = 1;
    }

    bool empty() const
    {
        return (this->headrl == this->tailrl && this->spos == this->epos);
    }

    void enqueSlow(void* v)
    {
        void** tmp = (void**)mi_zalloc_small(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
        this->tailrl[0] = tmp;
        this->tailrl = tmp;
        this->epos = 1;
    }

    inline void enque(void* v)
    {
        if(this->epos < GC_REF_LIST_BLOCK_SIZE_DEFAULT) [[likely]]
        {
            this->tailrl[this->epos++] = v;
        }
        else [[unlikely]]
        {
            this->enqueSlow(v);
        }
    }

    void* dequeSlow()
    {
        void** tmp = this->headrl;
    
        this->headrl = (void**)this->headrl[0];
        this->spos = 2;

        mi_free(tmp);
        return this->headrl[1];
    }

    inline void* deque()
    {
        assert(!this->empty());

        if(this->spos < GC_REF_LIST_BLOCK_SIZE_DEFAULT) [[likely]]
        {
            return this->tailrl[this->spos++];
        }
        else [[unlikely]]
        {
            return this->dequeSlow();
        }
    }

    void iterBegin(GCRefListIterator& iter) const
    {
        iter.crl = this->headrl;
        iter.cpos = this->spos;
    }

    inline bool iterHasMore(const GCRefListIterator& iter) const
    {
        return (iter.crl != this->tailrl) | (iter.cpos != this->epos);
    }

    void iterAdvanceSlow(GCRefListIterator& iter) const
    {
        iter.crl = (void**)iter.crl[0];
        iter.cpos = 1;
    }

    inline void iterAdvance(GCRefListIterator& iter) const
    {
        if(iter.cpos < GC_REF_LIST_BLOCK_SIZE_DEFAULT) [[likely]]
        {
            iter.cpos++;
        }
        else [[unlikely]]
        {
            this->iterAdvanceSlow(iter);
        }
    }
};

//A class that implements our bump pointer nursery space
class BumpSpaceAllocator
{
private:
    //We inline the fields for the current/end of the block that we are allocating from
    uint8_t *m_currPos;
    uint8_t *m_endPos;

    size_t m_allocsize;
    uint8_t *m_block;

#ifdef ENABLE_MEM_STATS
    size_t totalbumpalloc;
    size_t totalbigalloc;
#endif

    void setAllocBlock(size_t asize)
    {
        this->m_allocsize = asize;
        this->m_block = (uint8_t*)BSQ_BUMP_SPACE_ALLOC(asize);

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
    BumpSpaceAllocator() : m_block(nullptr)
    {
        MEM_STATS_OP(this->totalbumpalloc = 0);
        MEM_STATS_OP(this->totalbigalloc = 0);

        this->setAllocBlock(BSQ_MIN_NURSERY_SIZE);
    }

    ~BumpSpaceAllocator()
    {
        BSQ_BUMP_SPACE_RELEASE(this->m_block);
    }

    void postGCProcess(size_t rcmem)
    {
        this->resizeAllocatorAsNeeded(rcmem);

        this->m_currPos = this->m_block;
        this->m_endPos = this->m_block + this->m_allocsize;
    }

    size_t currentAllocatedSlabBytes() const
    {
        return (size_t)(this->m_currPos - this->m_block);
    }

    void ensureSpace_slow();

    //Return uint8_t* of given asize + sizeof(MetaData*)
    inline uint8_t* allocateDynamicSize(size_t asize)
    {
        size_t rsize = asize + sizeof(GC_META_DATA_WORD);

        if(this->m_currPos + rsize > this->m_endPos) [[unlikely]]
        {
             this->ensureSpace_slow();
        }

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }

    inline void ensureSpace(size_t required)
    {
        if (this->m_currPos + required > this->m_endPos) [[unlikely]]
        {
            this->ensureSpace_slow();
        }
    }

    inline uint8_t* allocateSafe(size_t asize)
    {
        size_t rsize = asize + sizeof(GC_META_DATA_WORD);
        assert(this->m_currPos + rsize <= this->m_endPos);

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
};

class Allocator
{
public:
    static Allocator GlobalAllocator;

private:
    BumpSpaceAllocator bumpalloc;
    size_t rcalloc;

    GCRefList maybeZeroCounts;
    GCRefList newMaybeZeroCounts;

    GCRefList worklist;
    GCRefList releaselist;

    size_t liveoldspace;

    void* globals_mem;
    RefMask globals_mask;

#ifdef ENABLE_MEM_STATS
    size_t gccount;
    size_t promotedbytes;
    size_t maxheap;
#endif

    template <bool isRoot>
    void* moveYoungBumpObjectToOldRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        void* nobj = BSQ_FREE_LIST_ALLOC_SMALL(osize);

        this->liveoldspace += osize;
        MEM_STATS_OP(this->promotedbytes += osize);

        GC_MEM_COPY(nobj, addr, osize);
        if (!ometa->isLeaf())
        {
            this->worklist.enque(nobj);
        }

        if constexpr (isRoot)
        {
            GC_INIT_OLD_RC_ROOT_REF(nobj, w);
            this->newMaybeZeroCounts.enque(nobj);
        }
        else
        {
            GC_INIT_OLD_RC_HEAP_REF(nobj, w);
        }

        GC_SET_TYPE_META_DATA_FORWARD_SENTINAL(addr);

        void* robj = (void*)((uint8_t*)nobj + sizeof(GC_META_DATA_WORD));
        GC_SET_FORWARD_PTR(obj, robj);

        return robj;
    }

    template <bool isRoot>
    void moveYoungRCAllocObjectToOldRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
    {
        this->liveoldspace += osize;

        if (!ometa->isLeaf())
        {
            this->worklist.enque(obj);
        }

        if(GC_TEST_IS_EAGER_RC(w))
        {
            GC_UPDATE_OLD_RC_EAGER(obj, w);
        }
        else
        {
            if constexpr (isRoot)
            {
                GC_UPDATE_OLD_RC_ROOT_REF(obj, w);
            }
            else
            {
                GC_UPDATE_OLD_RC_HEAP_REF(obj, w);
            }
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

                if(GC_TEST_IS_BUMP_SPACE(w))
                {
                    *slot = Allocator::GlobalAllocator.moveYoungBumpObjectToOldRCSpace<isRoot>(v, addr, w, ometa, osize);
                }
                else
                {
                    Allocator::GlobalAllocator.moveYoungRCAllocObjectToOldRCSpace<isRoot>(v, addr, w, ometa, osize);
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
                    if(!GC_TEST_IS_STRICT(w))
                    { 
                        GC_SET_META_DATA_WORD(addr, GC_INC_RC(w));
                    }
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
    inline static void gcProcessSlotsWithUnion(void** slots)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return (getProcessFP<isRoot>(umeta))(umeta, slots + 1);
        }
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
                case PTR_FIELD_MASK_NOP:
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcProcessSlot<isRoot>(cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcProcessSlotWithString<isRoot>(cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcProcessSlotWithBigNum<isRoot>(cslot);
                    break;
                default:
                    Allocator::gcProcessSlotsWithUnion<isRoot>(cslot);
                    break;
            }
            cslot++;
        }
    }

    ////////
    //Operations GC decrement
    inline static void gcDecrement(void* v)
    {
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD waddr = GC_LOAD_META_DATA_WORD(addr);

            GC_META_DATA_WORD w = GC_DEC_RC(waddr);
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

    inline static void gcDecrementSlotsWithUnion(void** slots)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return umeta->gcops.fpDecObj(umeta, slots + 1);
        }
    }

    inline static void gcDecSlotsWithMask(void** slots, RefMask mask)
    {
        void** cslot = slots;

        RefMask cmaskop = mask;
        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_NOP:
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcDecrement(*cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcDecrementString(*cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcDecrementBigNum(*cslot);
                    break;
                default:
                    Allocator::gcDecrementSlotsWithUnion(cslot);
                    break;
            }
            cslot++;
        }
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

    inline static void gcClearMarkSlotsWithUnion(void** slots)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return umeta->gcops.fpClearObj(umeta, slots + 1);
        }
    }

    inline static void gcClearMarkSlotsWithMask(void** slots, RefMask mask)
    {
        void** cslot = slots;

        RefMask cmaskop = mask;
        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_NOP:
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcClearMark(*cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcClearMarkString(*cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcClearMarkBigNum(*cslot);
                    break;
                default:
                    Allocator::gcClearMarkSlotsWithUnion(cslot);
                    break;
            }
            cslot++;
        }
    }

    ////////
    //Operations Make Immortal
    inline static void gcMakeImmortal(void* v)
    {
        if (v != nullptr)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
            GC_META_DATA_WORD waddr = GC_LOAD_META_DATA_WORD(addr);

            GC_SET_META_DATA_WORD(addr, GC_INC_RC(waddr));
        }
    }

    inline static void gcMakeImmortalString(void* v)
    {
        if (!IS_INLINE_STRING(v))
        {
            Allocator::gcMakeImmortal(v);
        }
    }

    inline static void gcMakeImmortalBigNum(void* v)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            Allocator::gcMakeImmortal(v);
        }
    }

    inline static void gcMakeImmortalSlotsWithUnion(void** slots)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return umeta->gcops.fpMakeImmortal(umeta, slots + 1);
        }
    }

    inline static void gcMakeImmortalSlotsWithMask(void** slots, RefMask mask)
    {
        void** cslot = slots;

        RefMask cmaskop = mask;
        while (*cmaskop)
        {
            char op = *cmaskop++;
            switch(op)
            {
                case PTR_FIELD_MASK_NOP:
                    break;
                case PTR_FIELD_MASK_PTR:
                    Allocator::gcMakeImmortal(*cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcMakeImmortalString(*cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcMakeImmortalBigNum(*cslot);
                    break;
                default:
                    Allocator::gcMakeImmortalSlotsWithUnion(cslot);
                    break;
            }
            cslot++;
        }
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

        if(Allocator::GlobalAllocator.globals_mem != nullptr)
        {
            Allocator::gcProcessSlotsWithMask<true>((void**)Allocator::GlobalAllocator.globals_mem, Allocator::GlobalAllocator.globals_mask);
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
        GCRefListIterator iter;
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
        size_t freelimit = (3 * (this->bumpalloc.currentAllocatedSlabBytes() + rcalloc)) / 2;
        size_t freecount = 0;

        while (!this->releaselist.empty())
        {
            if(freelimit <= freecount) [[unlikely]]
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
            freecount += asize;

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

        if(Allocator::GlobalAllocator.globals_mem != nullptr)
        {
            Allocator::gcClearMarkSlotsWithMask((void**)Allocator::GlobalAllocator.globals_mem, Allocator::GlobalAllocator.globals_mask);
        }
    }

public:
    Allocator() : bumpalloc(), rcalloc(0), maybeZeroCounts(), newMaybeZeroCounts(), worklist(), releaselist(), liveoldspace(0), globals_mem(nullptr)
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
        uint8_t* alloc = this->bumpalloc.allocateDynamicSize(asize);

        GC_INIT_BUMP_SPACE_ALLOC(alloc, mdata->tid);
        return (alloc + sizeof(GC_META_DATA_WORD));
    }

    inline void ensureSpace(size_t required)
    {
        this->bumpalloc.ensureSpace(required);
    }

    inline void ensureSpace(const BSQType* mdata)
    {
        this->bumpalloc.ensureSpace(mdata->allocinfo.heapsize + sizeof(GC_META_DATA_WORD));
    }

    inline uint8_t* allocateSafe(const BSQType* mdata)
    {
        uint8_t* alloc = this->bumpalloc.allocateSafe(mdata->allocinfo.heapsize);

        GC_INIT_BUMP_SPACE_ALLOC(alloc, mdata->tid);
        return (alloc + sizeof(GC_META_DATA_WORD));
    }

    template <bool eager>
    inline uint8_t* allocateDynamicRC(const BSQType* mdata)
    {
        size_t asize = mdata->allocinfo.heapsize;
        uint8_t* alloc = mi_zalloc_small(asize);

        if constexpr (eager)
        {
            GC_INIT_EAGER_RC(alloc, mdata->tid);
        }
        else
        {
            GC_INIT_RC(alloc, mdata->tid);
            this->maybeZeroCounts.enque(alloc);
        }
        
        return (alloc + sizeof(GC_META_DATA_WORD));
    }

    template <typename T>
    inline T* eagerRCInc(T* v)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
        GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

        GC_SET_META_DATA_WORD(addr, GC_INIT_RC(w));
        return v;
    }

    template <typename T>
    inline T* eagerRCRelax(T* v)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
        GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

        GC_SET_META_DATA_WORD(addr, GC_CLEAR_EAGER_RC_BIT(w));
        this->maybeZeroCounts.enque(v);

        return v;
    }

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->bumpalloc.currentAllocatedSlabBytes() + this->rcalloc + this->liveoldspace));

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
        this->bumpalloc.postGCProcess(this->liveoldspace);
        this->rcalloc = 0;

        if(this->globals_mem != nullptr)
        {
            Allocator::gcMakeImmortalSlotsWithMask((void**)Allocator::GlobalAllocator.globals_mem, Allocator::GlobalAllocator.globals_mask);

            mi_free(Allocator::GlobalAllocator.globals_mem);
            Allocator::GlobalAllocator.globals_mem = nullptr;
        }
    }

    void setGlobalsMemory(void* globals, const RefMask mask)
    {
        this->globals_mem = globals;
        this->globals_mask = mask;
    }
};
