//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#ifdef _WIN32
#include "memoryapi.h"
#else
#endif

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;

    const BSQTypeID tid;
    const BSQTypeLayoutKind tkind;
    
    const BSQTypeSizeInfo allocinfo;
    const GCFunctorSet gcops;

    KeyCmpFP fpkeycmp;
    const std::map<BSQVirtualInvokeID, BSQInvokeID> vtable; //TODO: This is slow indirection but nice and simple

    DisplayFP fpDisplay;
    const std::string name;

    size_t allocpageCount;
    PageInfo* allocpages;

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name): 
        tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), fpkeycmp(fpkeycmp), vtable(vtable), fpDisplay(fpDisplay), name(name)
    {;}

    virtual ~BSQType() {;}

    inline bool isLeaf() const
    {
        return this->allocinfo.heapmask == nullptr;
    }

    virtual bool isUnion() const
    {
        return false;
    }

    virtual void clearValue(StorageLocationPtr trgt) const = 0;
    virtual void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const = 0;
    virtual StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const = 0;
};

////////////////////////////////
//Core Malloc
inline void* xalloc(size_t alloc)
{
    return malloc(alloc);
}

inline void* zxalloc(size_t alloc)
{
    void* vv = malloc(alloc);
    GC_MEM_ZERO(vv, alloc);

    return vv;
}

inline void xfree(void* mem)
{
    free(mem);
}

////////////////////////////////
//Storage Operators

class BSQCollectionIterator
{
public:
    std::vector<void*> iterstack;
    void* lcurr;

    BSQCollectionIterator(): iterstack(), lcurr(nullptr) {;}
    virtual ~BSQCollectionIterator() {;}
};

//
//TODO: this should all end up using the actual call stack and walked via ASM (interpreter just stack allocs for data and C compiler frames are in there too)
//      lets go look at chakra for this
//
class GCStack
{
public:
    static void** frames[BSQ_MAX_STACK];
    static uint32_t stackp;

    static void reset()
    {
        stackp = 1;
    }

    inline static void pushFrame(void** framep)
    {
        if (GCStack::stackp < BSQ_MAX_STACK)
        {
            GCStack::frames[GCStack::stackp++] = framep;
        }
        else
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
        this->headrl = (void**)zxalloc(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
        this->tailrl = this->headrl;
    }

    ~GCRefList()
    {
        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            xfree(tmp);
        }
    }

    void assignFrom(GCRefList& other)
    {
        assert(this != &other);

        while(this->headrl != nullptr)
        {
            auto tmp = this->headrl;
            this->headrl = (void**)this->headrl[0];

            xfree(tmp);
        }

        this->headrl = other.headrl;
        this->tailrl = other.tailrl;
        this->spos = other.spos;
        this->epos = other.epos;

        other.headrl = (void**)zxalloc(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
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

            xfree(tmp);
        }

        this->headrl = (void**)zxalloc(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
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
        void** tmp = (void**)zxalloc(GC_REF_LIST_BLOCK_SIZE_DEFAULT * sizeof(void*));
        this->tailrl[0] = tmp;
        this->tailrl = tmp;
        this->epos = 1;
    }

    inline void enque(void* v)
    {
        if(this->epos < GC_REF_LIST_BLOCK_SIZE_DEFAULT)
        {
            this->tailrl[this->epos++] = v;
        }
        else
        {
            this->enqueSlow(v);
        }
    }

    void* dequeSlow()
    {
        void** tmp = this->headrl;
    
        this->headrl = (void**)this->headrl[0];
        this->spos = 2;

        xfree(tmp);
        return this->headrl[1];
    }

    inline void* deque()
    {
        assert(!this->empty());

        if(this->spos < GC_REF_LIST_BLOCK_SIZE_DEFAULT)
        {
            return this->tailrl[this->spos++];
        }
        else
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
        if(iter.cpos < GC_REF_LIST_BLOCK_SIZE_DEFAULT)
        {
            iter.cpos++;
        }
        else
        {
            this->iterAdvanceSlow(iter);
        }
    }
};

//A class that implements our block allocator stuff
class BlockAllocator
{
public:
    //set of all pages that are currently allocated
    std::set<PageInfo*> page_set;
    std::list<PageInfo*> free_pages;

#ifndef ALLOC_BLOCKS
    //For malloc based debug implementation we keep explicit map from object to page it is in
    std::map<void*, PageInfo*> page_map;
#endif

    inline bool isAddrAllocated(void* addr) const
    {
        auto pageiter = this->page_set.find(PAGE_MASK_EXTRACT(addr));
        if(pageiter == this->page_set.cend() || !(*pageiter)->inuse)
        {
            return false;
        }
        else
        {
            auto ooidx = GC_PAGE_INDEX_FOR_ADDR(addr, *pageiter);
            auto meta = GC_LOAD_META_DATA_WORD(GC_GET_META_DATA_ADDR_AND_PAGE(addr, *pageiter));
            return GC_IS_ALLOCATED(meta);
        }
    }

    inline void allocatePageForType(BSQType* btype)
    {
        PageInfo* pp = nullptr;
        if(!this->free_pages.empty())
        {
            pp = this->free_pages.front();
            this->free_pages.pop_front();
        }
        else
        {
#ifdef ALLOC_BLOCKS
#ifdef _WIN32
            //https://docs.microsoft.com/en-us/windows/win32/memory/reserving-and-committing-memory
            pp = (PageInfo*)VirtualAlloc(nullptr, BSQ_BLOCK_ALLOCATION_SIZE, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
            assert(pp != nullptr); //failed for some reason
            assert(((uintptr_t)pp) < MAX_ALLOCATED_ADDRESS);

            pp->slots = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo));
            pp->data = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo) + btype->tableEntryCount * sizeof(GC_META_DATA_WORD));
#else
            xxxx;
#endif
#else
            pp = new PageInfo();
            pp->slots = (GC_META_DATA_WORD*)zxalloc(btype->tableEntryCount * sizeof(GC_META_DATA_WORD));
            pp->data = (void*)zxalloc(btype->tableEntryCount * sizeof(void*));
#endif
        }

#ifndef ALLOC_BLOCKS
        for(size_t i = 0; i < btype->tableEntryCount; ++i)
        {
            *((void**)(pp->data) + i) = (void*)zxalloc(btype->allocinfo.heapsize);
        }
#endif

        pp->pageid = this->page_set.size();
        pp->entry_size = btype->allocinfo.heapsize;
        pp->entry_count = btype->tableEntryCount;
        pp->entry_available_count = btype->tableEntryCount;

        pp->tid = btype->tid;
        pp->type = btype;
        pp->idxshift = btype->tableEntryIndexShift;

        pp->inuse = true;
        pp->next = btype->allocpages;
        pp->prev = nullptr;

        btype->allocpages->prev = pp;
        btype->allocpages = pp;
        this->page_set.insert(pp);
    }
};




class BumpSpaceAllocator
{
private:
    //We inline the fields for the current/end of the block that we are allocating from
    uint8_t *m_currPos;
    uint8_t *m_endPos;

    size_t m_allocsize;
    uint8_t* m_block;

#ifdef ENABLE_MEM_STATS
    size_t totalbumpalloc;
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

        if(this->m_currPos + rsize > this->m_endPos)
        {
             this->ensureSpace_slow();
        }

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }

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

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
};

class Allocator
{
public:
    static Allocator GlobalAllocator;

    

#ifdef BSQ_DEBUG_BUILD
    static std::map<size_t, std::pair<const BSQType*, void*>> dbg_idToObjMap;

    static void resetDbgObjIDMap(void* obj)
    {
        Allocator::dbg_idToObjMap.clear();
    }

    static std::string registerDbgObjID(const BSQType* btype, void* obj)
    {
        auto id = Allocator::dbg_idToObjMap.size();
        Allocator::dbg_idToObjMap[id] = std::make_pair(btype, obj);

        return std::string("*") + std::to_string(id);
    }
#endif

    void reset()
    {
        Allocator::collectionnodesend = Allocator::collectionnodes;

        Allocator::collectioniters.clear();
        Allocator::alloctemps.clear();

        Allocator::dbg_idToObjMap.clear();
    }

private:

    BumpSpaceAllocator bumpalloc;

    bool gcEnabled; //can turn off collector for a bit if we want
    bool compactionEnabled; //can turn off compaction for a bit if we want

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
    void* moveBumpObjectToOldRCSpace(void* obj, GC_META_DATA_WORD* addr, GC_META_DATA_WORD w, const BSQType* ometa, size_t osize)
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

public:
        inline void processIncHeapRC(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta, void* fromObj)
    {
        if(GC_RC_IS_COUNT(meta))
        {
            GC_STORE_META_DATA_WORD(addr, GC_INC_RC_COUNT(meta));
        }
        else
        {
            if(GC_RC_IS_PARENT_CLEAR(GC_RC_GET_PARENT1(meta)))
            {
                GC_STORE_META_DATA_WORD(addr, ((GC_PAGE_NUMBER_FOR_ADDR(fromObj) << GC_RC_PAGE1_SHIFT) | GC_ALLOCATED_BIT | GC_EXTRACT_TYPEID(meta)));
            }
            else if(GC_RC_IS_PARENT_CLEAR(GC_RC_GET_PARENT2(meta)))
            {
                GC_STORE_META_DATA_WORD(addr, ((GC_PAGE_NUMBER_FOR_ADDR(fromObj) << GC_RC_PAGE2_SHIFT) | meta));
            }
            else
            {
                GC_STORE_META_DATA_WORD(addr, (GC_RC_KIND_MASK | GC_RC_THREE | GC_ALLOCATED_BIT | GC_EXTRACT_TYPEID(meta)));
            }
        }
    }

    inline void processDecHeapRC(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta, void* fromObj) 
    {
        if(GC_RC_IS_COUNT(meta))
        {
            GC_STORE_META_DATA_WORD(addr, GC_DEC_RC_COUNT(meta));
        }
        else
        {
            auto parent = GC_PAGE_NUMBER_FOR_ADDR(fromObj);
            if(GC_RC_GET_PARENT2(meta) == parent)
            {
                //delete parent 2
                GC_STORE_META_DATA_WORD(addr, ((GC_PAGE_NUMBER_FOR_ADDR(fromObj) << GC_RC_PAGE1_SHIFT) | GC_ALLOCATED_BIT | GC_EXTRACT_TYPEID(meta)));
            }
            else
            {
                //That is really bad
                assert(GC_RC_GET_PARENT1(meta) == parent);

                //shift parent 2 to parent 1
                GC_STORE_META_DATA_WORD(addr, (GC_RC_KIND_MASK | GC_RC_THREE | GC_ALLOCATED_BIT | GC_EXTRACT_TYPEID(meta)));
            }
        }
    }

    inline void processDecHeapRC_DuringCollection(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta, void* fromObj)
    {
        Allocator::processDecHeapRC(addr, meta, fromObj);

        if(GC_TEST_IS_UNREACHABLE(GC_LOAD_META_DATA_WORD(addr)))
        {
            xxxx; //this goes on dealloc processing list
        }
    }

    inline void processDecHeapRC_DuringCompaction(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta, void* fromObj)
    {
        Allocator::processDecHeapRC(addr, meta, fromObj);

        if(GC_TEST_IS_UNREACHABLE(GC_LOAD_META_DATA_WORD(addr)))
        {
            xxxx; //this goes on maybe 0 list
        }
    }

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

                *slot = Allocator::GlobalAllocator.moveBumpObjectToOldRCSpace<isRoot>(v, addr, w, ometa, osize);
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

        BSQCollectionGCReprNode* cni = Allocator::collectionnodes;
        while(cni < Allocator::collectionnodesend)
        {
            Allocator::gcProcessSlot<true>(&(cni->repr));
        }

        for(auto citer = Allocator::collectioniters.begin(); citer != Allocator::collectioniters.end(); ++citer)
        {
            Allocator::gcProcessSlot<true>(&((*citer)->lcurr));
            for(auto piter = (*citer)->iterstack.begin(); piter != (*citer)->iterstack.end(); piter++)
            {
                Allocator::gcProcessSlot<true>(&(*piter));
            }
        }

        for(auto titer = Allocator::alloctemps.begin(); titer != Allocator::alloctemps.end(); ++titer)
        {
            for(auto iiter = titer->cbegin(); iiter != titer->cend(); ++iiter)
            {
                Allocator::gcProcessSlotsWithMask<true>((void**)iiter->root, iiter->rtype->allocinfo.inlinedmask);
            }
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
        size_t freelimit = (3 * this->bumpalloc.currentAllocatedSlabBytes()) / 2;
        size_t freecount = 0;

        while (!this->releaselist.empty())
        {
            if(freelimit <= freecount)
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

        BSQCollectionGCReprNode* cni = Allocator::collectionnodes;
        while(cni < Allocator::collectionnodesend)
        {
            Allocator::gcClearMark(cni->repr);
        }

        for(auto citer = Allocator::collectioniters.begin(); citer != Allocator::collectioniters.end(); ++citer)
        {
            Allocator::gcClearMark((*citer)->lcurr);
            for(auto piter = (*citer)->iterstack.begin(); piter != (*citer)->iterstack.end(); piter++)
            {
                Allocator::gcClearMark(*piter);
            }
        }

        for(auto titer = Allocator::alloctemps.begin(); titer != Allocator::alloctemps.end(); ++titer)
        {
            for(auto iiter = titer->cbegin(); iiter != titer->cend(); ++iiter)
            {
                Allocator::gcClearMarkSlotsWithMask((void**)iiter->root, iiter->rtype->allocinfo.inlinedmask);
            }
        }
    }

public:
    Allocator() : bumpalloc(), maybeZeroCounts(), newMaybeZeroCounts(), worklist(), releaselist(), liveoldspace(0), globals_mem(nullptr)
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

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->bumpalloc.currentAllocatedSlabBytes() + this->rcalloc + this->liveoldspace));

        //mark and move all live objects out of new space
        this->processRoots();
        this->processHeap();

        //Sweep young roots and look possible unreachable old roots in the old with collect them as needed -- new zero counts are rotated in
        this->checkMaybeZeroCountList();

        //Process release of RC space objects as needed
        this->processRelease();

        //Clear any marks
        this->clearAllMarkRoots();

        //Adjust the new space size if needed and reset/free the newspace allocators
        this->bumpalloc.postGCProcess(this->liveoldspace);
    }

    void setGlobalsMemory(void* globals, const RefMask mask)
    {
        this->globals_mem = globals;
        this->globals_mask = mask;
    }

    void completeGlobalInitialization()
    {
        this->collect();

        Allocator::gcMakeImmortalSlotsWithMask((void**)Allocator::GlobalAllocator.globals_mem, Allocator::GlobalAllocator.globals_mask);

        xfree(Allocator::GlobalAllocator.globals_mem);
        Allocator::GlobalAllocator.globals_mem = nullptr;
    }

    void registerCollectionIterator(BSQCollectionIterator* iter)
    {
        Allocator::collectioniters.push_front(iter);
    }

    void releaseCollectionIterator(BSQCollectionIterator* iter)
    {
        Allocator::collectioniters.erase(std::find(Allocator::collectioniters.begin(), Allocator::collectioniters.end(), iter));
    }

    BSQCollectionGCReprNode* getCollectionNodeCurrentEnd()
    {
        return Allocator::collectionnodesend;
    }

    BSQCollectionGCReprNode* registerCollectionNode(void* val)
    {
        assert(collectionnodesend < collectionnodes + BSQ_MAX_STACK);

        Allocator::collectionnodesend->repr = val;
        return Allocator::collectionnodesend++;
    }

    BSQCollectionGCReprNode* resetCollectionNodeEnd(BSQCollectionGCReprNode* endpoint, void* val=nullptr)
    {
        Allocator::collectionnodesend = endpoint;
        if(val == nullptr)
        {
            return nullptr;
        }
        else
        {
            return this->registerCollectionNode(val);
        }
    }

    void pushTempRootScope()
    {
        Allocator::alloctemps.push_back({});
    }

    std::list<BSQTempRootNode>& getTempRootCurrScope()
    {
        return Allocator::alloctemps.back();
    }

    void popTempRootScope()
    {
        for(auto iter = Allocator::alloctemps.back().begin(); iter != Allocator::alloctemps.back().end(); ++iter)
        {
            xfree(iter->root);
        }

        Allocator::alloctemps.pop_back();
    }

    std::list<BSQTempRootNode>::iterator registerTempRoot(const BSQType* btype)
    {
        void* root = zxalloc(btype->allocinfo.inlinedatasize);
        Allocator::alloctemps.back().emplace_front(btype, root);

        return Allocator::alloctemps.back().begin();
    }
};

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

constexpr GCFunctorSet REF_GC_FUNCTOR_SET{ gcProcessRootOperator_refImpl, gcProcessHeapOperator_refImpl, gcDecOperator_refImpl, gcClearOperator_refImpl, gcMakeImmortalOperator_refImpl };
constexpr GCFunctorSet STRUCT_LEAF_GC_FUNCTOR_SET{ gcProcessRootOperator_nopImpl, gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcClearOperator_nopImpl, gcMakeImmortalOperator_nopImpl };
constexpr GCFunctorSet STRUCT_STD_GC_FUNCTOR_SET{ gcProcessRootOperator_inlineImpl, gcProcessHeapOperator_inlineImpl, gcDecOperator_inlineImpl, gcClearOperator_inlineImpl, gcMakeImmortalOperator_inlineImpl };
constexpr GCFunctorSet REGISTER_GC_FUNCTOR_SET{ gcProcessRootOperator_nopImpl, gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcClearOperator_nopImpl, gcMakeImmortalOperator_nopImpl };

