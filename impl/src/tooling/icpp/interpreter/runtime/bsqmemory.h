//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#ifdef _WIN32
#include "memoryapi.h"
#else
#include <sys/mman.h>
#endif

#define DEFAULT_PAGE_COST 2
#define MAX_PAGE_COST 16
#define COLLECT_ALL_PAGE_COST 4294967296
#define DEFAULT_POST_COLLECT_RUN_DECS_COST 1024

#define DEFAULT_DEC_OPS_COUNT 256

#define OCCUPANCY_LOW_MID_BREAK 0.30f
#define OCCUPANCY_MID_HIGH_BREAK 0.85f

#define FREE_PAGE_MIN 256
#define FREE_PAGE_RATIO 0.1f

////
//Alloc page grouping
class AllocPages
{
public:
    //(1-30%, 31-85%, 86-100%) -- this is fuzzy, based on the utilization when we put them in the list but dec ops may change it over time
    std::set<PageInfo*> low_utilization; //keep in memory order
    std::list<PageInfo*> mid_utilization;
    std::set<PageInfo*> high_utilization;
};

class GeneralMemoryStats
{
public:
    uint64_t total_pages;
    uint64_t empty_pages;

    uint64_t live_bytes;
};

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;

    PageInfo* allocpage;
    PageInfo* evacuatepage;

    const BSQTypeID tid;
    const BSQTypeLayoutKind tkind;
    
    const BSQTypeSizeInfo allocinfo;
    const GCFunctorSet gcops;

    KeyCmpFP fpkeycmp;
    const std::map<BSQVirtualInvokeID, BSQInvokeID> vtable; //TODO: This is slow indirection but nice and simple

    DisplayFP fpDisplay;
    const std::string name;

    size_t tableEntryCount;

    AllocPages allocatedPages;
    std::set<PageInfo*> filledPages; //pages that have been filled by the allocator and are pending collection -- this overlaps with the one in the block allocator but we have it here to so we can process pages of this type when needed

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name, PageInfo* spage): 
        allocpage(spage), evacuatepage(spage), tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), fpkeycmp(fpkeycmp), vtable(vtable), fpDisplay(fpDisplay), name(name)
    {
        static_assert(sizeof(PageInfo) % 8 == 0);

        this->tableEntryCount = (size_t)((float)(8192 - sizeof(PageInfo)) / (float)(sizeof(GC_META_DATA_WORD) + allocinfo.heapsize));
    }

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
    static uint8_t* stackp;
    static uint8_t sdata[BSQ_MAX_STACK];

    static void reset()
    {
        stackp = GCStack::sdata;
        GC_MEM_ZERO(GCStack::sdata, BSQ_MAX_STACK);
    }

    inline static uint8_t* allocFrame(size_t bytes)
    {
        assert((GCStack::stackp - GCStack::sdata) < BSQ_MAX_STACK);
        
        uint8_t* frame = GCStack::stackp;
        GCStack::stackp += bytes;

        return frame;
    }

    inline static void popFrame(size_t bytes)
    {
        GCStack::stackp -= bytes;
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
    //set of all pages that are currently allocated -- TODO: probably want some bitvector and/or semi-hierarchical structure here instead
    std::set<PageInfo*> page_set;
    std::set<PageInfo*> free_pages; //pages that are completely empty

    std::set<PageInfo*> filled_pages; //pages that have been filled by the allocator and are pending collection

    static PageInfo g_sential_page;

#ifdef DEBUG_ALLOC_BLOCKS
    //For malloc based debug implementation we keep explicit map from object to page it is in
    std::map<void*, PageInfo*> page_map;
#endif

    inline bool isAddrAllocated(void* addr, void*& realobj) const
    {
        //TODO: probably want some bitvector and/or semi-hierarchical structure here instead 

        auto pageiter = this->page_set.find(PAGE_MASK_EXTRACT_ADDR(addr));
        if(pageiter == this->page_set.cend() || (*pageiter)->btype == nullptr)
        {
            return false;
        }
        else
        {
            auto ooidx = GC_PAGE_INDEX_FOR_ADDR(addr, *pageiter);
            auto meta = GC_LOAD_META_DATA_WORD(GC_GET_META_DATA_ADDR_AND_PAGE(addr, *pageiter));

            realobj = GC_GET_OBJ_AT_INDEX(*pageiter, ooidx); //if this was an interior pointer get the enclosing object
            return GC_IS_ALLOCATED(meta);
        }
    }

    void initializePageFreelist(PageInfo* p)
    {
        p->freelist = nullptr;
        p->freelist_count = p->entry_count;

        GC_MEM_ZERO(p->slots, p->entry_count * sizeof(GC_META_DATA_WORD));

#ifndef DEBUG_ALLOC_BLOCKS
        void** curr = &p->freelist;
        GC_META_DATA_WORD* metacurr = p->slots;
        uint8_t* datacurr = (uint8_t*)(p->data);

        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            *((void**)datacurr) = *curr;
            *((void**)datacurr + 1) = metacurr;

            *curr = *((void**)datacurr);

            metacurr++;
            datacurr += p->entry_size;
        }

        *curr = nullptr;
#else
        void** curr = &p->freelist;
        GC_META_DATA_WORD* metacurr = p->slots;

        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            **((void***)p->data + i) = *curr;
            *(*((void***)p->data + i) + 1) = metacurr;

            *curr = *((void**)p->data + i);

            metacurr++;
        }

        *curr = nullptr;
#endif
    }

    void initializeFreshPageForType(PageInfo* p, BSQType* btype)
    {
        p->entry_size = btype->allocinfo.heapsize;
        p->entry_count = btype->tableEntryCount;
        
        p->btype = btype;

        p->allocinfo = 0x0;
    }

    void unlinkPageFromType(PageInfo* p)
    {
#ifdef DEBUG_ALLOC_BLOCKS
        for(size_t i = 0; i < p->btype->tableEntryCount; ++i)
        {
            xfree(*((void**)(p->data) + i));
        }
        p->objslots.clear();
#endif

        p->entry_count = 0;
        p->entry_size = 0;
        
        p->btype = nullptr;

        p->allocinfo = 0x0;
    }

    PageInfo* allocateFreePage(BSQType* btype)
    {
        PageInfo* pp = nullptr;
        if(!this->free_pages.empty())
        {
            auto minpageiter = this->free_pages.begin();

            pp = *minpageiter;
            this->free_pages.erase(minpageiter);
        }
        else
        {
#ifndef DEBUG_ALLOC_BLOCKS
#ifdef _WIN32
            //https://docs.microsoft.com/en-us/windows/win32/memory/reserving-and-committing-memory
            pp = (PageInfo*)VirtualAlloc(nullptr, BSQ_BLOCK_ALLOCATION_SIZE, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
            assert(pp != nullptr);
#else
            pp = (PageInfo*)mmap(nullptr, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            assert(pp != MAP_FAILED);
#endif
            pp->slots = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo));
            pp->data = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo) + btype->tableEntryCount * sizeof(GC_META_DATA_WORD));
#else
            pp = (PageInfo*)zxalloc(sizeof(PageInfo));
            pp->slots = (GC_META_DATA_WORD*)zxalloc(btype->tableEntryCount * sizeof(GC_META_DATA_WORD));
            pp->data = (void*)zxalloc(btype->tableEntryCount * sizeof(void*));
#endif
            this->page_set.insert(pp);

            assert(MIN_ALLOCATED_ADDRESS < ((uintptr_t)pp));
            assert(((uintptr_t)pp) < MAX_ALLOCATED_ADDRESS);
        }

#ifdef DEBUG_ALLOC_BLOCKS
        for(size_t i = 0; i < btype->tableEntryCount; ++i)
        {
            void* obj = (void*)zxalloc(btype->allocinfo.heapsize);
            *((void**)(pp->data) + i) = obj;
            pp->objslots[obj] = i;
        }
#endif

        this->initializeFreshPageForType(pp, btype);
        this->initializePageFreelist(pp);

        return pp;
    }

    void releasePage(PageInfo* pp)
    {
#ifndef DEBUG_ALLOC_BLOCKS
#ifdef _WIN32
        VirtualFree(pp, 0, MEM_RELEASE);
#else
        munmap(pp, BSQ_BLOCK_ALLOCATION_SIZE);
#endif
#else
        delete pp;
#endif
    }

    PageInfo* processAndGetNewPageForEvacuation(BSQType* btype)
    {
        if(btype->evacuatepage == &BlockAllocator::g_sential_page)
        {
            btype->evacuatepage = this->allocateFreePage(btype);
        }
        else
        {
            btype->allocatedPages.high_utilization.insert(btype->evacuatepage);
            
            if(!btype->allocatedPages.mid_utilization.empty())
            {
                btype->evacuatepage = btype->allocatedPages.mid_utilization.back();
                btype->allocatedPages.mid_utilization.pop_back();
            }
            else if(!btype->allocatedPages.low_utilization.empty())
            {
                btype->evacuatepage = *(btype->allocatedPages.low_utilization.begin());
                btype->allocatedPages.low_utilization.erase(btype->evacuatepage);
            }
            else
            {
                btype->evacuatepage = this->allocateFreePage(btype);
            }
        }
            
        btype->evacuatepage->allocinfo = AllocPageInfo_Ev;
    }
    
    PageInfo* processAndGetNewPageForAllocation(BSQType* btype)
    {
        if(btype->allocpage == &BlockAllocator::g_sential_page)
        {
            btype->allocpage = this->allocateFreePage(btype);
            btype->allocpage->allocinfo = AllocPageInfo_Alloc;
            return;
        }
        else
        {
            btype->allocpage->allocinfo = btype->allocpage->allocinfo & AllocPageInfo_EvCandidate;
            this->filled_pages.insert(btype->allocpage);

            if(!btype->allocatedPages.low_utilization.empty())
            {
                btype->evacuatepage = *(btype->allocatedPages.low_utilization.begin());
                btype->allocatedPages.low_utilization.erase(btype->evacuatepage);
            }
            else if(!btype->allocatedPages.mid_utilization.empty())
            {
                btype->evacuatepage = btype->allocatedPages.mid_utilization.front();
                btype->allocatedPages.mid_utilization.pop_front();
            }
            else
            {
                btype->evacuatepage = this->allocateFreePage(btype);
            }

            btype->evacuatepage->allocinfo = btype->evacuatepage->allocinfo | AllocPageInfo_Alloc;
        }
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
        Allocator::dbg_idToObjMap.clear();
    }

private:
    BlockAllocator blockalloc;
    GCRefList worklist;
    void* pendingdecs;

    std::set<void*> oldroots;
    GCRefList roots;
    GCRefList evacobjs;
    std::list<PageInfo*> activeallocprocessing; //pages that need to be processed in the STW phase since we are actively allocating from them

    //"cost" to get a new page -- pay by doing defered decs, processing pages, or (later running some scavanging if needed)
    //    can adjust to make sure we keep up with alloc/free -- but start out with a cost of 2
    size_t page_cost;
    size_t dec_ops_count;
    size_t post_release_dec_ops_count;
    size_t current_allocated_bytes;

    uint8_t* globals_mem;
    RefMask globals_mask;

#ifdef ENABLE_MEM_STATS
    size_t gccount;
    std::list<GeneralMemoryStats> heap_stats;
#endif

public:
    inline void processIncHeapRC(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta, void* fromObj)
    {
        if(GC_RC_IS_COUNT(meta))
        {
            GC_STORE_META_DATA_WORD(addr, GC_INC_RC_COUNT(meta));
        }
        else
        {
            if(GC_IS_ZERO_RC(meta))
            {
                GC_STORE_META_DATA_WORD(addr, GC_RC_SET_PARENT(meta, fromObj));
            }
            else
            {
                GC_STORE_META_DATA_WORD(addr, (GC_ALLOCATED_BIT | GC_RC_KIND_MASK | GC_RC_TWO) | meta);
            }
        }
    }

    inline void processDecHeapRC(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta) 
    {
        if(GC_RC_IS_COUNT(meta))
        {
            auto w = GC_DEC_RC_COUNT(meta);
            if(GC_IS_ZERO_RC(w))
            {
                GC_STORE_META_DATA_WORD(addr, w & ~GC_RC_KIND_MASK);
            }
            else
            {
                GC_STORE_META_DATA_WORD(addr, w);
            }
        }
        else
        {
            GC_STORE_META_DATA_WORD(addr, GC_RC_SET_PARENT(meta, nullptr));
        }
    }

    void processDecHeapRC_Slow(void* obj)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
        GC_STORE_META_DATA_WORD(addr, GC_SET_DEC_LIST(this->pendingdecs));

        this->pendingdecs = obj;
    }

    inline void processDecHeapRC(void* obj)
    { 
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
        Allocator::processDecHeapRC(addr, GC_LOAD_META_DATA_WORD(addr));

        if(GC_IS_UNREACHABLE(GC_LOAD_META_DATA_WORD(addr)))
        {
            this->processDecHeapRC_Slow(obj);
        }
    }

    inline void processDecHeapEvacuate(void* obj, void** slot)
    {
        if(obj == *slot)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
            auto ometa = PAGE_MASK_EXTRACT_ADDR(*slot)->btype;

            *slot = Allocator::GlobalAllocator.evacuateObject(*slot, ometa, obj);
            GC_STORE_META_DATA_WORD(addr, GC_RC_SET_PARENT(*addr, nullptr));
        }
    }

    inline void gcCopyRoots(uintptr_t v)
    {
        if((((uintptr_t)GCStack::sdata) <= v) | (v <= ((uintptr_t)GCStack::stackp)))
        {
            return; //it is a pointer to something on the stack -- which gets rooted when that frame is scanned
        }

        if((MIN_ALLOCATED_ADDRESS < v) | (v < MAX_ALLOCATED_ADDRESS))
        {
            return; //it is obviously not a pointer
        }

        void* obj = (void*)v;
        void* resolvedobj = nullptr;
        if(this->blockalloc.isAddrAllocated(obj, resolvedobj))
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(resolvedobj);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);
            
            GC_STORE_META_DATA_WORD(addr, GC_SET_MARK_BIT(w));

            this->roots.enque(resolvedobj);
        }
    }

    inline uint8_t* allocateEvacuate(BSQType* mdata)
    {
        PageInfo* pp = mdata->allocpage;
        if(pp->freelist == nullptr)
        {
            pp = this->blockalloc.processAndGetNewPageForEvacuation(mdata);
        }
        
        uint8_t* alloc = (uint8_t*)pp->freelist;
        *((GC_META_DATA_WORD*)(*((void**)pp->freelist + 1))) = GC_ALLOCATED_BIT;

        pp->freelist = *((void**)pp->freelist);
        pp->freelist_count--;

        return alloc;
    }

    void* evacuateObject(void* obj, BSQType* ometa, void* fromObj)
    {
        void* nobj = this->allocateEvacuate(ometa);
        GC_MEM_COPY(nobj, obj, ometa->allocinfo.heapsize);
        
        GC_META_DATA_WORD* naddr = GC_GET_META_DATA_ADDR(nobj);
        GC_STORE_META_DATA_WORD(naddr, GC_RC_SET_PARENT(GC_ALLOCATED_BIT, fromObj));

        return nobj;
    }

    inline static void gcProcessSlotHeap(void** slot, void* fromObj)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(slot);
        GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);
        
        if(GC_IS_FWD_PTR(w))
        {
            *slot = GC_GET_FWD_PTR(w);
            addr = GC_GET_META_DATA_ADDR(slot);
            w = GC_LOAD_META_DATA_WORD(addr);

            Allocator::GlobalAllocator.processIncHeapRC(addr, w, fromObj);
        }
        else
        {
            if(GC_IS_MARKED(w) | !GC_IS_YOUNG(w))
            {
                Allocator::GlobalAllocator.processIncHeapRC(addr, w, fromObj);
            }
            else
            {
                PageInfo* pp = PAGE_MASK_EXTRACT_ADDR(*slot);
                auto ometa = pp->btype;

                *slot = Allocator::GlobalAllocator.evacuateObject(*slot, ometa, fromObj);
                GC_STORE_META_DATA_WORD(addr, GC_SET_FWD_PTR(*slot));

                //if it is an active alloc page but not yet pending then special enqueue it
                if((pp->allocinfo & (AllocPageInfo_Alloc | AllocPageInfo_Pending)) == AllocPageInfo_Alloc)
                {
                    pp->allocinfo = pp->allocinfo | AllocPageInfo_Pending;
                    Allocator::GlobalAllocator.activeallocprocessing.push_back(pp);
                }

                if (!ometa->isLeaf())
                {
                    Allocator::GlobalAllocator.worklist.enque(*slot);
                }
            }
        }
    }

    inline static void gcProcessSlotWithString(void** slot, void* fromObj)
    {
        if (!IS_INLINE_STRING(*slot))
        {
            Allocator::gcProcessSlotHeap(slot, fromObj);
        }
    }

    inline static void gcProcessSlotWithBigNum(void** slot, void* fromObj)
    {
        if (!IS_INLINE_BIGNUM(*slot))
        {
            Allocator::gcProcessSlotHeap(slot, fromObj);
        }
    }

    inline static void gcProcessSlotsWithUnion(void** slots, void* fromObj)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return (umeta->gcops.fpProcessObjVisit)(umeta, slots + 1, fromObj);
    }

    inline static void gcProcessSlotsWithMask(void** slots, void* fromObj, RefMask mask)
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
                    Allocator::gcProcessSlotHeap(cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcProcessSlotWithString(cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcProcessSlotWithBigNum(cslot, fromObj);
                    break;
                default:
                    Allocator::gcProcessSlotsWithUnion(cslot, fromObj);
                    break;
            }
            cslot++;
        }
    }

    ////////
    //Operations GC decrement
    inline static void gcDecrementString(void** v)
    {
        if (!IS_INLINE_STRING(*v))
        {
            Allocator::GlobalAllocator.processDecHeapRC(*v);
        }
    }

    inline static void gcDecrementBigNum(void** v)
    {
        if (!IS_INLINE_BIGNUM(*v))
        {
            Allocator::GlobalAllocator.processDecHeapRC(*v);
        }
    }

    inline static void gcDecrementSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpDecObj(umeta, slots + 1);
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
                    Allocator::GlobalAllocator.processDecHeapRC(cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcDecrementString(cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcDecrementBigNum(cslot);
                    break;
                default:
                    Allocator::gcDecrementSlotsWithUnion(cslot);
                    break;
            }
            cslot++;
        }
    }

    inline static void gcEvacuateString(void** slot, void* obj)
    {
        if (!IS_INLINE_STRING(*slot))
        {
            Allocator::GlobalAllocator.processDecHeapEvacuate(obj, slot);
        }
    }

    inline static void gcEvacuateBigNum(void** slot, void* obj)
    {
        if (!IS_INLINE_BIGNUM(*slot))
        {
            Allocator::GlobalAllocator.processDecHeapEvacuate(obj, slot);
        }
    }

    inline static void gcEvacuateWithUnion(void** slots, void* obj)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpProcessMoveObj(umeta, slots + 1, obj);
    }

    inline static void gcEvacuateWithMask(void** slots, void* obj, RefMask mask)
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
                    Allocator::GlobalAllocator.processDecHeapEvacuate(obj, cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcEvacuateString(cslot, obj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcEvacuateBigNum(cslot, obj);
                    break;
                default:
                    Allocator::gcEvacuateWithUnion(cslot, obj);
                    break;
            }
            cslot++;
        }
    }

    ////////
    //Operations Make Immortal
    inline static void gcMakeImmortal(void* v)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(v);
        GC_META_DATA_WORD waddr = GC_LOAD_META_DATA_WORD(addr);

        GC_STORE_META_DATA_WORD(addr, GC_INC_RC_COUNT(waddr));
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

    void postsweep_processing(PageInfo* pp, bool allrcsimple)
    {
        if(pp->freelist_count == pp->entry_count)
        {
            //don't put on free list if we are allocating from it
            if((pp->allocinfo & (AllocPageInfo_Alloc | AllocPageInfo_Ev)) != 0x0)
            {
                return;
            }
                        
            this->blockalloc.unlinkPageFromType(pp);
            this->blockalloc.free_pages.insert(pp);
        }
        
        auto utilization = (1.0f - (float)pp->freelist_count) / (float)pp->entry_count;
        pp->allocinfo = 0x0;

        if(utilization > OCCUPANCY_MID_HIGH_BREAK)
        {
            pp->btype->allocatedPages.high_utilization.insert(pp);
        }
        else if(utilization > OCCUPANCY_LOW_MID_BREAK)
        {
            auto ipos = std::find_if(pp->btype->allocatedPages.mid_utilization.begin(), pp->btype->allocatedPages.mid_utilization.end(), [pp](PageInfo* p) {
                return p->freelist_count >= pp->freelist_count;
            });

            pp->btype->allocatedPages.mid_utilization.insert(ipos, pp);
        }
        else
        {
            if(allrcsimple)
            {
                pp->allocinfo = AllocPageInfo_EvCandidate;
            }
            pp->btype->allocatedPages.low_utilization.insert(pp);
        }
    }

    template <bool evacrc>
    void processFilledPage(const BSQType* btype, PageInfo* pp)
    {
        GC_META_DATA_WORD* metacurr = pp->slots;

#ifndef DEBUG_ALLOC_BLOCKS
        uint8_t* datacurr = (uint8_t*)(pp->data);
#endif

        bool allrcsimple = !evacrc;
        for(uint64_t i = 0; i < pp->entry_count; ++i)
        {
            GC_META_DATA_WORD w = *metacurr;
            if(GC_IS_FWD_PTR(w) | GC_IS_UNREACHABLE(w))
            {
#ifndef DEBUG_ALLOC_BLOCKS
                *((void**)datacurr) = pp->freelist;
                *((void**)datacurr + 1) = metacurr;

                pp->freelist = (void*)datacurr;

                pp->freelist_count++;
                *metacurr = 0x0;
#else
                **((void***)p->data + i) = pp->freelist;
                *(*((void***)p->data + i) + 1) = metacurr;

                pp->freelist = *((void**)p->data + i);
#endif
            }
            
            if constexpr (evacrc)
            {
                if(GC_IS_LIVE(w) & GC_RC_IS_PARENT(w))
                {
                    void* parent = GC_RC_GET_PARENT(w);
                    BSQType* ptype = PAGE_MASK_EXTRACT_ADDR(parent)->btype;
                    ptype->gcops.fpProcessMoveObj(ptype, (void**)parent, (void*)datacurr);
                
                    if(!GC_IS_MARKED(w))
                    {
                        this->evacobjs.enque((void*)datacurr);
                    }
                }
            }
            else
            {
                allrcsimple = allrcsimple & GC_HAS_RC_DATA(w) & GC_RC_IS_PARENT(w);
            }

            metacurr++;
            datacurr += pp->entry_size;
        }

        this->postsweep_processing(pp, allrcsimple);
    }

private:
    ////////
    //GC algorithm
    void processRoots()
    {
        for(uint8_t* curr = GCStack::sdata; curr < GCStack::stackp; curr += ICPP_WORD_SIZE)
        {
            this->gcCopyRoots(*((uintptr_t*)curr));
        }

        if(this->globals_mem != nullptr)
        {
            Allocator::gcProcessSlotsWithMask((void**)this->globals_mem, nullptr, this->globals_mask);
        }
    }

    void processHeap()
    {
        while (!this->worklist.empty())
        {
            void* obj = this->worklist.deque();

            const BSQType* umeta = PAGE_MASK_EXTRACT_ADDR(obj)->btype;
            assert(umeta->allocinfo.heapmask != nullptr);

            Allocator::gcProcessSlotsWithMask((void**)obj, obj, umeta->allocinfo.heapmask);
        }
    }

    void checkMaybeZeroCounts()
    {
        for(auto iter = this->oldroots.cbegin(); iter != this->oldroots.cend(); iter++)
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(*iter);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

            if (GC_IS_UNREACHABLE(w))
            {
                GC_STORE_META_DATA_WORD(addr, GC_SET_DEC_LIST(this->pendingdecs));
                this->pendingdecs = *iter;
            }
        }
        this->oldroots.clear();

        GCRefListIterator iter;
        this->evacobjs.iterBegin(iter);
        while(this->evacobjs.iterHasMore(iter))
        {
            auto obj = iter.get();
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);

            if (!GC_IS_UNREACHABLE(w))
            {
                GC_STORE_META_DATA_WORD(addr, GC_SET_DEC_LIST(this->pendingdecs));
                this->pendingdecs = obj;
            }
        }
        this->evacobjs.reset();
    }

    inline static bool dropped_out_of_high_util(PageInfo* pp)
    {
        float prevoccupancy = 1.0f - ((float)pp->entry_count - (float)(pp->freelist_count - 1)) / (float)pp->entry_count;
        float occupancy = 1.0f - ((float)pp->entry_count - (float)pp->freelist_count) / (float)pp->entry_count;

        return (prevoccupancy > OCCUPANCY_MID_HIGH_BREAK) & (occupancy <= OCCUPANCY_MID_HIGH_BREAK);
    }

    void postdec_processing(PageInfo* pp)
    {
        if(pp->freelist_count == pp->entry_count)
        {
            //don't put on free list if we are allocating from it
            if((pp->allocinfo & (AllocPageInfo_Alloc | AllocPageInfo_Ev)) != 0x0)
            {
                return;
            }

            //it is a filled page so just let it get taken care of when we sweep it
            if(pp->btype->filledPages.find(pp) != pp->btype->filledPages.cend())
            {
                return;
            }

            auto luiter = pp->btype->allocatedPages.low_utilization.find(pp);
            auto huiter = pp->btype->allocatedPages.high_utilization.find(pp);

            if(luiter != pp->btype->allocatedPages.low_utilization.cend())
            {
                pp->btype->allocatedPages.low_utilization.erase(luiter);
            }
            else if(huiter != pp->btype->allocatedPages.high_utilization.cend())
            {
                pp->btype->allocatedPages.high_utilization.erase(huiter);
            }
            else
            {
                auto muiter = std::find(pp->btype->allocatedPages.mid_utilization.begin(), pp->btype->allocatedPages.mid_utilization.end(), pp);
                pp->btype->allocatedPages.mid_utilization.erase(muiter);
            }
                        
            this->blockalloc.unlinkPageFromType(pp);
            this->blockalloc.free_pages.insert(pp);
        }
        
        if(Allocator::dropped_out_of_high_util(pp))
        {
            assert(pp->btype->allocatedPages.low_utilization.find(pp) == pp->btype->allocatedPages.low_utilization.cend());

            pp->btype->allocatedPages.high_utilization.erase(pp);
            pp->btype->allocatedPages.mid_utilization.push_back(pp);
        }
    }

    GeneralMemoryStats compute_mem_stats()
    {
//#ifdef GC_SANITY_CHECK
        for(auto piter = this->blockalloc.page_set.cbegin(); piter != this->blockalloc.page_set.cend(); piter++)
        {
            GC_META_DATA_WORD* metacurr = (*piter)->slots;

            uint64_t freecount = 0;
            for(uint64_t i = 0; i < (*piter)->entry_count; ++i)
            {
                if(*metacurr == 0x0)
                {
                    freecount++;
                }
                else
                {
                    assert(GC_IS_ALLOCATED(*metacurr));
                }

                metacurr++;
            }

            assert(freecount == (*piter)->freelist_count);

            if(freecount == 0)
            {
                assert((*piter)->freelist == nullptr);
            }
            else
            {
                assert((*piter)->freelist != nullptr);
            }
        }
//#endif

        uint64_t live_bytes = std::accumulate(this->blockalloc.page_set.cbegin(), this->blockalloc.page_set.cend(), 0, [](uint64_t acc, PageInfo* p) {
            return acc + (p->entry_size - p->freelist_count);
        });

        return GeneralMemoryStats{this->blockalloc.page_set.size(), this->blockalloc.free_pages.size(), live_bytes};
    }

    void processPendingDecs(uint32_t& credits, uint32_t maxcredits)
    {
        for(uint32_t i = 0; i < maxcredits && credits > 0 && this->pendingdecs != nullptr; ++i)
        {
            for(size_t i = 0; i < this->dec_ops_count && this->pendingdecs != nullptr; ++i)
            {
                void* decobj = this->pendingdecs;
                PageInfo* pp = PAGE_MASK_EXTRACT_ADDR(decobj);
                GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR_AND_PAGE(decobj, pp);

                this->pendingdecs = GC_GET_DEC_LIST(*addr);
                pp->btype->gcops.fpDecObj(pp->btype, (void**)decobj);

                GC_STORE_META_DATA_WORD(addr, 0x0);
                *((void**)decobj) = pp->freelist;
                *((void**)decobj + 1) = addr;
                pp->freelist = decobj;
                pp->freelist_count++;

                this->postdec_processing(pp);
            }

            credits--;
        }
    }

    void processBlocks(uint32_t credits, BSQType* mdata)
    {
        while(credits > 0 && !this->blockalloc.filled_pages.empty())
        {
            PageInfo* pp = nullptr;
            if(mdata != nullptr && !mdata->filledPages.empty())
            {
                pp = *(mdata->filledPages.begin());
            }
            else
            {
                pp = *(this->blockalloc.filled_pages.begin());
            }

            if((pp->allocinfo & AllocPageInfo_EvCandidate) != 0x0)
            { 
                this->processFilledPage<true>(pp->btype, pp);
            }
            else
            {
                this->processFilledPage<false>(pp->btype, pp);
            }

            pp->btype->filledPages.erase(pp);
            this->blockalloc.filled_pages.erase(pp);

            credits--;
        }
    }

    void collect()
    {
        MEM_STATS_OP(this->gccount++);
        MEM_STATS_OP(this->heap_stats.push_back(this->compute_mem_stats()));

        if(this->blockalloc.free_pages.size() )
        {
            auto freeratio = (float)this->blockalloc.free_pages.size() / (float)this->blockalloc.page_set.size();
            if(this->blockalloc.free_pages.size() > FREE_PAGE_MIN || freeratio > FREE_PAGE_RATIO)
            {
                auto ratiocount = (size_t)(this->blockalloc.free_pages.size() * FREE_PAGE_RATIO);
                auto trgtfreecount = (FREE_PAGE_MIN < ratiocount) ? FREE_PAGE_MIN : ratiocount;

                auto riter = this->blockalloc.free_pages.rend();
                while(this->blockalloc.free_pages.size() > trgtfreecount)
                {
                    auto delp = *riter;
                    riter++;

                    this->blockalloc.free_pages.erase(delp);
                }
            }
        }

        //clear all the old marks and rotate roots
        GCRefListIterator oriter;
        this->roots.iterBegin(oriter);

        this->oldroots.clear();
        while(this->roots.iterHasMore(oriter))
        {
            void* robj = oriter.get();

            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(robj);
            GC_STORE_META_DATA_WORD(addr, (*addr) & ~GC_MARK_BIT);

            oldroots.insert(robj);

            this->roots.iterAdvance(oriter);
        }
        this->roots.reset();

        //mark and move all live objects out of new space
        this->processRoots();
        this->processHeap();

        //Look at diff in old and new roots + evac operations as starts for dec operations
        this->checkMaybeZeroCounts();

        //We will take credits proportional to the newly allocated memory -- so in general most work is done in the STW phase
        uint32_t credits = this->post_release_dec_ops_count;
        this->processPendingDecs(credits, credits);
    }

    PageInfo* allocate_slow(BSQType* mdata)
    {
        uint32_t credits = this->page_cost;
        bool docollect = false;

        if(this->current_allocated_bytes > BSQ_COLLECT_THRESHOLD)
        {
            credits = COLLECT_ALL_PAGE_COST;
            docollect = true;

            if(this->pendingdecs != nullptr || !this->blockalloc.filled_pages.empty())
            {
                this->page_cost = (this->page_cost < MAX_PAGE_COST) ? (2 * this->page_cost) : MAX_PAGE_COST;
                this->post_release_dec_ops_count = 4 * DEFAULT_POST_COLLECT_RUN_DECS_COST;
            }
            else
            {
                this->page_cost = (this->page_cost > MAX_PAGE_COST) ? (this->page_cost / 2) : DEFAULT_PAGE_COST;
                this->post_release_dec_ops_count = DEFAULT_POST_COLLECT_RUN_DECS_COST;
            }
        }

        if(!docollect)
        {
            this->processPendingDecs(credits, credits / 2);
        }

        this->processBlocks(credits, mdata);

        if(docollect)
        {
            this->collect();
        }

        return this->blockalloc.processAndGetNewPageForAllocation(mdata);
    }

public:
    Allocator() : blockalloc(), worklist(), pendingdecs(nullptr), oldroots(), roots(), evacobjs(), activeallocprocessing(), page_cost(DEFAULT_PAGE_COST), dec_ops_count(DEFAULT_DEC_OPS_COUNT), post_release_dec_ops_count(DEFAULT_POST_COLLECT_RUN_DECS_COST), globals_mem(nullptr), globals_mask(nullptr)
    {
        MEM_STATS_OP(this->gccount = 0);
        MEM_STATS_OP(this->maxheap = 0);
    }

    ~Allocator()
    {
        ;
    }

    inline uint8_t* allocate(BSQType* mdata)
    {
        PageInfo* pp = mdata->allocpage;
        if(pp->freelist == nullptr)
        {
            this->allocate_slow(mdata);
        }
        
        uint8_t* alloc = (uint8_t*)pp->freelist;
        *((GC_META_DATA_WORD*)(*((void**)pp->freelist + 1))) = GC_ALLOCATED_BIT;

        pp->freelist = *((void**)pp->freelist);
        pp->freelist_count--;

        return alloc;
    }

    void setGlobalsMemory(void* globals, RefMask mask)
    {
        this->globals_mem = (uint8_t*)globals;
        this->globals_mask = mask;
    }

    void completeGlobalInitialization()
    {
        this->collect();

        Allocator::gcMakeImmortalSlotsWithMask((void**)this->globals_mem, this->globals_mask);

        xfree(this->globals_mem);
        this->globals_mem = nullptr;
    }
};

void gcProcessHeapOperator_nopImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_inlineImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_refImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data, void* fromObj);

void gcDecOperator_nopImpl(const BSQType* btype, void** data);
void gcDecOperator_inlineImpl(const BSQType* btype, void** data);
void gcDecOperator_refImpl(const BSQType* btype, void** data);
void gcDecOperator_stringImpl(const BSQType* btype, void** data);
void gcDecOperator_bignumImpl(const BSQType* btype, void** data);

void gcEvacuateOperator_nopImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_inlineImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_refImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_stringImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_bignumImpl(const BSQType* btype, void** data, void* obj);

void gcMakeImmortalOperator_nopImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_inlineImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_refImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_stringImpl(const BSQType* btype, void** data);
void gcMakeImmortalOperator_bignumImpl(const BSQType* btype, void** data);

constexpr GCFunctorSet REF_GC_FUNCTOR_SET{ gcProcessHeapOperator_refImpl, gcDecOperator_refImpl, gcEvacuateOperator_refImpl, gcMakeImmortalOperator_refImpl };
constexpr GCFunctorSet STRUCT_LEAF_GC_FUNCTOR_SET{ gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcEvacuateOperator_nopImpl, gcMakeImmortalOperator_nopImpl };
constexpr GCFunctorSet STRUCT_STD_GC_FUNCTOR_SET{ gcProcessHeapOperator_inlineImpl, gcDecOperator_inlineImpl, gcEvacuateOperator_inlineImpl, gcMakeImmortalOperator_inlineImpl };
constexpr GCFunctorSet REGISTER_GC_FUNCTOR_SET{ gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcEvacuateOperator_nopImpl, gcMakeImmortalOperator_nopImpl };

