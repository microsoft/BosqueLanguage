//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
//I want this for valloc but seems like I need to do windows.h (#include "memoryapi.h")
#else
#include <sys/mman.h>
#include <unistd.h>
#endif

#define DEFAULT_PAGE_COST 2
#define MAX_PAGE_COST 16
#define COLLECT_ALL_PAGE_COST ((uint32_t)4294967296)
#define DEFAULT_POST_COLLECT_RUN_DECS_COST 1024

#define DEFAULT_DEC_OPS_COUNT 256

#define OCCUPANCY_LOW_MID_BREAK 0.30f
#define OCCUPANCY_MID_HIGH_BREAK 0.85f

#define FREE_PAGE_MIN 256
#define FREE_PAGE_RATIO 0.2f

////
//Alloc page grouping
class AllocPages
{
public:
    //(1-30%, 31-85%, 86-100%) -- this is fuzzy, based on the utilization when we put them in the list but dec ops may change it over time
    std::set<PageInfo*> low_utilization; //keep in memory order
    std::list<PageInfo*> mid_utilization;
    std::set<PageInfo*> high_utilization;

    static PageInfo g_sential_page;
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

    size_t tableEntrySize;
    size_t tableEntryCount;

    AllocPages allocatedPages;
    std::set<PageInfo*> filledPages; //pages that have been filled by the allocator and are pending collection -- this overlaps with the one in the block allocator but we have it here to so we can process pages of this type when needed

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name): 
        allocpage(&AllocPages::g_sential_page), evacuatepage(&AllocPages::g_sential_page), tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), fpkeycmp(fpkeycmp), vtable(vtable), fpDisplay(fpDisplay), name(name)
    {
        static_assert(sizeof(PageInfo) % 8 == 0);

        this->tableEntrySize = allocinfo.heapsize;

#ifdef ALLOC_DEBUG_CANARY
        this->tableEntrySize += ALLOC_DEBUG_CANARY_SIZE;
#endif

        this->tableEntryCount = (size_t)((float)(8192 - sizeof(PageInfo)) / (float)(sizeof(GC_META_DATA_WORD) + this->tableEntrySize));
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

    static bool global_init_complete;
    static PageInfo* global_memory;
    static BSQType* global_type;

    //TODO: eventually want a list of these as they must broken up into page size

    static void reset(uint8_t* argsend)
    {
        stackp = argsend;
    }

    inline static uint8_t* allocFrame(size_t bytes)
    {
        assert((GCStack::stackp - GCStack::sdata) < BSQ_MAX_STACK);
        
        uint8_t* frame = GCStack::stackp;

        //Not required but useful for preventing false pointers -- When we compile might want to only include this prolog on non-leaf or allocating functions (or something similar)
        GC_MEM_ZERO(frame, bytes);

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

#ifdef ALLOC_FIXED_MEM_ADDR
    uint8_t* dbg_known_mem_range = nullptr;
    void dbg_try_reserve_page_range()
    {
            uintptr_t known_addr = 68719476736ul; //2^36
            size_t asize = 134217728ul; //2^27

#ifdef _WIN32
            //https://docs.microsoft.com/en-us/windows/win32/memory/reserving-and-committing-memory
            this->dbg_known_mem_range = (uint8_t*)VirtualAlloc(reinterpret_cast<void*>(known_addr), asize, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
            assert(this->dbg_known_mem_range != nullptr);
#else
            this->dbg_known_mem_range = (uint8_t*)mmap(reinterpret_cast<void*>(known_addr), asize, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            assert(this->dbg_known_mem_range != MAP_FAILED);
#endif

            if(this->dbg_known_mem_range != reinterpret_cast<void*>(known_addr))
            {
                this->dbg_known_mem_range = nullptr;
                assert(false); //lets flag this and see if/when it triggers
            }
    }
#endif

#ifdef ALLOC_DEBUG_CANARY
    static void checkCanary(void* addr)
    {
        if(((uintptr_t)addr & PAGE_ADDR_MASK) != (uintptr_t)addr)
        {
            size_t* curr = (size_t*)(((uint8_t*)addr) - ALLOC_DEBUG_CANARY_SIZE);
            while(curr < addr)
            {
                assert(*curr == ALLOC_DEBUG_MEM_INITIALIZE_VALUE);
                curr++;
            }
        }
    }

    static void checkAllCanariesOnPage(PageInfo* page)
    {
        for(size_t i = 0; i < page->alloc_entry_count; ++i)
        {
            if(GC_IS_ALLOCATED(page->slots[i]))
            {
                checkCanary(GC_GET_OBJ_AT_INDEX(page, i));
            }
        }
    }

    void checkAllCanaries()
    {
        for(auto iter = this->page_set.cbegin(); iter != this->page_set.cend(); ++iter)
        {
            checkAllCanariesOnPage(*iter);
        }
    }
#endif

    void initializePageFreelist(PageInfo* p)
    {
        p->freelist = nullptr;
        p->freelist_count = p->alloc_entry_count;

        GC_MEM_ZERO(p->slots, p->alloc_entry_count * sizeof(GC_META_DATA_WORD));

#ifdef ALLOC_DEBUG_MEM_INITIALIZE
        GC_MEM_FILL(p->data, p->alloc_entry_count * p->alloc_entry_size, ALLOC_DEBUG_MEM_INITIALIZE_VALUE);
#endif

        void** curr = &p->freelist;
        GC_META_DATA_WORD* metacurr = p->slots;
        uint8_t* datacurr = (uint8_t*)(p->data);

        for(uint64_t i = 0; i < p->alloc_entry_count; ++i)
        {
            *((void**)datacurr) = *curr;
            *((void**)datacurr + 1) = metacurr;

            *curr = (void*)datacurr;

            metacurr++;
            datacurr += p->alloc_entry_size;
        }
    }

    void initializeFreshPageForType(PageInfo* p, BSQType* btype)
    {
        p->alloc_entry_size = btype->tableEntrySize;
        p->alloc_entry_count = btype->tableEntryCount;
        
        p->btype = btype;

        p->allocinfo = 0x0;
    }

    void unlinkPageFromType(PageInfo* p)
    {
        p->alloc_entry_size = 0;
        p->alloc_entry_count = 0;
        
        p->btype = nullptr;

        p->allocinfo = 0x0;
    }

    PageInfo* allocateFreePageMemOp()
    {
#ifdef ALLOC_FIXED_MEM_ADDR
        if(this->dbg_known_mem_range != nullptr)
        {
            auto pp = (PageInfo*)this->dbg_known_mem_range;
            this->dbg_known_mem_range += BSQ_BLOCK_ALLOCATION_SIZE;

            return pp;
        }
#endif

#ifdef _WIN32
            //https://docs.microsoft.com/en-us/windows/win32/memory/reserving-and-committing-memory
            auto pp = (PageInfo*)VirtualAlloc(nullptr, BSQ_BLOCK_ALLOCATION_SIZE, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
            assert(pp != nullptr);

            return pp;
#else
            void* ppstart = (PageInfo*)mmap(nullptr, 2 * BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            assert(ppstart != MAP_FAILED);

            auto pagesize = sysconf(_SC_PAGESIZE);
            uint8_t* pplcurr = (uint8_t*)ppstart;
            while((((uintptr_t)pplcurr) & PAGE_ADDR_MASK) != ((uintptr_t)pplcurr))
            {
                pplcurr = pplcurr + pagesize;
            }
            auto ldist = std::distance((uint8_t*)ppstart, pplcurr);
            if(ldist != 0)
            {
                auto rr = munmap(ppstart, ldist);
                assert(rr != -1);
            }

            uint8_t* pplend = pplcurr + BSQ_BLOCK_ALLOCATION_SIZE;
            auto rdist = std::distance(pplend, (uint8_t*)ppstart + 2 * BSQ_BLOCK_ALLOCATION_SIZE);
            if(rdist != 0)
            {
                auto rr = munmap(pplend, rdist);
                assert(rr != -1);
            }

            auto pp = (PageInfo*)pplcurr;

            return pp;
#endif   
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
            pp = this->allocateFreePageMemOp();
            pp->slots = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo));
            pp->data = (GC_META_DATA_WORD*)((uint8_t*)pp + sizeof(PageInfo) + btype->tableEntryCount * sizeof(GC_META_DATA_WORD));

            this->page_set.insert(pp);

            assert(MIN_ALLOCATED_ADDRESS < ((uintptr_t)pp));
            assert(((uintptr_t)pp) < MAX_ALLOCATED_ADDRESS);
        }

        this->initializeFreshPageForType(pp, btype);
        this->initializePageFreelist(pp);

        return pp;
    }

    void releasePage(PageInfo* pp)
    {
#ifdef ALLOC_FIXED_MEM_ADDR
        if(this->dbg_known_mem_range != nullptr)
        {
            return;
        }
#endif

#ifdef _WIN32
        VirtualFree(pp, 0, MEM_RELEASE);
#else
        munmap(pp, BSQ_BLOCK_ALLOCATION_SIZE);
#endif
    }

    PageInfo* processAndGetNewPageForEvacuation(BSQType* btype)
    {
        if(btype->evacuatepage == &AllocPages::g_sential_page)
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
        return btype->evacuatepage;
    }
    
    PageInfo* processAndGetNewPageForAllocation(BSQType* btype)
    {
        if(btype->allocpage == &AllocPages::g_sential_page)
        {
            btype->allocpage = this->allocateFreePage(btype);
            btype->allocpage->allocinfo = AllocPageInfo_Alloc;
        }
        else
        {
            btype->allocpage->allocinfo = btype->allocpage->allocinfo & AllocPageInfo_EvCandidate;
            this->filled_pages.insert(btype->allocpage);

            if(!btype->allocatedPages.low_utilization.empty())
            {
                btype->allocpage = *(btype->allocatedPages.low_utilization.begin());
                btype->allocatedPages.low_utilization.erase(btype->evacuatepage);
            }
            else if(!btype->allocatedPages.mid_utilization.empty())
            {
                btype->allocpage = btype->allocatedPages.mid_utilization.front();
                btype->allocatedPages.mid_utilization.pop_front();
            }
            else
            {
                btype->allocpage = this->allocateFreePage(btype);
            }

            btype->allocpage->allocinfo = btype->allocpage->allocinfo | AllocPageInfo_Alloc;
        }

        return btype->allocpage;
    }
};

class Allocator
{
public:
    static Allocator GlobalAllocator;

private:
    BlockAllocator blockalloc;
    GCRefList worklist;
    void* pendingdecs;

    std::set<void*> oldroots;
    GCRefList roots;
    GCRefList evacobjs;
    std::list<PageInfo*> activeallocprocessing; //pages that need to be processed in the STW phase since we are actively allocating from them

    std::set<BSQCollectionIterator*> activeiters;

    //"cost" to get a new page -- pay by doing defered decs, processing pages, or (later running some scavanging if needed)
    //    can adjust to make sure we keep up with alloc/free -- but start out with a cost of 2
    size_t page_cost;
    size_t dec_ops_count;
    size_t post_release_dec_ops_count;
    size_t current_allocated_bytes;

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

    inline static void gcProcessSlotWithCollection(void** slot, void* fromObj)
    {
        if (!IS_EMPTY_COLLECTION(*slot))
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
                case PTR_FIELD_MASK_COLLECTION:
                    Allocator::gcProcessSlotWithCollection(cslot, fromObj);
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

    inline static void gcDecrementCollection(void** v)
    {
        if (!IS_EMPTY_COLLECTION(*v))
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
                case PTR_FIELD_MASK_COLLECTION:
                    Allocator::gcDecrementCollection(cslot);
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

    inline static void gcEvacuateCollection(void** slot, void* obj)
    {
        if (!IS_EMPTY_COLLECTION(*slot))
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
                case PTR_FIELD_MASK_COLLECTION:
                    Allocator::gcEvacuateCollection(cslot, obj);
                    break;
                default:
                    Allocator::gcEvacuateWithUnion(cslot, obj);
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
#else
                auto sweepobj = GC_GET_OBJ_AT_INDEX(pp, i);

                GC_DBG_PAGE_FREE(sweepobj);
                sweepobj = (void*)GC_DBG_PAGE_ALLOC(pp->btype->allocinfo.heapsize);
                PAGE_MASK_SET_ID(sweepobj, pp);

                *((void**)(pp->data) + i) = sweepobj;

                **((void***)pp->data + i) = pp->freelist;
                *(*((void***)pp->data + i) + 1) = metacurr;

                pp->freelist = *((void**)pp->data + i);
#endif

                pp->freelist_count++;
                *metacurr = 0x0;
            }
            
            if constexpr (evacrc)
            {
                if(GC_IS_LIVE(w) & GC_RC_IS_PARENT(w))
                {
                    void* parent = GC_RC_GET_PARENT(w);
                    BSQType* ptype = PAGE_MASK_EXTRACT_ADDR(parent)->btype;

#ifndef DEBUG_ALLOC_BLOCKS
                    ptype->gcops.fpProcessMoveObj(ptype, (void**)parent, (void*)datacurr);
#else
                    auto evacobj = GC_GET_OBJ_AT_INDEX(pp, i);
                    ptype->gcops.fpProcessMoveObj(ptype, (void**)parent, evacobj);
#endif
                
                    if(!GC_IS_MARKED(w))
                    {
#ifndef DEBUG_ALLOC_BLOCKS
                        this->evacobjs.enque((void*)datacurr);
#else
                        this->evacobjs.enque(evacobj);
#endif
                    }
                }
            }
            else
            {
                allrcsimple = allrcsimple & GC_HAS_RC_DATA(w) & GC_RC_IS_PARENT(w);
            }

            metacurr++;

#ifndef DEBUG_ALLOC_BLOCKS
            datacurr += pp->entry_size;
#endif
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

        for(auto iter = this->activeiters.begin(); iter != this->activeiters.end(); iter++)
        {
            this->gcCopyRoots((uintptr_t)(*iter)->lcurr);

            for(size_t i = 0; i < (*iter)->iterstack.size(); ++i)
            {
                this->gcCopyRoots((uintptr_t)(*iter)->iterstack[i]);
            }
        }

#ifndef DEBUG_ALLOC_BLOCKS
        void* groot = GCStack::global_memory->data;
#else
        void* groot = *((void**)GCStack::global_memory->data);
#endif
        if(GCStack::global_init_complete)
        {
            //treat it like a single root to the globals object
            this->gcCopyRoots(*((uintptr_t*)groot));
        }
        else
        {
            //treat it like a stack frame thing
            uint8_t* gend = ((uint8_t*)groot + (GCStack::global_type->allocinfo.heapsize));
            for(uint8_t* curr = (uint8_t*)groot; curr < gend; curr += ICPP_WORD_SIZE)
            {
                this->gcCopyRoots(*((uintptr_t*)curr));
            }
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

        uint64_t live_bytes = std::accumulate(this->blockalloc.page_set.cbegin(), this->blockalloc.page_set.cend(), (uint64_t)0, [](uint64_t acc, PageInfo* p) {
            return acc + (uint64_t)(p->entry_size - p->freelist_count);
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

#ifdef DEBUG_ALLOC_BLOCKS
                auto idx = GC_PAGE_INDEX_FOR_ADDR(decobj, pp);

                GC_DBG_PAGE_FREE(decobj);
                decobj = (void*)GC_DBG_PAGE_ALLOC(pp->btype->allocinfo.heapsize);
                PAGE_MASK_SET_ID(decobj, pp);
                *((void**)(pp->data) + idx) = decobj;
#endif

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

        if(this->blockalloc.free_pages.size() > FREE_PAGE_MIN)
        {
            auto freeratio = (float)this->blockalloc.free_pages.size() / (float)this->blockalloc.page_set.size();
            if(freeratio > FREE_PAGE_RATIO)
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
    Allocator() : blockalloc(), worklist(), pendingdecs(nullptr), oldroots(), roots(), evacobjs(), activeallocprocessing(), activeiters(), page_cost(DEFAULT_PAGE_COST), dec_ops_count(DEFAULT_DEC_OPS_COUNT), post_release_dec_ops_count(DEFAULT_POST_COLLECT_RUN_DECS_COST)
    {
        MEM_STATS_OP(this->gccount = 0);
        MEM_STATS_OP(this->maxheap = 0);
    }

    ~Allocator()
    {
        ;
    }

    inline uint8_t* allocateDynamic(const BSQType* mdata)
    {
        PageInfo* pp = mdata->allocpage;
        if(pp->freelist == nullptr)
        {
            pp = this->allocate_slow(const_cast<BSQType*>(mdata));
        }
        
        uint8_t* alloc = (uint8_t*)pp->freelist;
        *((GC_META_DATA_WORD*)(*((void**)pp->freelist + 1))) = GC_ALLOCATED_BIT;

        pp->freelist = *((void**)pp->freelist);
        pp->freelist_count--;

        return alloc;
    }

    void insertCollectionIter(BSQCollectionIterator* iter)
    {
        this->activeiters.insert(iter);
    }

    void removeCollectionIter(BSQCollectionIterator* iter)
    {
        this->activeiters.erase(iter);
    }

    void setGlobalsMemory(const BSQType* global_type)
    {
        GCStack::global_memory = this->blockalloc.allocateFreePage(const_cast<BSQType*>(global_type));
        GCStack::global_type = const_cast<BSQType*>(global_type);
        GCStack::global_init_complete = false;
    }

    void completeGlobalInitialization()
    {
        GCStack::global_init_complete = true;

        //Maybe we want to force a collect here or even a very aggressive compact
        //this->collect();
    }
};

void gcProcessHeapOperator_nopImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_inlineImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_refImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_stringImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_bignumImpl(const BSQType* btype, void** data, void* fromObj);
void gcProcessHeapOperator_collectionImpl(const BSQType* btype, void** data, void* fromObj);

void gcDecOperator_nopImpl(const BSQType* btype, void** data);
void gcDecOperator_inlineImpl(const BSQType* btype, void** data);
void gcDecOperator_refImpl(const BSQType* btype, void** data);
void gcDecOperator_stringImpl(const BSQType* btype, void** data);
void gcDecOperator_bignumImpl(const BSQType* btype, void** data);
void gcDecOperator_collectionImpl(const BSQType* btype, void** data);

void gcEvacuateOperator_nopImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_inlineImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_refImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_stringImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_bignumImpl(const BSQType* btype, void** data, void* obj);
void gcEvacuateOperator_collectionImpl(const BSQType* btype, void** data, void* obj);

constexpr GCFunctorSet REF_GC_FUNCTOR_SET{ gcProcessHeapOperator_refImpl, gcDecOperator_refImpl, gcEvacuateOperator_refImpl };
constexpr GCFunctorSet STRUCT_LEAF_GC_FUNCTOR_SET{ gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcEvacuateOperator_nopImpl };
constexpr GCFunctorSet STRUCT_STD_GC_FUNCTOR_SET{ gcProcessHeapOperator_inlineImpl, gcDecOperator_inlineImpl, gcEvacuateOperator_inlineImpl };
constexpr GCFunctorSet REGISTER_GC_FUNCTOR_SET{ gcProcessHeapOperator_nopImpl, gcDecOperator_nopImpl, gcEvacuateOperator_nopImpl };

