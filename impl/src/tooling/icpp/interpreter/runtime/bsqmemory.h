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
#define DEFAULT_DEC_OPS_COUNT 256

#define OCCUPANCY_LOW_MID_BREAK 0.30f
#define OCCUPANCY_MID_HIGH_BREAK 0.85f

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
    size_t tableEntryIndexShift;

    AllocPages allocatedPages;
    std::set<PageInfo*> filledPages; //pages that have been filled by the allocator and are pending collection -- this overlaps with the one in the block allocator but we have it here to so we can process pages of this type when needed

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name, PageInfo* spage): 
        allocpage(spage), evacuatepage(spage), tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), fpkeycmp(fpkeycmp), vtable(vtable), fpDisplay(fpDisplay), name(name)
    {
        static_assert(sizeof(PageInfo) % 8 == 0);

        this->tableEntryCount = xxxx;
        this->tableEntryIndexShift = xxxx;
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

#ifndef DEBUG_ALLOC_BLOCKS
        void** curr = &p->freelist;
        GC_META_DATA_WORD* metacurr = p->slots;
        uint8_t* datacurr = (uint8_t*)(p->data);

        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            *curr = *((void**)datacurr);

#ifdef DEBUG_ALLOC_ZERO
            GC_MEM_ZERO(datacurr, p->entry_size); //zero on debug
#endif
            metacurr++;
            datacurr += p->entry_size;
        }

        *curr = nullptr;
#else
        void** curr = &p->freelist;
        GC_META_DATA_WORD* metacurr = p->slots;

        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            *curr = *((void**)p->data + i);

#ifdef DEBUG_ALLOC_ZERO
            GC_MEM_ZERO(*((void**)p->data + i), p->entry_size); //zero on debug
#endif
            metacurr++;
            datacurr += p->entry_size;
        }

        *curr = nullptr;
#endif
    }

    void initializeFreshPageForType(PageInfo* p, BSQType* btype)
    {
        p->entry_size = btype->allocinfo.heapsize;
        p->entry_count = btype->tableEntryCount;
        p->idxshift = btype->tableEntryIndexShift;

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
        p->idxshift = 0;

        p->btype = nullptr;

        p->allocinfo = 0x0;
    }

    void processPage(PageInfo* p)
    {
        uint16_t freesize = 0;
        uint16_t stuckcount = 0;
        bool allrcsimple = true;

        GC_META_DATA_WORD* metacurr = p->slots;
        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            auto w = *metacurr;
            if(!GC_IS_DEC_PENDING(w))
            {
                if(GC_IS_FWD_PTR(w))
                {
                    GC_STORE_META_DATA_WORD(metacurr, 0x0ul);
                    w = 0x0ul;
                }
                
                if(!GC_IS_ALLOCATED(w))
                {
                    freesize++;
                }
                else
                {
                    if(GC_IS_STUCK(w))
                    {
                        stuckcount++;
                    }
                
                    //it is a count RC
                    allrcsimple &= (w & GC_RC_KIND_MASK);

                    GC_RESET_YOUNG_AND_MARK(metacurr, w);
                }
            }

            metacurr++;
        }

        p->free_count = freesize;
        p->stuck_count = stuckcount;

        if(freesize == p->entry_count)
        {
            this->unlinkPageFromType(p);
            this->free_pages.insert(p);
        }
        else if((float)freesize > (PAGE_FULL_FACTOR * (float)p->entry_count))
        {
            p->allocatable_category = AllocationListInfo_Full;
            this->full_pages.insert(p);
        }
        else
        {
            if(stuckcount != 0)
            {
                p->allocatable_category = AllocationListInfo_Stuck;
                p->type->
            }
            else
            {
                if(allrcsimple & ((float)freesize <= (PAGE_EVACUATABLE_FACTOR * p->entry_count)))
                {
                    p->allocatable_category = AllocationListInfo_Evacuatable;
                }
                else
                {
                    p->allocatable_category = AllocationListInfo_General;
                }
            }
        }
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

    uint8_t* globals_mem;
    size_t globals_mem_size;

#ifdef ENABLE_MEM_STATS
    size_t gccount;
    size_t maxheap;
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
                GC_STORE_META_DATA_WORD(addr, (GC_RC_KIND_MASK | GC_RC_TWO) | meta);
            }
        }
    }

    inline void processDecHeapRC(GC_META_DATA_WORD* addr, GC_META_DATA_WORD meta) 
    {
        if(GC_RC_IS_COUNT(meta))
        {
            GC_STORE_META_DATA_WORD(addr, GC_DEC_RC_COUNT(meta));
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
            
            GC_STORE_META_DATA_WORD(addr, GC_MARK_BIT);

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

        pp->freelist = *((void**)pp->freelist);
        pp->freelist_count--;

        return alloc;
    }

    void* evacuateObject(void* obj, BSQType* ometa, void* fromObj)
    {
        void* nobj = this->allocateEvacuate(ometa);
        GC_MEM_COPY(nobj, obj, ometa->allocinfo.heapsize);
        
        GC_META_DATA_WORD* naddr = GC_GET_META_DATA_ADDR(nobj);
        GC_STORE_META_DATA_WORD(naddr, GC_RC_INITIALIZE_PARENT(fromObj));

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
    inline static void gcDecrementString(void* v)
    {
        if (!IS_INLINE_STRING(v))
        {
            Allocator::GlobalAllocator.processDecHeapRC(v);
        }
    }

    inline static void gcDecrementBigNum(void* v)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            Allocator::GlobalAllocator.processDecHeapRC(v);
        }
    }

    inline static void gcDecrementSlotsWithUnion(void** slots)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpDecObj(umeta, *(slots + 1));
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
                    Allocator::GlobalAllocator.processDecHeapRC(*cslot);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::GlobalAllocator.gcDecrementString(*cslot);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::GlobalAllocator.gcDecrementBigNum(*cslot);
                    break;
                default:
                    Allocator::GlobalAllocator.gcDecrementSlotsWithUnion(cslot);
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

    inline void gcEvacuateBigNum(void** slot, void* obj)
    {
        if (!IS_INLINE_BIGNUM(*slot))
        {
            Allocator::GlobalAllocator.processDecHeapEvacuate(obj, slot);
        }
    }

    inline void gcEvacuateWithUnion(void** slots, void* obj)
    {
        const BSQType* umeta = ((const BSQType*)(*slots));
        return umeta->gcops.fpProcessMoveObj(umeta, slots + 1, obj);
    }

    inline void gcEvacuateWithMask(void** slots, void* obj, RefMask mask)
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
                    Allocator::GlobalAllocator.gcEvacuateString(cslot, obj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::GlobalAllocator.gcEvacuateBigNum(cslot, obj);
                    break;
                default:
                    Allocator::GlobalAllocator.gcEvacuateWithUnion(cslot, obj);
                    break;
            }
            cslot++;
        }
    }

    void processFilledPage(const BSQType* btype, PageInfo* pp)
    {
        xxxx;
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
            for(uint8_t* gcurr = this->globals_mem; gcurr < (this->globals_mem + this->globals_mem_size); gcurr += ICPP_WORD_SIZE)
            {
                this->gcCopyRoots(*((uintptr_t*)gcurr));
            }
        }

        GCRefListIterator rootiter; 
        this->rootlist.iterBegin(rootiter);
        while(this->rootlist.iterHasMore(rootiter))
        {
            void* robj = rootiter.get();
            this->gcProcessSlotRoot(robj);

            this->rootlist.iterAdvance(rootiter);
        }
    }

    void processHeap()
    {
        GCRefListIterator rootiter; 
        this->rootlist.iterBegin(rootiter);
        while(this->rootlist.iterHasMore(rootiter))
        {
            void* robj = rootiter.get();
            this->worklist.enque(robj);

            this->rootlist.iterAdvance(rootiter);
        }

        while (!this->worklist.empty())
        {
            void* obj = this->worklist.deque();

            const BSQType* umeta = PAGE_MASK_EXTRACT_ADDR(obj)->type;
            assert(umeta->allocinfo.heapmask != nullptr);

            Allocator::gcProcessSlotsWithMask((void**)obj, obj, umeta->allocinfo.heapmask);
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
        size_t freelimit = (3 * BSQ_COLLECT_THRESHOLD) / 2;
        size_t freecount = 0;

        while (!this->releaselist.empty())
        {
            if(freelimit <= freecount)
            {
                break;
            } 

            void* obj = this->releaselist.deque();
            PageInfo* pp = PAGE_MASK_EXTRACT_ADDR(obj);

            BSQType* umeta = PAGE_MASK_EXTRACT_ADDR(obj)->type;
            freecount += pp->entry_size;
            pp->entry_release_count++;

            if (umeta->allocinfo.heapmask != nullptr)
            {
                umeta->gcops.fpDecObjCollect(umeta, (void**)obj, obj);
            }

            if(pp->entry_release_count + pp->entry_available_count == pp->entry_count)
            {
                this->blockalloc.unlinkPageFromType(umeta, pp);
            }
        }
    }

    inline static bool dropped_out_of_high_util(PageInfo* pp)
    {
        float prevoccupancy = 1.0f - ((float)pp->entry_count - (float)(pp->freelist_count - 1)) / (float)pp->entry_count;
        float occupancy = 1.0f - ((float)pp->entry_count - (float)pp->freelist_count) / (float)pp->entry_count;

        return (prevoccupancy > OCCUPANCY_MID_HIGH_BREAK) & (occupancy <= OCCUPANCY_MID_HIGH_BREAK);
    }

    PageInfo* allocate_slow(BSQType* mdata)
    {
        uint32_t credits = this->page_cost;

        if(this->pendingdecs != nullptr)
        {
            for(size_t i = 0; i < this->dec_ops_count && this->pendingdecs != nullptr; ++i)
            {
                void* decobj = this->pendingdecs;
                PageInfo* pp = PAGE_MASK_EXTRACT_ADDR(decobj);
                GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR_AND_PAGE(decobj, pp);

                this->pendingdecs = GC_GET_DEC_LIST(*addr);
                pp->btype->gcops.fpDecObj(pp->btype, decobj);

                GC_STORE_META_DATA_WORD(addr, 0x0);
                *((void**)decobj) = pp->freelist;
                pp->freelist = decobj;
                pp->freelist_count++;

                if(pp->freelist_count == pp->entry_count)
                {
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

            credits--;
        }

        if(!this->blockalloc.filled_pages.empty())
        {
            while(credits != 0)
            {
                PageInfo* pp = nullptr;
                if(!mdata->filledPages.empty())
                {
                    pp = *(mdata->filledPages.begin());
                }
                else
                {
                    pp = *(this->blockalloc.filled_pages.begin());
                }

                this->processFilledPage(mdata, pp);
                pp->btype->filledPages.erase(pp);
                this->blockalloc.filled_pages.erase(pp);

                credits--;
            }
        }

        return this->blockalloc.processAndGetNewPageForAllocation(mdata);
    }

public:
    Allocator() : blockalloc(), worklist(), pendingdecs(nullptr), oldroots(), roots(), evacobjs(), activeallocprocessing(), page_cost(DEFAULT_PAGE_COST), dec_ops_count(DEFAULT_DEC_OPS_COUNT), globals_mem(nullptr), globals_mem_size(0)
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

        pp->freelist = *((void**)pp->freelist);
        pp->freelist_count--;

        return alloc;
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

    void setGlobalsMemory(void* globals, size_t bytes)
    {
        this->globals_mem = (uint8_t*)globals;
        this->globals_mem_size = bytes;
    }

    void completeGlobalInitialization()
    {
        this->collect();

        Allocator::gcMakeImmortalSlotsWithMask((void**)Allocator::GlobalAllocator.globals_mem, Allocator::GlobalAllocator.globals_mask);

        xfree(Allocator::GlobalAllocator.globals_mem);
        Allocator::GlobalAllocator.globals_mem = nullptr;
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

