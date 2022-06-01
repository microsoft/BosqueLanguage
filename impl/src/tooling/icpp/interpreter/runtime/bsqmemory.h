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

#define PAGE_FULL_FACTOR 0.90f
#define PAGE_EVACUATABLE_FACTOR 0.05f

////
//BSQType abstract base class
class BSQType
{
public:
    static const BSQType** g_typetable;

    PageInfo* allocpage;
    PageInfo* evallocpage;

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

    //TODO: may want to split allocPages into sparseYoung and denseOld -- then try to bifurcate by prefering sparseYoung 
    //      for regular allocation and denseOld for evacuation

    std::set<PageInfo*> stuckAllocPages; //pages with stuck objects or high ref-count objects that we can allocate into -- sorted in memory order
    std::set<PageInfo*> partialAllocPages; //pages without any stuck objects that we can alloc into -- sorted in memory order
    std::set<PageInfo*> evacuatablePages; //pages with less than PAGE_EVACUATABLE_FACTOR occupancy and no stuck objects that we want to evacuate

    //Constructor that everyone delegates to
    BSQType(BSQTypeID tid, BSQTypeLayoutKind tkind, BSQTypeSizeInfo allocinfo, GCFunctorSet gcops, std::map<BSQVirtualInvokeID, BSQInvokeID> vtable, KeyCmpFP fpkeycmp, DisplayFP fpDisplay, std::string name, PageInfo* spage): 
        allocpage(spage), evallocpage(spage), tid(tid), tkind(tkind), allocinfo(allocinfo), gcops(gcops), fpkeycmp(fpkeycmp), vtable(vtable), fpDisplay(fpDisplay), name(name)
    {
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
    std::set<PageInfo*> full_pages; //pages that are full
    std::set<PageInfo*> filled_pages; //pages that have been filled by the allocator and are pending collection
    std::set<PageInfo*> free_pages; //pages that are completely empty

    //TODO: may want to metronome walk the full page set and make pending any pages not processed in the last k epochs

    int32_t gc_epoch = 0;
    std::list<PageInfo*> processing_pages; //pages that are pending processing
    std::list<PageInfo*> next_epoch_processing_pages; //pages that were processed but we want to process again or that were alloc into and have refs -- stick here and we will get them next epoch

    static PageInfo g_sential_page;


#ifdef DEBUG_ALLOC_BLOCKS
    //For malloc based debug implementation we keep explicit map from object to page it is in
    std::map<void*, PageInfo*> page_map;
#endif

    inline bool isAddrAllocated(void* addr, void*& realobj) const
    {
        //TODO: probably want some bitvector and/or semi-hierarchical structure here instead 

        auto pageiter = this->page_set.find(PAGE_MASK_EXTRACT_ADDR(addr));
        if(pageiter == this->page_set.cend() || (*pageiter)->type == nullptr)
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
            p->entry_available_count++;
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
        p->entry_count = btype->tableEntryCount;
        p->entry_size = btype->allocinfo.heapsize;
        p->idxshift = btype->tableEntryIndexShift;

        p->type = btype;

        p->state = PageInfoStateFlag_Clear;
        p->lru_gc_epoch = -1;

        this->page_set.insert(p);
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

        p->type = nullptr;

        p->state = PageInfoStateFlag_Clear;
        p->lru_gc_epoch = -1;
    }

    void processPage(PageInfo* p)
    {
        uint64_t freesize = 0;
        bool hasrefs = false;
        bool hasstuck = false;
        bool allrcsimple = true;

        GC_META_DATA_WORD* metacurr = p->slots;
        for(uint64_t i = 0; i < p->entry_count; ++i)
        {
            auto w = *metacurr;
            if(!GC_IS_ALLOCATED(w))
            {
                freesize++;
            }
            else
            {
                if(GC_IS_FWD_PTR(w))
                {
                    GC_STORE_META_DATA_WORD(metacurr, 0x0ul);
                    freesize++;
                }
                else if(GC_IS_DEC_PENDING(w))
                {
                    ;
                }
                else
                {
                    if(GC_TEST_MARK_BIT(w))
                    {
                        w = GC_INC_STUCK_COUNT(w);
                        hasrefs = true;
                        hasstuck |= (GC_IS_STUCK(w));
                    }
                
                    //it is a count RC
                    allrcsimple &= (w & GC_RC_KIND_MASK);

                    GC_RESET_YOUNG_AND_MARK(metacurr, w);
                }
            }

            metacurr++;
        }

        p->lru_gc_epoch = this->gc_epoch;

        auto oldpagestate = (p->state & ~PageInfoStateFlag_ProcessingPending);
        if(freesize == p->entry_count)
        {
            this->unlinkPageFromType(p);
        }
        else if((float)freesize > (PAGE_FULL_FACTOR * (float)p->entry_count))
        {
            p->state = PageInfoStateFlag_FullPage;
        }
        else
        {
            if(hasstuck)
            {
                p->state = PageInfoStateFlag_StuckAvailable;
            }
            else
            {
                if(allrcsimple & ((float)freesize <= (PAGE_EVACUATABLE_FACTOR * p->entry_count)))
                {
                    p->state = PageInfoStateFlag_Evacuatable;
                }
                else
                {
                    p->state = PageInfoStateFlag_GeneralAvailable;
                }
            }
        }

        if(oldpagestate != p->state)
        {
            assert(oldpagestate != PageInfoStateFlag_Clear);

            if(oldpagestate == PageInfoStateFlag_AllocPage)
            {
                p->type->allocpage = &BlockAllocator::g_sential_page;
            }
            else if(oldpagestate == PageInfoStateFlag_AllocFilledPage)
            {
                this->filled_pages.erase(p);
            }
            else if(oldpagestate == PageInfoStateFlag_FullPage)
            {
                this->full_pages.erase(p);
            }
            else if(oldpagestate == PageInfoStateFlag_StuckAvailable)
            {
                p->type->stuckAllocPages.erase(p);
            }
            else if(oldpagestate == PageInfoStateFlag_GeneralAvailable)
            {
                p->type->partialAllocPages.erase(p);
            }
            else if(oldpagestate == PageInfoStateFlag_Evacuatable)
            {
                p->type->evacuatablePages.erase(p);
            }
            else
            {
                assert(false); //lost page?
            }

            if(p->state == PageInfoStateFlag_Clear)
            {
                this->free_pages.insert(p);
            }
            else if(p->state == PageInfoStateFlag_FullPage)
            {
                this->full_pages.insert(p);
            }
            else if(p->state == PageInfoStateFlag_StuckAvailable)
            {
                p->type->stuckAllocPages.insert(p);
            }
            else if(p->state == PageInfoStateFlag_GeneralAvailable)
            {
                p->type->partialAllocPages.insert(p);
            }
            else if(p->state == PageInfoStateFlag_Evacuatable)
            {
                p->type->evacuatablePages.insert(p);
            }
            else
            {
                assert(false); //lost page?
            }
        }

        if(hasrefs && (oldpagestate == PageInfoStateFlag_AllocPage || oldpagestate == PageInfoStateFlag_AllocFilledPage))
        {
            //put into next epoch queue cause some of these will certainly die
            p->state = p->state | PageInfoStateFlag_ProcessingPending;
            this->next_epoch_processing_pages.push_back(p);
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

        return pp;
    }

    void releasePage(PageInfo* pp)
    {
        assert(pp->state == PageInfoStateFlag_Clear);

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

    void getAllocPageForType(BSQType* btype)
    {
        if(btype->allocpage == &BlockAllocator::g_sential_page)
        {
            btype->allocpage = this->allocateFreePage(btype);
            this->initializeFreshPageForType(btype->allocpage, btype);

            this->initializePageFreelist(btype->allocpage);
            btype->allocpage->state = PageInfoStateFlag_AllocPage;
            return;
        }
        else
        {
            auto stuckopt = btype->stuckAllocPages.begin();
            if(stuckopt != btype->stuckAllocPages.end())
            {
                btype->allocpage = *stuckopt;
                btype->stuckAllocPages.erase(stuckopt);

                this->initializePageFreelist(btype->allocpage);
                btype->allocpage->state = PageInfoStateFlag_AllocPage | (btype->allocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            auto partialopt = btype->partialAllocPages.begin(); 
            if(partialopt != btype->partialAllocPages.end())
            {
                btype->allocpage = *partialopt;
                btype->partialAllocPages.erase(partialopt);

                this->initializePageFreelist(btype->allocpage);
                btype->allocpage->state = PageInfoStateFlag_AllocPage | (btype->allocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            auto evacopt = btype->evacuatablePages.begin(); 
            if(evacopt != btype->evacuatablePages.end())
            {
                btype->allocpage = *evacopt;
                btype->evacuatablePages.erase(partialopt);

                this->initializePageFreelist(btype->allocpage);
                btype->allocpage->state = PageInfoStateFlag_AllocPage | (btype->allocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            btype->allocpage = this->allocateFreePage(btype);
            this->initializeFreshPageForType(btype->allocpage, btype);

            this->initializePageFreelist(btype->allocpage);
            btype->allocpage->state = PageInfoStateFlag_AllocPage;
            return;
        }
    }

    void getYoungEvacuateAllocPageForType(BSQType* btype)
    {
        if(btype->evallocpage == &BlockAllocator::g_sential_page)
        {
            btype->evallocpage = this->allocateFreePage(btype);
            this->initializeFreshPageForType(btype->evallocpage, btype);

            this->initializePageFreelist(btype->evallocpage);
            btype->evallocpage->state = PageInfoStateFlag_AllocPage;
            return;
        }
        else
        {
            auto stuckopt = btype->stuckAllocPages.begin();
            if(stuckopt != btype->stuckAllocPages.end())
            {
                btype->evallocpage = *stuckopt;
                btype->stuckAllocPages.erase(stuckopt);

                this->initializePageFreelist(btype->evallocpage);
                btype->evallocpage->state = PageInfoStateFlag_AllocPage | (btype->evallocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            auto partialopt = btype->partialAllocPages.begin(); 
            if(partialopt != btype->partialAllocPages.end())
            {
                btype->evallocpage = *partialopt;
                btype->partialAllocPages.erase(partialopt);

                this->initializePageFreelist(btype->evallocpage);
                btype->evallocpage->state = PageInfoStateFlag_AllocPage | (btype->evallocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            auto evacopt = btype->evacuatablePages.begin(); 
            if(evacopt != btype->evacuatablePages.end())
            {
                btype->evallocpage = *evacopt;
                btype->evacuatablePages.erase(partialopt);

                this->initializePageFreelist(btype->evallocpage);
                btype->evallocpage->state = PageInfoStateFlag_AllocPage | (btype->evallocpage->state & PageInfoStateFlag_ProcessingPending);
                return;
            }

            btype->evallocpage = this->allocateFreePage(btype);
            this->initializeFreshPageForType(btype->evallocpage, btype);

            this->initializePageFreelist(btype->evallocpage);
            btype->evallocpage->state = PageInfoStateFlag_AllocPage;
            return;
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

    bool gc_in_stw;
    bool gc_in_young_walk_evacuate;

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
            auto fromPageId = PAGE_MASK_EXTRACT_ID(fromObj);
            if(GC_RC_IS_PARENT1_CLEAR(meta))
            {
                GC_STORE_META_DATA_WORD(addr, ((fromPageId << GC_RC_PAGE1_SHIFT) | meta));
            }
            else if(GC_RC_IS_PARENT2_CLEAR(meta))
            {
                GC_STORE_META_DATA_WORD(addr, ((fromPageId << GC_RC_PAGE2_SHIFT) | meta));
            }
            else
            {
                GC_STORE_META_DATA_WORD(addr, (GC_RC_KIND_MASK | GC_RC_THREE) | (( GC_MARK_BIT | GC_STUCK_BITS | GC_YOUNG_BIT | GC_ALLOCATED_BIT) & meta));
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
            auto fromPageId = PAGE_MASK_EXTRACT_ID(fromObj);
            if(GC_RC_GET_PARENT1(meta) == fromPageId)
            {
                //delete parent 1
                GC_STORE_META_DATA_WORD(addr, (GC_RC_PAGE1_MASK | GC_MARK_BIT | GC_STUCK_BITS | GC_YOUNG_BIT | GC_ALLOCATED_BIT) & meta);
            }
            else
            {
                //That is really bad
                assert(GC_RC_GET_PARENT2(meta) == fromPageId);

                //delete parent 2
                GC_STORE_META_DATA_WORD(addr, (GC_RC_PAGE2_MASK | GC_MARK_BIT | GC_STUCK_BITS | GC_YOUNG_BIT | GC_ALLOCATED_BIT) & meta);
            }
        }
    }

    void processDecHeapRC_Slow(void* obj)
    {
        PageInfo* pp = PAGE_MASK_EXTRACT_ADDR(obj);
        
        if((pp->state & PageInfoStateFlag_ProcessingPending) != PageInfoStateFlag_Clear)
        {
            pp->state = pp->state | PageInfoStateFlag_ProcessingPending;

            if(pp->lru_gc_epoch < this->blockalloc.gc_epoch)
            {
                this->blockalloc.processing_pages.push_back(pp);
            }
            else
            {
                this->blockalloc.next_epoch_processing_pages.push_back(pp);
            }
        }
    }

    inline void processDecHeapRC(void* obj, void* fromObj)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(obj);
        Allocator::processDecHeapRC(addr, GC_LOAD_META_DATA_WORD(addr), fromObj);

        if(GC_TEST_IS_UNREACHABLE(GC_LOAD_META_DATA_WORD(addr)))
        {
            this->processDecHeapRC_Slow(obj);
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

        void* obj = reinterpret_cast<void*>(v);
        void* resolvedobj = nullptr;
        if(this->blockalloc.isAddrAllocated(obj, resolvedobj))
        {
            GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(resolvedobj);
            GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);
            
            GC_STORE_META_DATA_WORD(addr, GC_SET_MARK_BIT(w));

            this->worklist.enque(resolvedobj);
        }
    }

    inline uint8_t* allocateYoungEvacuate(BSQType* mdata)
    {
        PageInfo* pp = mdata->evallocpage;
        if(pp->freelist == nullptr)
        {
            this->blockalloc.getYoungEvacuateAllocPageForType(mdata);
        }
        
        uint8_t* alloc = (uint8_t*)pp->freelist;
        pp->freelist = *((void**)pp->freelist);

        return alloc;
    }

    void* evacuateYoungObject(void* obj, GC_META_DATA_WORD* addr, BSQType* ometa, void* fromObj)
    {
        void* nobj = this->allocateYoungEvacuate(ometa);
        GC_MEM_COPY(nobj, obj, ometa->allocinfo.heapsize);
        
        GC_META_DATA_WORD* naddr = GC_GET_META_DATA_ADDR(nobj);
        Allocator::GlobalAllocator.processIncHeapRC(naddr, GC_ALLOCATED_BIT, fromObj);

        GC_STORE_META_DATA_WORD(addr, GC_IS_FWD_PTR_BIT | (uintptr_t)nobj);

        return nobj;
    }

    inline void gcProcessSlotHeap(void** slot, void* fromObj)
    {
        GC_META_DATA_WORD* addr = GC_GET_META_DATA_ADDR(slot);
        GC_META_DATA_WORD w = GC_LOAD_META_DATA_WORD(addr);
        
        if(GC_IS_FWD_PTR(w))
        {
            *slot = (void*)(w & ~GC_IS_FWD_PTR_BIT);
            addr = GC_GET_META_DATA_ADDR(slot);
            w = GC_LOAD_META_DATA_WORD(addr);

            Allocator::GlobalAllocator.processIncHeapRC(addr, w, fromObj);
        }
        else
        {
            if(GC_TEST_MARK_BIT(w))
            {
                Allocator::GlobalAllocator.processIncHeapRC(addr, w, fromObj);
            }
            else
            {
                auto ometa = PAGE_MASK_EXTRACT_ADDR(*slot)->type;
                *slot = this->evacuateYoungObject(*slot, addr, ometa, fromObj);

                if (!ometa->isLeaf())
                {
                    this->worklist.enque(*slot);
                }
            }
        }
    }

    inline static void gcProcessSlotWithString(void* slot, void* fromObj)
    {
        if (!IS_INLINE_STRING(slot))
        {
            Allocator::gcProcessSlotHeap(slot, fromObj);
        }
    }

    inline static void gcProcessSlotWithBigNum(void* slot, void* fromObj)
    {
        if (!IS_INLINE_BIGNUM(slot))
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
                    Allocator::gcProcessSlotHeap(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_STRING:
                    Allocator::gcProcessSlotWithString(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    Allocator::gcProcessSlotWithBigNum(*cslot, fromObj);
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
    inline void gcDecrementString_Collection(void* v, void* fromObj)
    {
        if (!IS_INLINE_STRING(v))
        {
            this->processDecHeapRC_DuringCollection(v, fromObj);
        }
    }

    inline void gcDecrementBigNum_Collection(void* v, void* fromObj)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            this->processDecHeapRC_DuringCollection(v, fromObj);
        }
    }

    inline void gcDecrementSlotsWithUnion_Collection(void** slots, void* fromObj)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return umeta->gcops.fpDecObjCollect(umeta, slots + 1, fromObj);
        }
    }

    inline void gcDecSlotsWithMask_Collection(void** slots, void* fromObj, RefMask mask)
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
                    this->processDecHeapRC_DuringCollection(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_STRING:
                    this->gcDecrementString_Collection(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    this->gcDecrementBigNum_Collection(*cslot, fromObj);
                    break;
                default:
                    this->gcDecrementSlotsWithUnion_Collection(cslot, fromObj);
                    break;
            }
            cslot++;
        }
    }

    inline void gcDecrementString_Compaction(void* v, void* fromObj)
    {
        if (!IS_INLINE_STRING(v))
        {
            this->processDecHeapRC_DuringCompaction(v, fromObj);
        }
    }

    inline void gcDecrementBigNum_Compaction(void* v, void* fromObj)
    {
        if (!IS_INLINE_BIGNUM(v))
        {
            this->processDecHeapRC_DuringCompaction(v, fromObj);
        }
    }

    inline void gcDecrementSlotsWithUnion_Compaction(void** slots, void* fromObj)
    {
        if(*slots != nullptr)
        {
            const BSQType* umeta = ((const BSQType*)(*slots));
            return umeta->gcops.fpDecObjCompact(umeta, slots + 1, fromObj);
        }
    }

    inline void gcDecSlotsWithMask_Compaction(void** slots, void* fromObj, RefMask mask)
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
                    this->processDecHeapRC_DuringCompaction(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_STRING:
                    this->gcDecrementString_Compaction(*cslot, fromObj);
                    break;
                case PTR_FIELD_MASK_BIGNUM:
                    this->gcDecrementBigNum_Compaction(*cslot, fromObj);
                    break;
                default:
                    this->gcDecrementSlotsWithUnion_Compaction(cslot, fromObj);
                    break;
            }
            cslot++;
        }
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

    inline uint8_t* allocate(BSQType* mdata)
    {
        PageInfo* pp = mdata->allocpages;
        if(pp->freelist == nullptr)
        {
            pp = this->blockalloc.managePagesForType(mdata);
        }
        
        uint8_t* alloc = (uint8_t*)pp->freelist;

        pp->freelist = *((void**)pp->freelist);
        pp->entry_available_count--;

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

