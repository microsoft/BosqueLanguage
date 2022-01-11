//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqvalue.h"

#include <bitset>

#define LIST_LOAD_TYPE_INFO(SL) SLPTR_LOAD_UNION_INLINE_TYPE(SL)
#define LIST_LOAD_TYPE_INFO_REPR(SL) SLPTR_LOAD_UNION_INLINE_TYPE_AS(BSQListReprType, SL)
#define LIST_LOAD_DATA(SL) SLPTR_LOAD_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL))

#define LIST_STORE_RESULT_REPR(R, SL) SLPTR_STORE_UNION_INLINE_TYPE(SLPTR_LOAD_HEAP_TYPE(R), SL); SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL), R)
#define LIST_STORE_RESULT_EMPTY(SL) SLPTR_STORE_UNION_INLINE_TYPE(BSQWellKnownType::g_typeNone, SL); SLPTR_STORE_CONTENTS_AS_GENERIC_HEAPOBJ(SLPTR_LOAD_UNION_INLINE_DATAPTR(SL), BSQNoneValue)

enum class ListReprKind
{
    PV4,
    PV8,
    TreeElement
};

class BSQListReprType : public BSQRefType
{
public:
    const BSQTypeID entrytype;
    const ListReprKind lkind;

    BSQListReprType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, BSQTypeID entrytype, ListReprKind lkind)
    : BSQRefType(tid, allocsize, heapmask, {}, EMPTY_KEY_CMP, entityListReprDisplay_impl, name), entrytype(entrytype), lkind(lkind)
    {;}

    virtual ~BSQListReprType() {;}

    virtual uint64_t getCount(void* repr) const = 0;
};

class BSQPartialVectorType : public BSQListReprType
{
public:
    const size_t entrysize;

    BSQPartialVectorType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, BSQTypeID entrytype, ListReprKind lkind, size_t entrysize) 
    : BSQListReprType(tid, allocsize, heapmask, name, entrytype, lkind), entrysize(entrysize)
    {;}

    virtual ~BSQPartialVectorType() {;}

    virtual uint64_t getCount(void* repr) const override final
    {
        return *((uint64_t*)repr);
    }

    inline static int16_t getPVCount(void* repr) 
    {
        return (int16_t)*((uint64_t*)repr);
    }

    inline static void setPVCount(void* repr, int16_t count)
    {
        *((uint64_t*)repr) = (uint64_t)count;
    }

    inline StorageLocationPtr get(void* repr, int16_t i) const
    {
        return ((uint8_t*)repr) + sizeof(uint64_t) + (i * this->entrysize);
    }

    inline void copyPVData(void* pvinto, void* pvfrom) const
    {
        auto intoloc = ((uint8_t*)pvinto) + (sizeof(uint64_t) + (*((uint64_t*)pvinto) * this->entrysize));
        auto fromloc = ((uint8_t*)pvfrom) + sizeof(uint64_t);
        auto bytecount = (*((uint64_t*)pvfrom) * this->entrysize);

        GC_MEM_COPY(intoloc, fromloc, bytecount);
        *((uint64_t*)pvinto) += *((uint64_t*)pvfrom);
    }

    template <size_t K>
    inline void packPVData(void* pvinto, void* pvfrom, std::bitset<K> mask) const
    {
        auto intoloc = ((uint8_t*)pvinto) + sizeof(uint64_t);
        auto fromloc = ((uint8_t*)pvfrom) + sizeof(uint64_t);
        
        uint64_t jj = 0;
        for(size_t i = 0; i < K; ++i)
        {
            if(mask[i])
            {
                auto dst = intoloc + (this->entrysize * jj);
                auto src = fromloc + (this->entrysize * i);

                GC_MEM_COPY(dst, src, this->entrysize);
                jj++;
            }
        }

        *((uint64_t*)pvinto) += jj;
    }
};

struct BSQListTreeRepr
{
    void* l;
    void* r;
    uint64_t size;
};

class BSQListTreeType : public BSQListReprType
{
public:
    BSQListTreeType(BSQTypeID tid, std::string name, BSQTypeID entrytype)
    : BSQListReprType(tid, sizeof(BSQListTreeRepr), "22", name, entrytype, ListReprKind::TreeElement) 
    {;}

    virtual ~BSQListTreeType() {;}

    virtual uint64_t getCount(void* repr) const override final
    {
        return ((BSQListTreeRepr*)repr)->size;
    }
};

struct BSQListTypeFlavor
{
    BSQTypeID ltype;
    const BSQPartialVectorType* pv4type;
    const BSQPartialVectorType* pv8type;
    const BSQListTreeType* treetype;
};

class BSQListForwardIterator : public BSQCollectionIterator
{
public:
    int64_t curr;
    int64_t lmax;
    const BSQPartialVectorType* lctype;
    int16_t icurr;
    int16_t imax;

    BSQListForwardIterator(const BSQType* lreprtype, void* lroot): BSQCollectionIterator(), lctype(nullptr), icurr(0), imax(0)
    {
        if(lroot != nullptr) 
        {
            this->lmax = (int64_t)dynamic_cast<const BSQListReprType*>(lreprtype)->getCount(lroot); 

            void* rr = lroot;
            const BSQListReprType* rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
            while(rt->lkind == ListReprKind::TreeElement)
            {
                this->iterstack.push_back(static_cast<BSQListTreeRepr*>(rr));

                rr = static_cast<BSQListTreeRepr*>(rr)->l;
                rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
            }

            this->lcurr = static_cast<void*>(rr);
            this->lctype = static_cast<const BSQPartialVectorType*>(rt);

            this->icurr = 0;
            this->imax = BSQPartialVectorType::getPVCount(rr);
        }
    }
    
    virtual ~BSQListForwardIterator() {;}

    inline bool valid() const
    {
        return this->curr != this->lmax;
    }

    void advance_slow()
    {
        void* rr = this->lcurr;
        while(static_cast<BSQListTreeRepr*>(this->iterstack.back())->r == rr)
        {
            rr = this->iterstack.back();
            this->iterstack.pop_back();
        }

        rr = static_cast<BSQListTreeRepr*>(rr)->r;
        const BSQListReprType* rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
        while(rt->lkind == ListReprKind::TreeElement)
        {
            this->iterstack.push_back(static_cast<BSQListTreeRepr*>(rr));

            rr = static_cast<BSQListTreeRepr*>(rr)->l;
            rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
        }

        this->lcurr = static_cast<void*>(rr);
        this->lctype = static_cast<const BSQPartialVectorType*>(rt);

        this->icurr = 0;
        this->imax = BSQPartialVectorType::getPVCount(rr);
    }

    inline void advance()
    {
        assert(this->valid());

        this->curr++;
        this->icurr++;
        if(this->icurr >= this->imax)
        {
            this->advance_slow();
        }
    }

    inline StorageLocationPtr getlocation() const
    {
        assert(this->valid());

        return this->lctype->get(this->lcurr, this->icurr);
    }
};

class BSQListReverseIterator : public BSQCollectionIterator
{
public:
    int64_t curr;
    const BSQPartialVectorType* lctype;
    int16_t icurr;

    BSQListReverseIterator(const BSQType* lreprtype, void* lroot): BSQCollectionIterator(), lctype(nullptr), icurr(0)
    {
        if(lroot != nullptr) 
        {
            this->curr = (int64_t)dynamic_cast<const BSQListReprType*>(lreprtype)->getCount(lroot) - 1; 

            void* rr = lroot;
            const BSQListReprType* rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
            while(rt->lkind == ListReprKind::TreeElement)
            {
                this->iterstack.push_back(static_cast<BSQListTreeRepr*>(rr));

                rr = static_cast<BSQListTreeRepr*>(rr)->r;
                rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
            }

            this->lcurr = static_cast<void*>(rr);
            this->lctype = static_cast<const BSQPartialVectorType*>(rt);

            this->icurr = BSQPartialVectorType::getPVCount(rr) - 1;
        }
    }
    
    virtual ~BSQListReverseIterator() {;}

    inline bool valid() const
    {
        return this->curr >= 0;
    }

    void advance_slow()
    {
        void* rr = this->lcurr;
        while(static_cast<BSQListTreeRepr*>(this->iterstack.back())->l == rr)
        {
            rr = this->iterstack.back();
            this->iterstack.pop_back();
        }

        rr = static_cast<BSQListTreeRepr*>(rr)->r;
        const BSQListReprType* rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
        while(rt->lkind == ListReprKind::TreeElement)
        {
            this->iterstack.push_back(static_cast<BSQListTreeRepr*>(rr));

            rr = static_cast<BSQListTreeRepr*>(rr)->r;
            rt = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rr));
        }

        this->lcurr = static_cast<void*>(rr);
        this->lctype = static_cast<const BSQPartialVectorType*>(rt);

        this->icurr = BSQPartialVectorType::getPVCount(rr) - 1;
    }

    inline void advance()
    {
        assert(this->valid());

        this->curr--;
        this->icurr--;
        if(this->icurr < 0)
        {
            this->advance_slow();
        }
    }

    inline StorageLocationPtr getlocation() const
    {
        assert(this->valid());

        return this->lctype->get(this->lcurr, this->icurr);
    }
};

class BSQListOps
{
public:
    static std::map<BSQTypeID, BSQListTypeFlavor> g_flavormap; //map from entry type to the flavors of the repr

    static void* list_append(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* lnode, BSQCollectionGCReprNode* rnode)
    {
        if(lnode == nullptr & rnode == nullptr)
        {
            return nullptr;
        }
        else if(lnode == nullptr)
        {
            return rnode->repr;
        }
        else if(rnode == nullptr)
        {
            return lnode->repr;
        }
        else
        {
            auto ltype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(lnode->repr));
            auto rtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rnode->repr));

            Allocator::GlobalAllocator.ensureSpace(sizeof(GC_META_DATA_WORD) + std::max(lflavor.pv8type->allocinfo.heapsize, sizeof(BSQListTreeRepr)));

            auto lrepr = lnode->repr;
            auto rrepr = rnode->repr;
            if((ltype->lkind != ListReprKind::TreeElement) & (rtype->lkind != ListReprKind::TreeElement))
            {
                auto count = BSQPartialVectorType::getPVCount(lrepr) + BSQPartialVectorType::getPVCount(rrepr);

                void* res = nullptr;
                if(count <= 4)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv4type);
                    lflavor.pv4type->copyPVData(res, lrepr);
                    lflavor.pv4type->copyPVData(res, rrepr);
                } 
                else if(count <= 8)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv8type);
                    lflavor.pv8type->copyPVData(res, lrepr);
                    lflavor.pv8type->copyPVData(res, rrepr);
                }
                else
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                    ((BSQListTreeRepr*)res)->l = lrepr;
                    ((BSQListTreeRepr*)res)->r = rrepr;
                    ((BSQListTreeRepr*)res)->size = count;
                }

                return res;
            }
            else
            {
                BSQListTreeRepr* res = (BSQListTreeRepr*)Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                res->l = lrepr;
                res->r = rrepr;
                res->size = ltype->getCount(lrepr) + rtype->getCount(rrepr);

                return res;
            }
        }
    }

    template <typename OP_PV>
    static void* list_tree_transform(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(lflavor, reprnode, reprtype);
        }
        else
        {
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto llnode = list_tree_transform(lflavor, lnode, fn_partialvector);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
            auto rrnode = list_tree_transform(lflavor, rnode, fn_partialvector);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            return BSQListOps::list_append(lflavor, llres, rrres);
        }
    }

    template <typename OP_PV>
    static void* list_tree_transform_idx(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode, uint64_t idx, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(lflavor, reprnode, reprtype, idx);
        }
        else
        {
            auto ltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto lsize = ltype->getCount(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);

            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto llnode = list_tree_transform_idx(lflavor, lnode, idx, fn_partialvector);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
            auto rrnode = list_tree_transform_idx(lflavor, rnode, idx + lsize, fn_partialvector);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            return BSQListOps::list_append(lflavor, llres, rrres);
        }
    }

    static BSQNat s_size_ne(StorageLocationPtr sl)
    {
        return LIST_LOAD_TYPE_INFO_REPR(sl)->getCount(LIST_LOAD_DATA(sl));
    }

    template <typename T>
    static void* s_range_ne_rec(const BSQListTypeFlavor& lflavor, T start, T end, T count)
    {
        void* res = nullptr;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                SLPTR_STORE_CONTENTS_AS(T, lflavor.pv4type->get(res, i), start + (T)i);
            }
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                SLPTR_STORE_CONTENTS_AS(T, lflavor.pv4type->get(res, i), start + (T)i);
            }
        }
        else
        {
            auto mid = start + (count / (T)2);
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto llnode = s_range_ne_rec(lflavor, start, mid, mid - start);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rrnode = s_range_ne_rec(lflavor, mid, end, end - mid);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            return BSQListOps::list_append(lflavor, llres, rrres);
        }
        return res;
    }

    static void s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res)
    {
        auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
        if(oftype->tid == BSQ_TYPE_ID_INT)
        {
            auto ll = BSQListOps::s_range_ne_rec<BSQInt>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_INT)->second, SLPTR_LOAD_CONTENTS_AS(BSQInt, start), SLPTR_LOAD_CONTENTS_AS(BSQInt, end), SLPTR_LOAD_CONTENTS_AS(BSQInt, count));
            LIST_STORE_RESULT_REPR(res, ll);
        }
        else
        {
            assert(oftype->tid == BSQ_TYPE_ID_NAT);

            auto ll = BSQListOps::s_range_ne_rec<BSQNat>(BSQListOps::g_flavormap.find(BSQ_TYPE_ID_NAT)->second, SLPTR_LOAD_CONTENTS_AS(BSQNat, start), SLPTR_LOAD_CONTENTS_AS(BSQNat, end), SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
            LIST_STORE_RESULT_REPR(res, ll);
        }
        Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    }

    static void* s_fill_ne_rec(const BSQListTypeFlavor& lflavor, const BSQType* oftype, StorageLocationPtr val, BSQNat count)
    {
        void* res = nullptr;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                oftype->storeValue(lflavor.pv4type->get(res, i), val);
            }
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                oftype->storeValue(lflavor.pv4type->get(res, i), val);
            }
        }
        else
        {
            auto mid = count / 2;
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto llnode = s_fill_ne_rec(lflavor, oftype, val, mid);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rrnode = s_fill_ne_rec(lflavor, oftype, val, count - mid);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            return BSQListOps::list_append(lflavor, llres, rrres);
        }
        return res;
    }

    static void s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res)
    {
        auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();

        auto ll = BSQListOps::s_fill_ne_rec(BSQListOps::g_flavormap.find(oftype->tid)->second, oftype, val, SLPTR_LOAD_CONTENTS_AS(BSQNat, count));
        LIST_STORE_RESULT_REPR(res, ll);
    
        Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    }

    static void s_zip_index_ne(const BSQType* oftype, const BSQType* oftupletype, StorageLocationPtr ll, StorageLocationPtr res)
    {
        auto gcpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
        auto lnode = Allocator::GlobalAllocator.registerCollectionNode(LIST_LOAD_DATA(ll));

        auto offlavor = BSQListOps::g_flavormap.find(oftype->tid)->second;
        auto tupleinfo = dynamic_cast<const BSQTupleInfo*>(oftupletype);

        auto zlres = BSQListOps::list_tree_transform_idx(BSQListOps::g_flavormap.find(oftupletype->tid)->second, lnode, 0, [&](const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode, const BSQListReprType* reprtype, BSQNat idx) {
            auto pvcount = BSQPartialVectorType::getPVCount(reprnode->repr);
            void* pvres = nullptr;
            if(reprtype->lkind == ListReprKind::PV4)
            {
                pvres = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
                BSQPartialVectorType::setPVCount(pvres, pvcount);
                for(int16_t i = 0; i < pvcount; ++i)
                {
                    auto val = lflavor.pv4type->get(pvres, i);
                    SLPTR_STORE_CONTENTS_AS(BSQNat, oftupletype->indexStorageLocationOffset(val, tupleinfo->idxoffsets[0]), idx);
                    BSQType::g_typetable[tupleinfo->ttypes[1]]->storeValue(oftupletype->indexStorageLocationOffset(val, tupleinfo->idxoffsets[1]), offlavor.pv4type->get(reprnode->repr, i));
                }
            }
            else
            {
                pvres = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
                BSQPartialVectorType::setPVCount(pvres, pvcount);
                for(int16_t i = 0; i < pvcount; ++i)
                {
                    auto val = lflavor.pv8type->get(pvres, i);
                    SLPTR_STORE_CONTENTS_AS(BSQNat, oftupletype->indexStorageLocationOffset(val, tupleinfo->idxoffsets[0]), idx);
                    BSQType::g_typetable[tupleinfo->ttypes[1]]->storeValue(oftupletype->indexStorageLocationOffset(val, tupleinfo->idxoffsets[1]), offlavor.pv8type->get(reprnode->repr, i));
                }
            }
        });
    
        LIST_STORE_RESULT_REPR(zlres, res);
        Allocator::GlobalAllocator.resetCollectionNodeEnd(gcpoint);
    }
};


/////////////////////////////////////////

//List
class BSQListType : public BSQType
{
public:
    const BSQTypeID etype; //type of entries in the list

    BSQListType(BSQTypeID tid, DisplayFP fpDisplay, std::string name, BSQTypeID etype): 
        BSQType(tid, BSQTypeLayoutKind::Struct, {16, 16, 16, nullptr, "12"}, STRUCT_STD_GC_FUNCTOR_SET, {}, EMPTY_KEY_CMP, fpDisplay, name),
        etype(etype)
    {;}

    virtual ~BSQListType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, 16);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        BSQ_MEM_COPY(trgt, src, 16);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }
};

//MAP
class BSQMapType : public BSQType
{
public:
    const BSQTypeID ktype; //type of K in the map
    const BSQTypeID vtype; //type of V in the map
    const BSQTypeID etype; //type of [K, V]

    BSQMapType(BSQTypeID tid, DisplayFP fpDisplay, std::string name, BSQTypeID ktype, BSQTypeID vtype, BSQTypeID etype): 
        BSQType(tid, BSQTypeLayoutKind::Struct, {16, 16, 16, nullptr, "12"}, STRUCT_STD_GC_FUNCTOR_SET, {}, EMPTY_KEY_CMP, fpDisplay, name),
        ktype(ktype), vtype(vtype), etype(etype)
    {;}

    virtual ~BSQMapType() {;}

    void clearValue(StorageLocationPtr trgt) const override final
    {
        GC_MEM_ZERO(trgt, 16);
    }

    void storeValue(StorageLocationPtr trgt, StorageLocationPtr src) const override final
    {
        BSQ_MEM_COPY(trgt, src, 16);
    }

    StorageLocationPtr indexStorageLocationOffset(StorageLocationPtr src, size_t offset) const override final
    {
        assert(false);
        return nullptr;
    }
};