//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqvalue.h"

enum class ListReprKind
{
    PV4,
    PV8,
    TreeElement
};

class BSQListReprType : public BSQRefType
{
public:
    const ListReprKind lkind;

    BSQListReprType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, ListReprKind lkind)
    : BSQRefType(tid, allocsize, heapmask, {}, EMPTY_KEY_CMP, entityListReprDisplay_impl, name), lkind(lkind)
    {;}

    virtual ~BSQListReprType() {;}

    virtual uint64_t getCount(void* repr) const = 0;
};

class BSQPartialVectorType : public BSQListReprType
{
public:
    const size_t entrysize;

    BSQPartialVectorType(BSQTypeID tid, uint64_t allocsize, RefMask heapmask, std::string name, ListReprKind lkind, size_t entrysize) 
    : BSQListReprType(tid, allocsize, heapmask, name, lkind), entrysize(entrysize)
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

    inline StorageLocationPtr get(void* repr, int16_t i) const
    {
        return ((uint8_t*)repr) + sizeof(uint64_t) + (i * this->entrysize);
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
    BSQListTreeType(BSQTypeID tid, std::string name)
    : BSQListReprType(tid, sizeof(BSQListTreeRepr), "22", name, ListReprKind::TreeElement) 
    {;}

    virtual ~BSQListTreeType() {;}

    virtual uint64_t getCount(void* repr) const override final
    {
        return ((BSQListTreeRepr*)repr)->size;
    }
};

struct BSQList
{
    const BSQType* lreprtype;
    void* repr;
};

class BSQListForwardIterator : public BSQCollectionIterator
{
public:
    int64_t curr;
    int64_t lmax;
    const BSQPartialVectorType* lctype;
    int16_t icurr;
    int16_t imax;

    BSQListForwardIterator(BSQList& lroot): BSQCollectionIterator(), lctype(nullptr), icurr(0), imax(0)
    {
        if(lroot.repr != nullptr) 
        {
            this->lmax = (int64_t)dynamic_cast<const BSQListReprType*>(lroot.lreprtype)->getCount(lroot.repr); 

            void* rr = lroot.repr;
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

    BSQListReverseIterator(BSQList& lroot): BSQCollectionIterator(), lctype(nullptr), icurr(0)
    {
        if(lroot.repr != nullptr) 
        {
            this->curr = (int64_t)dynamic_cast<const BSQListReprType*>(lroot.lreprtype)->getCount(lroot.repr) - 1; 

            void* rr = lroot.repr;
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
private:
    BSQCollectionGCReprNode* list_tree_transform(BSQCollectionGCReprNode* reprnode)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(reprnode);
        }
        else
        {
            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto llnode = fn_listtree(lnode);
            Allocator::GlobalAllocator.getCollectionNodeReset();
            if(llnode != nullptr)
            {
                Allocator::GlobalAllocator.getCollectionNodeAdd(llnode);
            }

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
            auto rrnode = fn_listtree(rnode);
            Allocator::GlobalAllocator.getCollectionNodeReset();
            if(rrnode != nullptr)
            {
                Allocator::GlobalAllocator.getCollectionNodeAdd(rrnode);
            }

            if(llnode == nullptr & rrnode == nullptr)
            {
                return nullptr;
            }
            else if(llnode == nullptr)
            {
                return rrnode;
            }
            else if(rrnode == nullptr)
            {
                return llnode;
            }
            else
            {
                auto lltype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(llnode->repr));
                auto rrtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rrnode->repr));

                if((lltype->lkind != ListReprKind::TreeElement) & (rrtype->lkind != ListReprKind::TreeElement))
                {

                }
                else
                {
                    xxxx;
                }
            }
        }
    }

public:

};
