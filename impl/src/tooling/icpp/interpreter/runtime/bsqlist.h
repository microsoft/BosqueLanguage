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

    inline static uint64_t getPVCount(void* repr) 
    {
        return *((uint64_t*)repr);
    }

    inline StorageLocationPtr get(void* repr, size_t i) const
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

class BSQListForwardIterator
{
public:
    std::vector<BSQListTreeRepr*> iterstack;
    size_t curr;
    size_t lmax;
    void* lcurr;
    const BSQPartialVectorType* lctype;
    uint16_t icurr;
    uint16_t imax;

    BSQListForwardIterator(BSQList& lroot) 
    : iterstack(), curr(0), lmax(0), lcurr(nullptr), lctype(nullptr), icurr(0), imax(0)
    {
        if(lroot.repr != nullptr) {
            this->lmax = dynamic_cast<const BSQListReprType*>(lroot.lreprtype)->getCount(lroot.repr); 

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
        while(this->iterstack.back()->r == rr)
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

    size_t distance() const
    {
        return this->curr;
    }
};

class BSQStringReverseIterator : public CharCodeIterator
{
private:
    void initializeIteratorPosition(int64_t curr);
    
    void increment_utf8byte();
public:
    BSQString* sstr;
    int64_t curr;
    int64_t strmax;
    uint8_t* cbuff;
    uint16_t cpos;

    BSQStringReverseIterator(BSQString* sstr, int64_t curr) : CharCodeIterator(), sstr(sstr), curr(curr), strmax(strmax), cbuff(nullptr), cpos(0) 
    {
        if(IS_INLINE_STRING(sstr))
        {
            this->strmax = (int64_t)BSQInlineString::utf8ByteCount(sstr->u_inlineString);
        }
        else
        {
            this->strmax = (int64_t)GET_TYPE_META_DATA_AS(BSQStringReprType, sstr->u_data)->utf8ByteCount(sstr->u_data);
        }

        this->initializeIteratorPosition(curr);
        if(curr == strmax - 1)
        {
            auto utfbyte = this->cbuff[this->cpos];
            if((utfbyte & 0x8) == 1)
            {
                //not implemented
                assert(false);
            }
        }
    }

    virtual ~BSQStringReverseIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != -1;
    }

    virtual void advance() override final
    {
        assert(this->valid());
        this->increment_utf8byte();

        if(this->valid()) [[likely]]
        {
            auto utfbyte = this->cbuff[this->cpos];
            if((utfbyte & 0x8) == 1) [[unlikely]]
            {
                //not implemented
                assert(false);
            }
        }
    }

    virtual CharCode get() const override final
    {
        assert(this->valid());

        auto utfbyte = this->cbuff[this->cpos];
        if((utfbyte & 0x8) == 0) [[likely]]
        {
            return (CharCode)utfbyte;
        }
        else [[unlikely]]
        {
            //not implemented
            assert(false);
        }
    }

    virtual size_t distance() const override final
    {
        return this->strmax - (this->curr + 1);
    }

    virtual void resetTo(size_t distance) override final
    {
        this->initializeIteratorPosition(this->strmax - (distance + 1));
    }

    void advance_byte()
    {
        assert(this->valid());
        this->increment_utf8byte();
    } 

    uint8_t get_byte() const
    {
        assert(this->valid());
        return this->cbuff[this->cpos];
    } 
};

class BSQListOps
{
public:

};
