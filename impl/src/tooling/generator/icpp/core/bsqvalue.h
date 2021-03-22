//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "bsqmemory.h"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/rational.hpp>

//All values must be passed as uniform representation -- so we pick a void* -- then we cast and load/store the value
//Compiler will want to distinguish between SLValues and values that can be passed by value
typedef void* SLValue;

////
//Primitive value representations

typedef uint64_t BSQNone;
#define NoneValue 0
#define BSQ_NONE_VALUE nullptr

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

typedef uint64_t BSQNat;
typedef int64_t BSQInt;

typedef boost::multiprecision::checked_uint256_t BSQBigNat;
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

typedef boost::multiprecision::cpp_bin_float_double BSQFloat;
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

typedef boost::rational<BSQBigInt> BSQRational;

enum class StringKindTag : uint8_t
{
    Inline = 0x0,
    Flat,
    Rope
};

struct BSQStringInlineContents
{
    wchar_t data[6];
    uint8_t length;
    
    inline static void fromchar(wchar_t c, BSQStringInlineContents& into)
    {
        into.length = 1;
        into.data[0] = c;
    }

    inline static void fromchars(const wchar_t* begin, const wchar_t* end, BSQStringInlineContents& into)
    {
        into.length = (end - begin);
        GC_MEM_COPY(into.data, begin, (end - begin) * sizeof(wchar_t));
    }
};

struct BSQStringFlatContents
{
    uint16_t length;
};

struct BSQStringRopeContents
{
    //TODO
};

struct BSQString
{
    union
    {
        BSQStringInlineContents u_inline;
        BSQStringFlatContents u_flat;
        BSQStringRopeContents u_rope;
    };

    StringKindTag kind;

    inline static void initializeInline(size_t count, const wchar_t* chars, BSQString& into)
    {
        into.kind = StringKindTag::Inline;
        BSQStringInlineContents::fromchars(chars, chars + count, into.u_inline);
    }

    static void initializeFlat(size_t count, const wchar_t* chars, BSQString& into, BSQType* stype)
    {
        into.kind = StringKindTag::Flat;

        into.u_flat = static_cast<BSQStringFlatContents*>Allocator::GlobalAllocator.allocateDynamic(count, stype);
        into.u_flat.length = (uint16_t)count;
        
        GC_MEM_COPY(into.u_flat., chars, count);
    }

    inline int64_t count() const
    {
        if(this->u_sdata == nullptr)
        {
            return 0;
        }
        else if(BSQ_IS_VALUE_TAGGED(this->u_sdata))
        {
            return (int64_t)((BSQStringFlatContents*)this->u_sdata)->count;
        }
        else
        {
            return (int64_t)this->u_inline.data[3];
        }
    }

    inline void charat(uint64_t i, BSQString& into) const
    {
        if(BSQ_IS_VALUE_TAGGED(this->u_sdata))
        {
            return BSQStringInlineContents::fromchar(((BSQStringFlatContents*)this->u_sdata)->getContents()[i], into.u_inline);
        }
        else
        {
            return BSQStringInlineContents::fromchar(this->u_inline.data[i], into.u_inline);
        }
    }

    void concat(const BSQString& other, BSQString& into) const
    {
        into.u_sdata = nullptr;
        int64_t thissize = this->count();
        int64_t othersize = other.count();
        int64_t totalsize = thissize + othersize;

        if(totalsize == 0)
        {
            return;
        }

        //
        //TODO: here is where we can get fancy and do ropes or whatever
        //

        wchar_t* contents = into.u_inline.data;
        if(totalsize > 3)
        {
            into.u_sdata = Allocator::GlobalAllocator.allocateTPlus<BSQStringFlatContents, wchar_t>(META_DATA_LOAD_DECL(MetaData_StringFlatContents), totalsize, &contents);
        }

        if(thissize <= 3)
        {
            GC_MEM_COPY(contents, this->u_inline.data, thissize * sizeof(wchar_t));
        }
        else
        {
            GC_MEM_COPY(contents, ((BSQStringFlatContents*)this->u_sdata)->getContents(), thissize * sizeof(wchar_t));
        }

        if(othersize <= 3)
        {
            GC_MEM_COPY(contents, other.u_inline.data, othersize * sizeof(wchar_t));
        }
        else
        {
            GC_MEM_COPY(contents, ((BSQStringFlatContents*)other.u_sdata)->getContents(), othersize * sizeof(wchar_t));
        }
    }

    wchar_t substring(int64_t start, int64_t end, BSQString& into) const
    {
        into.u_sdata = nullptr;
        if(start == end)
        {
            return;
        }

        //
        //TODO: here is where we can get fancy and do slices or whatever
        //

        int64_t size = end - start;
        wchar_t* contents = into.u_inline.data;
        if(size > 3)
        {
            into.u_sdata = Allocator::GlobalAllocator.allocateTPlus<BSQStringFlatContents, wchar_t>(META_DATA_LOAD_DECL(MetaData_StringFlatContents), size, &contents);
        }

        int64_t thissize = this->count();
        if(thissize <= 3)
        {
            GC_MEM_COPY(contents, this->u_inline.data + start, size * sizeof(wchar_t));
        }
        else
        {
            GC_MEM_COPY(contents, ((BSQStringFlatContents*)this->u_sdata)->getContents() + start, size * sizeof(wchar_t));
        }
    }

    inline static bool keyEqual(const BSQString& l, const BSQString& r)
    {
        if(l.u_sdata == nullptr)
        {
            return r.u_sdata == nullptr; 
        }
        else if(BSQ_IS_VALUE_TAGGED(l.u_sdata))
        {
            if(BSQ_IS_VALUE_TAGGED(r.u_sdata))
            {
                return BSQStringInlineContents::keyEqual(l.u_inline, r.u_inline);
            }
            else
            {
                return false;

            }
        }
        else
        {
            if(BSQ_IS_VALUE_TAGGED(r.u_sdata))
            {
                return BSQStringFlatContents::keyEqual((BSQStringFlatContents*)l.u_sdata, (BSQStringFlatContents*)r.u_sdata);
            }
            else
            {
                return false;
            }
        }
    }

    inline static bool keyLess(const BSQString& l, const BSQString& r)
    {
        if(l.u_sdata == nullptr)
        {
            return r.u_sdata != nullptr; //empty string is less than everything 
        }
        else if(BSQ_IS_VALUE_TAGGED(l.u_sdata))
        {
            if(BSQ_IS_VALUE_TAGGED(r.u_sdata))
            {
                return BSQStringInlineContents::keyLess(l.u_inline, r.u_inline);
            }
            else
            {
                return true; //always shorter then
            }
        }
        else
        {
            if(BSQ_IS_VALUE_TAGGED(r.u_sdata))
            {
                return BSQStringFlatContents::keyEqual((BSQStringFlatContents*)l.u_sdata, (BSQStringFlatContents*)r.u_sdata);
            }
            else
            {
                return false; //always longer
            }
        }
    }

    static std::wstring display(const BSQString& v)
    {
        if(v.u_sdata == nullptr)
        {
            return std::wstring(L"");
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(v.u_sdata))
        {
            return BSQStringInlineContents::display(v.u_inline);
        }
        else
        {
            return BSQStringFlatContents::display((BSQStringFlatContents*)v.u_sdata);
        }
    }
};
constexpr BSQString EmptyString = {nullptr};
