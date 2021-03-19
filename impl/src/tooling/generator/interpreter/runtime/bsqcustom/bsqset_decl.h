//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../bsqvalue.h"

namespace BSQ
{
template <typename T, typename T_CMP, typename T_EQ>
struct BSQSet 
{
    size_t count;

    inline bool has(T v)
    {
        T* entries = GET_COLLECTION_START_FIXED(this, sizeof(BSQSet));
        auto ipos = std::lower_bound(entries, entries + this->count, v, [](const T& a, const T& b){ return T_CMP{}(a, b); });

        return ipos != entries + this->count && T_EQ{}(v, *ipos);
    }

    template <typename T_INC>
    inline static std::vector<T> singletonInit(std::vector<T> src)
    {
        std::stable_sort(src.begin(), src.end(), T_CMP{});
        auto end = std::unique(src.begin(), src.end(), T_EQ{});

        std::vector<T> res;
        res.reserve(std::distance(src.begin(), end));
        std::transform(src.begin(), end, back_inserter(res), T_INC{});

        return res;
    }

    template <typename Ty, uint16_t count>
    inline static Ty* singletonInitSlow(MetaData* mdata, T* rcontents, size_t rsize)
    {
        T* contents = nullptr;
        Ty* alloc = Allocator::GlobalAllocator.allocateSafePlusDynamic<Ty, T>(mdata, rsize);

        std::copy(rcontents, rcontents + rsize, contents);
        
        return alloc;
    }

    template <typename Ty, uint16_t count>
    inline static Ty* singletonInit(MetaData* mdata, std::initializer_list<Value> values)
    {
        T* contents = nullptr;
        Ty* alloc = Allocator::GlobalAllocator.allocateSafePlus<Ty, T, count>(mdata);

        std::copy(values.begin(), values.end(), contents);
        std::stable_sort(contents, contents + count, T_CMP{});
        auto end = std::unique(contents, contents + count, T_EQ{});

        if(end == contents + count)
        {
            return alloc;
        }
        else
        {
            return BSQSet::singletonInitSlow(mdata, contents, std::distance(contents, end));
        }
    }

    template <typename DisplayF>
    std::wstring display() const
    {
        std::wstring ss(L"{");
        xxxx;
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ss += L", ";
            }
            first = false;

            ss += DisplayF{}(*iter);
        }
        ss += L"}";

        return ss;
    }
};
}
