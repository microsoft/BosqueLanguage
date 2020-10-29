//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../bsqvalue.h"

namespace BSQ
{
//
//TODO: do we want to allow for list repr as tree or view structures (like for strings) to provide fast append/slice operations
//

template <typename T>
struct BSQList
{
    size_t count;

    template <typename Ty, uint16_t count>
    inline static Ty* singletonInit(MetaData* mdata, std::initializer_list<Value> values)
    {
        T* contents = nullptr;
        Ty* alloc = Allocator::GlobalAllocator.allocateSafePlus<Ty, T, count>(mdata);

        std::copy(values.begin(), values.end(), contents);

        return alloc;
    }

    inline T* begin()
    {
        return (T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t));
    }

    inline T* end()
    {
        return ((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t))) + this->count;
    }

    inline T& at(size_t i)
    {
        return *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + i);
    }

    inline void copyto(size_t ipos, BSQList* from, size_t fpos)
    {
        *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + ipos) = *((T*)GET_COLLECTION_START_FIXED(from, sizeof(size_t)) + fpos);
    }

    inline void store(size_t ipos, const T& v)
    {
        *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + ipos) = v;
    }

    template <typename DisplayF>
    std::wstring display() const
    {
        T* vals = GET_COLLECTION_START_FIXED(this, sizeof(BSQList<T>));
        std::wstring ls(L"{");
        for (size_t i = 0; i < this->count; ++i)
        {
            if (i != 0)
            {
                ls += L", ";
            }
            ls += DisplayF{}(vals[i]);
        }
        ls += L"}";

        return ls;
    }

    template <typename Ty, typename ListT>
    inline static Ty* list_concat(ListT& l, MetaData* mdata)
    {
        size_t totalct = std::transform_reduce(
            l->begin(), 
            l->end(), 
            0,
            [](const Ty* ll) => { return ll->count; },
            [] (size_t acc, size_t v) => { return acc + v; }
        );

        T* contents = nullptr;
        Ty* res = Allocator::GlobalAllocator.allocateTPlus<Ty, T>(mdata, totalct, &contents);
        
        size_t cpos = 0;
        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            Ty* ll = l->at(i);
            std::copy(ll->begin(), ll->end(), contents + cpos);
            
            cpos += ll->count;
        }

        return res;
    }

    template <std::execution ep>
    inline int64_t list_sum_int()
    {
        int64_t res = std::reduce(ep, this->begin(), this->end(), 0, [](int64_t a, int64_t b) {
            if((a == std::numeric_limits<int64_t>::max()) | (b == std::numeric_limits<int64_t>::max())) 
            {
                return std::numeric_limits<int64_t>::max();
            }
            else 
            {
                int64_t opres = 0;
                if(__builtin_add_overflow(a, b, &opres) || INT_OOF_BOUNDS(opres)) 
                {
                    opres = std::numeric_limits<int64_t>::max();
                }
                return opres;
            }
        });

        BSQ_ASSERT(res != std::numeric_limits<int64_t>::max());
        return res;
    }

    BSQBigInt* list_sum_bigint()
    {
        assert(false);
    }

    BSQBigInt* list_sum_mixed()
    {
        assert(false);
    }
};

struct ListOps
{
    template <typename ListU, typename ListV, typename ListTU, typename LambdaCons, typename LambdaP>
    inline static void list_join(ListU& lu, ListV& lv, ListTU& res, MetaData* resmeta, LambdaCons cc, LambdaP p)
    {
        size_t capacity = res->count;
        size_t rcount = 0;
        for(size_t i = 0; i < lu->count; ++i)
        {
            for(size_t j = 0; j < lv->count; ++j)
            {
                if(rcount == capacity)
                { 
                    Allocator::GlobalAllocator.grow(res, resmeta->datasize, resmeta->sizeentry, capacity);
                }

                if(p(lu->at(i), lv->at(j))) 
                { 
                    cc(lu->at(i), lv->at(j), res);
                }
            }
        }

        Allocator::GlobalAllocator.shrink(res, resmeta->datasize, resmeta->sizeentry, capacity, rcount);
    }

    template <typename ListU, typename ListV, typename ListTU, typename LambdaListCons, typename LambdaCons, typename LambdaP>
    inline static void* list_joingroup(ListU& lu, ListV& lv, ListTU& res, MetaData* llmeta, LambdaListCons llc, LambdaCons cc, LambdaP p)
    {
        for(size_t i = 0; i < lu->count; ++i)
        {
            size_t capacity = std::min((size_t)256, lu->count, lv->count);
            ListV tmpl = llc(capacity);
            Allocator::GlobalAllocator.pushRoot(tmpl);

            size_t rcount = 0;
            for(size_t j = 0; j < lv->count; ++j)
            {
                if(rcount == capacity)
                { 
                    Allocator::GlobalAllocator.grow(tmpl, llmeta->datasize, llmeta->sizeentry, capacity);
                }

                if(p(lu->at(i), lv->at(j))) 
                { 
                    cc(lu->at(i), lv->at(j), tmpl);
                }
            }

            Allocator::GlobalAllocator.shrink(tmpl, llmeta->datasize, llmeta->sizeentry, capacity, rcount);
            Allocator::GlobalAllocator.popRoot();
            res->store(tmpl, i);
        }
    }

    template <typename K, typename K_CMP>
    struct KPTR_CMP 
    {
        inline bool operator()(const K* k1, const K* k2)
        {
            return K_CMP{}(*k1, *k2);
        } 
    };

    template <typename Ty, typename V, typename KLIST, typename MType, typename K, typename K_CMP, typename LambdaMEC, typename V_OP> 
    inline static void list_partition(Ty& l, KLIST& kl, MType& res, LambdaMEC lmec, V_OP vop)
    {
        std::map<K*, std::pair<size_t, std::pair<size_t, size_t>>, KPTR_CMP<K, K_CMP>> partitionMap;

        size_t mpos = 0;
        size_t mcapacity = res.count;
        for(size_t i = 0; i < l->count; ++i)
        {
            auto iter = partitionMap.find(&kl->at(i));
            if(iter == partitions.end())
            {
                if(mpos == mcapacity)
                {
                    Allocator::GlobalAllocator.grow(res, GET_TYPE_META_DATA(res)->datasize, GET_TYPE_META_DATA(res)->sizeentry, mcapacity);
                }

                size_t isize = lmec(kl->at(i), l->at(i), res->at(mpos));
                partitionMap[&kl->at(i)] = std::make_pair(mpos++, std::make_pair(0, isize));
            }
            else 
            {
                std::pair<size_t, size_t>& sizes = res->at(iter->second.second);
                if(sizes.first == sizes.second)
                {
                    Allocator::GlobalAllocator.grow(res->at(iter->second.first), GET_TYPE_META_DATA(l)->datasize, GET_TYPE_META_DATA(l)->sizeentry, sizes.second);
                }

                vop(res->at(iter->second.first))->copyto(sizes.first++, l, i);
            }
        }

        Allocator::GlobalAllocator.shrink(res, GET_TYPE_META_DATA(res)->datasize, GET_TYPE_META_DATA(res)->sizeentry, mcapacity, mpos);
        for(auto iter = partitionMap.begin(); iter != partitionMap.end(); ++iter)
        {
            Allocator::GlobalAllocator.shrink(vop(res->at(iter->second.first)), GET_TYPE_META_DATA(l)->datasize, GET_TYPE_META_DATA(l)->sizeentry, iter->second.second.second, iter->second.second.first);
        }
    }
};
}
