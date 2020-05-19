//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqlist_decl.h"

#pragma once

namespace BSQ
{

template <typename Ty, typename T, typename RCIncF, typename RCDecF, typename DisplayF>
class BSQListOps
{
public:
    template <typename SetT, typename LambdaSC>
    static SetT* list_toset(Ty* l)
    {
        assert(false); //NOT IMPLEMENTED
        return nullptr;
    }

    template <typename LambdaP>
    static bool list_all(Ty* l, LambdaP p)
    {
        return std::all_of(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static bool list_none(Ty* l, LambdaP p)
    {
        return std::none_of(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static bool list_any(Ty* l, LambdaP p)
    {
        return std::any_of(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static int64_t list_count(Ty* l, LambdaP p)
    {
        return (int64_t)std::count_if(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static int64_t list_countnot(Ty* l, LambdaP p)
    {
        return (int64_t)l->entries.size() - (int64_t)std::count_if(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static int64_t list_indexof(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto uend = std::find_if(ib, ie, p);
        return s + (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    static int64_t list_indexofnot(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto uend = std::find_if_not(ib, ie, p);
        return s + (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    static int64_t list_indexoflast(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        for(int64_t i = e; i > s; --i)
        {
            if(p(l->entries[i]))
            {
                return i;
            }
        }
        return s;
    }

    template <typename LambdaP>
    static int64_t list_indexoflastnot(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        for(int64_t i = e; i > s; --i)
        {
            if(!p(l->entries[i]))
            {
                return i;
            }
        }
        return s;
    }

    template <typename LambdaC>
    static T list_min(Ty* l, LambdaC cmp)
    {
        return *std::min_element(l->entries.begin(), l->entries.end(), cmp);
    }

    template <typename LambdaC>
    static T list_max(Ty* l, LambdaC cmp)
    {
        return *std::max_element(l->entries.begin(), l->entries.end(), cmp);
    }

    static int64_t list_sum_int(Ty* l)
    {
        int64_t res = std::reduce(l->entries.begin(), l->entries.end(), 0, [](int64_t a, int64_t b) {
            if((a == std::numeric_limits<int64_t>::max()) | (b == std::numeric_limits<int64_t>::max())) 
            {
                return std::numeric_limits<int64_t>::max();
            }
            else 
            {
                int64_t res = 0;
                if(__builtin_add_overflow(a, b, &res) || INT_OOF_BOUNDS(res)) 
                {
                    res = std::numeric_limits<int64_t>::max();
                }
                return res;
            }
        });

        if(res == std::numeric_limits<int64_t>::max())
        {
            BSQ_ABORT("List<Int>.sum Overflow", "internal", -1);
        }

        return res;
    }

    static BSQBigInt* list_sum_bigint(Ty* l)
    {
        assert(false);
    }

    static BSQBigInt* list_sum_mixed(Ty* l)
    {
        assert(false);
    }

    template <typename LambdaP>
    static Ty* list_filter(Ty* l, LambdaP p)
    {
        std::vector<T> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, p](T& v) {
            if(p(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_filternot(Ty* l, LambdaP p)
    {
        std::vector<T> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, p](T& v) {
            if(!p(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static ListU* list_oftype(Ty* l, LambdaTC tc, LambdaCC cc)
    {
        std::vector<U> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, tc, cc](T& v) {
            if(tc(v))
            {
                entries.push_back(cc(v));
            }
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static ListU* list_cast(Ty* l, LambdaTC tc, LambdaCC cc)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [tc, cc](T& v) -> U {
            BSQ_ASSERT(tc(v), "Invalid element to cast");

            return cc(v);
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    static Ty* list_slice(Ty* l, int64_t s, int64_t e)
    {
        std::vector<T> entries;
        entries.reserve(e - s);

        std::transform(l->entries.begin() + s, l->entries.begin() + e, std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_takewhile(Ty* l)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), LambdaP{});
        return BSQListOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discardwhile(Ty* l)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), LambdaP{});
        return BSQListOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaP>
    static Ty* list_takeuntil(Ty* l)
    {
        auto uend = std::find_if(l->entries.begin(), l->entries.end(), LambdaP{});
        return BSQListOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discarduntil(Ty* l)
    {
        auto uend = std::find_if(l->entries.begin(), l->entries.end(), LambdaP{});
        return BSQListOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaCMP, typename LambdaEQ>
    static Ty* list_unique(Ty* l)
    {
        std::vector<T> vv(l->entries.begin(), l->entries.end());
        std::stable_sort(vv.begin(), vv.end(), LambdaCMP{});

        auto uend = std::unique(vv.begin(), vv.end(), LambdaEQ{});
        vv.erase(uend, vv.end());

        std::for_each(vv.begin(), vv.end(), [](T& v) -> T {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(vv));
    }

    static Ty* list_reverse(Ty* l)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.crbegin(), l->entries.crend(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaF>
    static ListU* list_map(Ty* l, LambdaF f)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [f](T& v) -> U {
            return f(v);
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaF>
    static ListU* list_mapindex(Ty* l, LambdaF f)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        for(int64_t i = 0; i < (int64_t)l->entries.size(); ++i)
        {
            entries.push_back(f(i, l->entries[i]));
        }

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaGet>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_project(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            return LambdaGet{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaGet>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_tryproject(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            return LambdaGet{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaZip>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_zipindex(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        for(int64_t i = 0; i < (int64_t)l->entries.size(); ++i)
        {
            entries.push_back(LambdaZip{}(i, l->entries[i]));
        }

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, typename RT, typename RT_RCDecF, typename RT_DisplayF, MIRNominalTypeEnum ntype, typename LambdaP, typename LambdaZip>
    static BSQList<RT, RT_RCDecF, RT_DisplayF>* list_join(Ty* l, BSQList<U, U_RCDecF, U_DisplayF>* ol)
    {
        std::vector<RT> entries;

        std::for_each(l->entries.begin(), l->entries.end(), [ol, &entries](T& v) {
            std::for_each(ol->entries.begin(), ol->entries.end(), [&v, &entries](U& u) {
                if(LambdaP{}(v, u))
                {
                    entries.push_back(LambdaZip{}(v, u));
                }
            });
        });

        return BSQ_NEW_NO_RC((BSQList<RT, RT_RCDecF, RT_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCIncF, typename U_RCDecF, typename U_DisplayF, typename RT, typename RT_RCDecF, typename RT_DisplayF, MIRNominalTypeEnum ntype, typename LambdaP, typename LambdaZip>
    static BSQList<RT, RT_RCDecF, RT_DisplayF>* list_joingroup(Ty* l, BSQList<U, U_RCDecF, U_DisplayF>* ol)
    {
        std::vector<RT> entries;

        std::for_each(l->entries.begin(), l->entries.end(), [ol, &entries](T& v) {
            std::vector<U> ue;

            std::for_each(ol->entries.begin(), ol->entries.end(), [&v, &ue](U& u) {
                if(LambdaP{}(v, u))
                {
                    ue.push_back(U_RCIncF{}(u));
                }
            });

            entries.push_back(LambdaZip{}(v, ue));
        });

        return BSQ_NEW_NO_RC((BSQList<RT, RT_RCDecF, RT_DisplayF>), ntype, move(entries));
    }

    static Ty* list_append(Ty* l, Ty* lp)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size() + lp->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        std::transform(lp->entries.begin(), lp->entries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename K, typename K_RCIncF, typename K_CMP, typename LambdaPF, typename MType, typename LambdaMC> 
    static MType* list_partition(Ty* l)
    {
        std::map<K, std::vector<T>, K_CMP> partitions;
        std::for_each(l->entries.begin(), l->entries.end(), [&partitions](T& v) {
            auto k = LambdaPF{}(v);
            auto pp = partitions.find(k);

            if(pp != partitions.end())
            {
                pp->second.push_back(RCIncF(v));
            }
            else 
            {
                partitions.emplace(k, std::vector<T>{RCIncF(v)});
            }
        });

        std::map<K, Ty*, K_CMP> mentries;

        auto ltype = l->nominalType;
        std::transform(partitions.begin(), partitions.end(), std::inserter(mentries, mentries.end()), [ltype](std::pair<K, std::vector<T>>& me) -> std::pair<K, Ty*> {
            auto le = BSQ_NEW_NO_RC(Ty, ltype, move(me.second));
            return std::make_pair(K_RCIncF{}(me.first), INC_REF_DIRECT(Ty, le));
        });

        return LambdaMC{}(move(mentries));
    }

    template <typename LambdaCMP>
    static Ty* list_sort(Ty* l)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::for_each(l->begin(), l->end(), [&entries](T& v) {
            entries.push_back(RCIncF{}(v));
        });
        std::stable_sort(entries.begin(), entries.end(), LambdaCMP{});

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename K, typename K_RCDecF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename LambdaKF, typename LambdaVF, typename MType, typename LambdaMC, bool merge> 
    static MType* list_tomap(Ty* l)
    {
        std::map<K, V, K_CMP> mentries;
        
        std::transform(l->entries.begin(), l->entries.end(), std::inserter(mentries, mentries.end()), [&mentries](T& v) {
            auto k = LambdaKF{}(v);
            auto vv = LambdaVF{}(v);

            auto epos = mentries.find(k);
            if(epos != mentries.end())
            {
                BSQ_ASSERT(merge, "Duplicate keys are not allowed");
                
                K_RCDecF{}(epos->first);
                V_RCDecF{}(epos->second); 
            }

            mentries.push_back(std::make_pair(k, vv));
        });

        return LambdaMC{}(move(mentries));
    }

    template <typename V, typename LambdaVF, typename MType, typename LambdaMC> 
    static MType* list_toindexmap(Ty* l)
    {
        std::vector<std::pair<int64_t, V>> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            auto v = LambdaVF{}(l->entries[i]);
            mentries.push_back(std::make_pair(i, v));
        }

        return LambdaMC{}(move(mentries));
    }
};

class BSQListUtilOps
{
public:
    template <typename LType1, typename LType2, typename RType, typename ZType, MIRNominalTypeEnum ntype, typename LambdaZ>
    static RType* list_zip(LType1* l1, LType2* l2)
    {
        std::vector<ZType> entries;
        entries.reserve(l1->entries.size());

        for(size_t i = 0; i < l1->entries.size(); ++i)
        {
            entries.push_back(LambdaZ{}(l1->entries[i], l2->entries[i]));
        }

        return BSQ_NEW_NO_RC(RType, ntype, move(entries));
    }

    template <typename RType1, MIRNominalTypeEnum ntype1, typename VType, typename RType2, MIRNominalTypeEnum ntype2, typename UType, typename LType, typename LambdaUZ>
    static std::pair<RType1*, RType2*> list_unzip(LType* l)
    {
        std::vector<VType> ventries;
        ventries.reserve(l->entries.size());

        std::vector<UType> uentries;
        uentries.reserve(l->entries.size());

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            std::pair<VType, UType> rr = LambdaUZ{}(l->entries[i]);

            ventries.push_back(rr.first);
            uentries.push_back(rr.second);
        }

        auto l1 = BSQ_NEW_NO_RC(RType1, ntype1, move(ventries));
        auto l2 = BSQ_NEW_NO_RC(RType2, ntype2, move(uentries));

        return std::make_pair(l1, l2);
    }

    template <typename T, typename RCIncF, typename RCDecF, typename DisplayF, MIRNominalTypeEnum ntype, typename ListT>
    static BSQList<T, RCDecF, DisplayF>* list_concat(ListT* l)
    {
        std::vector<T> entries;

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            std::vector<T>& llentries = (l->entries[i])->entries;
            std::transform(llentries.begin(), llentries.end(), std::back_inserter(entries), [](T& v) -> T {
                return RCIncF{}(v);
            });
        }

        return BSQ_NEW_NO_RC((BSQList<T, RCDecF, DisplayF>), ntype, move(entries));
    }

    template <typename T, typename RCIncF, typename RCDecF, typename DisplayF, MIRNominalTypeEnum ntype>
    static BSQList<T, RCDecF, DisplayF>* list_fill(int64_t k, T val)
    {
        std::vector<T> entries;
        entries.reserve(k);

        for(size_t i = 0; i < k; ++i)
        {
            entries.push_back(RCIncF{}(val));
        }

        return BSQ_NEW_NO_RC((BSQList<int64_t, RCDecFunctor_int64_t, DisplayFunctor_int64_t>), ntype, move(entries));
    }

    template <MIRNominalTypeEnum ntype>
    static BSQList<int64_t, RCDecFunctor_int64_t, DisplayFunctor_int64_t>* list_range(int64_t start, int64_t end)
    {
        std::vector<int64_t> entries;
        entries.reserve(end - start);

        for(size_t i = 0; i < (end - start); ++i)
        {
            entries.push_back(start + i);
        }

        return BSQ_NEW_NO_RC((BSQList<int64_t, RCDecFunctor_int64_t, DisplayFunctor_int64_t>), ntype, move(entries));
    }
};

}