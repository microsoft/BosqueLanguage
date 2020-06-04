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
    template <typename ListT, MIRNominalTypeEnum ntype>
    static Ty* list_concat(ListT l)
    {
        std::vector<T> entries;

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            std::vector<T>& llentries = (l->entries[i])->entries;
            std::transform(llentries.begin(), llentries.end(), std::back_inserter(entries), [](T v) -> T {
                return RCIncF{}(v);
            });
        }

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }

    template <MIRNominalTypeEnum ntype>
    static Ty* list_fill(int64_t k, T val)
    {
        std::vector<T> entries;
        entries.reserve(k);

        for(size_t i = 0; i < k; ++i)
        {
            entries.emplace_back(RCIncF{}(val));
        }

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }

    template <typename SetT, typename LambdaSC>
    static SetT* list_toset(Ty* l)
    {
        assert(false); //NOT IMPLEMENTED
        return nullptr;
    }

    template <typename LambdaP>
    static BSQBool list_all(Ty* l, LambdaP p)
    {
        return std::all_of(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static BSQBool list_none(Ty* l, LambdaP p)
    {
        return std::none_of(l->entries.begin(), l->entries.end(), p);
    }

    template <typename LambdaP>
    static BSQBool list_any(Ty* l, LambdaP p)
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
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, p](T v) {
            if(p(v))
            {
                entries.emplace_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_filternot(Ty* l, LambdaP p)
    {
        std::vector<T> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, p](T v) {
            if(!p(v))
            {
                entries.emplace_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static ListU* list_oftype(Ty* l, LambdaTC tc, LambdaCC cc)
    {
        std::vector<U> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries, tc, cc](T v) {
            if(tc(v))
            {
                entries.emplace_back(cc(v));
            }
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static ListU* list_cast(Ty* l, LambdaTC tc, LambdaCC cc)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [tc, cc](T v) -> U {
            BSQ_ASSERT(tc(v), "abort -- invalid element to cast List<T>::cast");

            return cc(v);
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    static Ty* list_slice(Ty* l, int64_t s, int64_t e)
    {
        std::vector<T> entries;
        entries.reserve(e - s);

        std::transform(l->entries.begin() + s, l->entries.begin() + e, std::back_inserter(entries), [](T v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_takewhile(Ty* l, LambdaP p)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), p);
        return BSQListOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discardwhile(Ty* l, LambdaP p)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), p);
        return BSQListOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaP>
    static Ty* list_takeuntil(Ty* l, LambdaP p)
    {
        auto uend = std::find_if(l->entries.begin(), l->entries.end(), p);
        return BSQListOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discarduntil(Ty* l, LambdaP p)
    {
        auto uend = std::find_if(l->entries.begin(), l->entries.end(), p);
        return BSQListOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaCMP>
    static Ty* list_unique(Ty* l)
    {
        std::vector<T> vv;
        std::set<T, LambdaCMP> seen;

        std::for_each(l->entries.begin(), l->entries.end(), [&seen, &vv](T v) {
            if(seen.find(v) == seen.cend()) 
            {
                seen.insert(v);
                vv.emplace_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(vv));
    }

    static Ty* list_reverse(Ty* l)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.rbegin(), l->entries.rend(), std::back_inserter(entries), [](T v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaF>
    static ListU* list_map(Ty* l, LambdaF f)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [f](T v) -> U {
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
            entries.emplace_back(f(l->entries[i], i));
        }

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename MapT, typename RCIncU>
    static ListU* list_project(Ty* l, MapT* m)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [m](T v) -> U {
            U vv;
            bool found = m->tryGetValue(v, &vv);
            BSQ_ASSERT(found, "abort -- missing key for List<T>::projectWith");

            return RCIncU{}(vv);
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename LU, typename UU, MIRNominalTypeEnum ntype, typename MapT, typename RCIncU, typename LambdaCC>
    static ListU* list_tryproject(Ty* l, MapT* m, LU unone, LambdaCC cc)
    {
        std::vector<LU> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [m, unone, cc](T v) -> LU {
            UU vv;
            if(m->tryGetValue(v, &vv))
            {
                return RCIncU{}(cc(vv));
            }
            else
            {
                return unone;
            }
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename MapT, typename RCIncU>
    static ListU* list_defaultproject(Ty* l, MapT* m, U dval)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [m, dval](T v) -> U {
            U vv;
            if(m->tryGetValue(v, &vv))
            {
                return RCIncU{}(vv);
            }
            else
            {
                return RCIncU{}(dval);
            }
        });

        return BSQ_NEW_NO_RC(ListU, ntype, move(entries));
    }

    template <typename ListIT, typename IT, MIRNominalTypeEnum ntype, typename ITConsWInc>
    static ListIT* list_zipindex(Ty* l, ITConsWInc itc)
    {
        std::vector<IT> entries;

        for(int64_t i = 0; i < (int64_t)l->entries.size(); ++i)
        {
            entries.emplace_back(itc(i, l->entries[i]));
        }

        return BSQ_NEW_NO_RC(ListIT, ntype, move(entries));
    }

    template <typename ListTU, typename TU, typename ListU, typename U, MIRNominalTypeEnum ntype, typename TUConsWInc, typename LambdaP>
    static ListTU* list_join(Ty* l, ListU* ol, TUConsWInc utc, LambdaP p)
    {
        std::vector<TU> entries;

        std::for_each(l->entries.begin(), l->entries.end(), [utc, p, ol, &entries](T v) {
            std::for_each(ol->entries.begin(), ol->entries.end(), [utc, p, v, &entries](U u) {
                if(p(v, u))
                {
                    entries.emplace_back(utc(v, u));
                }
            });
        });

        return BSQ_NEW_NO_RC(ListTU, ntype, move(entries));
    }

    template <typename ListTLU, typename TLU, typename ListU, typename U, MIRNominalTypeEnum lutype, MIRNominalTypeEnum ntype, typename U_RCIncF, typename TLUConsWInc, typename LambdaP>
    static ListTLU* list_joingroup(Ty* l, ListU* ol, TLUConsWInc lutc, LambdaP p)
    {
        std::vector<TLU> entries;
        
        std::for_each(l->entries.begin(), l->entries.end(), [lutc, p, ol, &entries](T v) {

            std::vector<U> ue;
            std::for_each(ol->entries.begin(), ol->entries.end(), [p, v, &ue](U u) {
                if(p(v, u))
                {
                    ue.emplace_back(U_RCIncF{}(u));
                }
            });

            ListU* lu = INC_REF_DIRECT(ListU, BSQ_NEW_NO_RC(ListU, lutype, std::move(ue))); 
            entries.emplace_back(lutc(v, lu));
        });

        return BSQ_NEW_NO_RC(ListTLU, ntype, move(entries));
    }

    static Ty* list_append(Ty* l, Ty* lp)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size() + lp->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T v) -> T {
            return RCIncF{}(v);
        });

        std::transform(lp->entries.begin(), lp->entries.end(), std::back_inserter(entries), [](T v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename MType, MIRNominalTypeEnum ntype, typename MECType, typename K, typename K_RCDecRef, typename K_CMP, typename LambdaPF, typename LambdaMEC> 
    static MType* list_partition(Ty* l, LambdaPF pf, LambdaMEC lmec)
    {
        std::map<K, std::vector<T>, K_CMP> partitions;
        std::for_each(l->entries.begin(), l->entries.end(), [pf, &partitions](T v) {
            auto k = pf(v);
            auto pp = partitions.find(k);

            if(pp != partitions.end())
            {
                pp->second.emplace_back(RCIncF{}(v));
                K_RCDecRef{}(k); //pf did inc so we need to dec
            }
            else 
            {
                partitions.emplace(k, std::vector<T>{RCIncF{}(v)});
            }
        });

        std::vector<MECType> mentries;
        std::transform(partitions.begin(), partitions.end(), std::back_inserter(mentries), [lmec, l](std::pair<K, std::vector<T>>&& me) -> MECType {
            auto le = BSQ_NEW_NO_RC(Ty, l->nominalType, std::move(me.second));
            return lmec(me.first, INC_REF_DIRECT(Ty, le));
        });

        return BSQ_NEW_NO_RC(MType, ntype, move(mentries));
    }

    template <typename LambdaCMP>
    static Ty* list_sort(Ty* l, LambdaCMP cmp)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::for_each(l->entries.begin(), l->entries.end(), [&entries](T v) {
            entries.emplace_back(RCIncF{}(v));
        });
        std::stable_sort(entries.begin(), entries.end(), cmp);

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename MEntryCons> 
    static MType* list_toindexmap(Ty* l, MEntryCons mec)
    {
        std::vector<MEntryType> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            mentries.emplace_back(mec(i, RCIncF{}(l->entries[i])));
        }

        return BSQ_NEW_NO_RC(MType, ntype, move(mentries));
    }

    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename LambdaVF, typename MEntryCons> 
    static MType* list_transformindexmap(Ty* l, LambdaVF vf, MEntryCons mec)
    {
        std::vector<MEntryType> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            mentries.emplace_back(mec(i, vf(l->entries[i])));
        }

        return BSQ_NEW_NO_RC(MType, ntype, move(mentries));
    }

    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename K, typename K_CMP, typename V, typename LambdaKF, typename LambdaVF, typename MEntryCons> 
    static MType* list_transformmap(Ty* l, LambdaKF kf, LambdaVF vf, MEntryCons mec)
    {
        std::map<K, MEntryType, K_CMP> mentries;
        
        std::transform(l->entries.begin(), l->entries.end(), std::inserter(mentries, mentries.end()), [kf, vf, mec, &mentries](T v) {
            auto k = kf(v);
            auto vv = vf(v);

            auto epos = mentries.find(k);
            BSQ_ASSERT(epos == mentries.end(), "abort -- duplicate keys are not allowed in List<T>::toMap");

            return std::make_pair(k, mec(k, vv));
        });

        std::vector<MEntryType> rvv;
        std::transform(mentries.begin(), mentries.end(), std::back_inserter(rvv), [](const std::pair<K, MEntryType>& e) { return e.second; });
        return BSQ_NEW_NO_RC(MType, ntype, move(rvv));
    }
};

class BSQListUtilOps
{
public:
    template <typename LType1, typename LType2, typename RType, typename ZType, MIRNominalTypeEnum ntype, typename LambdaZ>
    static RType* list_zip(LType1* l1, LType2* l2, LambdaZ zc)
    {
        std::vector<ZType> entries;
        entries.reserve(l1->entries.size());

        for(size_t i = 0; i < l1->entries.size(); ++i)
        {
            entries.emplace_back(zc(l1->entries[i], l2->entries[i]));
        }

        return BSQ_NEW_NO_RC(RType, ntype, move(entries));
    }

    template <typename RType1, typename UType, MIRNominalTypeEnum ntype1, typename RType2, typename VType, MIRNominalTypeEnum ntype2, typename LType, typename LambdaUZ>
    static std::pair<RType1*, RType2*> list_unzip(LType* l, LambdaUZ uz)
    {
        std::vector<UType> uentries;
        uentries.reserve(l->entries.size());

        std::vector<VType> ventries;
        ventries.reserve(l->entries.size());

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            std::pair<UType, VType> rr = uz(l->entries[i]);

            uentries.emplace_back(rr.first);
            ventries.emplace_back(rr.second);
        }

        auto l1 = BSQ_NEW_NO_RC(RType1, ntype1, move(uentries));
        auto l2 = BSQ_NEW_NO_RC(RType2, ntype2, move(ventries));

        return std::make_pair(l1, l2);
    }

    template <typename RType, MIRNominalTypeEnum ntype>
    static RType* list_range(int64_t start, int64_t end)
    {
        std::vector<int64_t> entries;
        entries.reserve(end - start);

        for(size_t i = 0; i < (end - start); ++i)
        {
            entries.emplace_back(start + i);
        }

        return BSQ_NEW_NO_RC(RType, ntype, move(entries));
    }
};

}