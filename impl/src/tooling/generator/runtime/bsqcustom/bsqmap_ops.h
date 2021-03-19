//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqmap_decl.h"

namespace BSQ
{
template <typename Ty, typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF>
class BSQMapOps
{
public:
    template <typename ListT, typename K_RCIncF, MIRNominalTypeEnum ntype>
    static ListT* map_key_list(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> K {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename SetT, typename K_RCIncF, MIRNominalTypeEnum ntype>
    static SetT* map_key_set(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> K {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC(SetT, ntype, move(entries));
    }

    template <typename ListT, typename V_RCIncF, MIRNominalTypeEnum ntype>
    static ListT* map_values(Ty* m)
    {
        std::vector<V> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> V {
            return V_RCIncF{}(v.value);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename ListT, typename MapEntryT, MIRNominalTypeEnum ntype, typename LambdaMEC>
    static ListT* map_entries(Ty* m, LambdaMEC lmec)
    {
        std::vector<MapEntryT> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [lmec](MEntry<K, V>& v) -> MapEntryT {
            return lmec(v.key, v.value);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename ListT>
    static BSQBool map_has_all(Ty* m, ListT* kl)
    {
        return std::all_of(kl->entries.begin(), kl->entries.end(), [m](K k) -> bool {
            return m->hasKey(k);
        });
    }

    template <typename SetT>
    static BSQBool map_domainincludes(Ty* m, SetT* s)
    {
        return std::all_of(s->entries.begin(), s->entries.end(), [m](K k) -> bool {
            return m->hasKey(k);
        });
    }

    template <typename K_RCIncF, typename V_RCIncF, typename LambdaP>
    static Ty* map_submap(Ty* m, LambdaP p)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [p, &entries](MEntry<K, V>& v) {
            if(p(v.key, v.value))
            {
                entries.emplace_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename RMType, typename RMEntryType, MIRNominalTypeEnum ntype, typename LambdaTCK, typename LambdaTCV, typename LambdaCC>
    static RMType* map_oftype(Ty* m, LambdaTCK tck, LambdaTCV tcv, LambdaCC cc)
    {
        std::vector<RMEntryType> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [tck, tcv, cc, &entries](MEntry<K, V>& v) {
            if(tck(v.key) && tcv(v.value))
            {
                entries.emplace_back(cc(v.key, v.value));
            }
        });

        return BSQ_NEW_NO_RC(RMType, ntype, move(entries));
    }

    template <typename RMType, typename RMEntryType, MIRNominalTypeEnum ntype, typename LambdaTCK, typename LambdaTCV, typename LambdaCC>
    static RMType* map_cast(Ty* m, LambdaTCK tck, LambdaTCV tcv, LambdaCC cc)
    {
        std::vector<RMEntryType> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [tck, tcv, cc, &entries](MEntry<K, V>& v) {
            BSQ_ASSERT(tck(v.key) && tcv(v.value), "abort -- invalid element in cast in Map<K, V>::cast");

            entries.emplace_back(cc(v.key, v.value));
        });

        return BSQ_NEW_NO_RC(RMType, ntype, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_projectall(Ty* m, ListT* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(dl->entries.begin(), dl->entries.end(), [&entries, m](K k) {
            V vv;
            if(m->tryGetValue(k, &vv))
            {
                entries.emplace_back(MEntry<K, V>{K_RCIncF{}(k), V_RCIncF{}(vv)});
            }
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V, K_CMP>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_excludeall(Ty* m, ListT* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::set<K, K_CMP> es(dl->entries.begin(), dl->entries.end());
        std::for_each(m->entries.begin(), m->entries.end(), [&entries, &es](MEntry<K, V>& e) {
            bool has = es.find(e.key) != es.end();
            if(!has)
            {
                entries.emplace_back(MEntry<K, V>{K_RCIncF{}(e.key), V_RCIncF{}(e.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename SetT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_project(Ty* m, SetT* ds)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(ds->entries.begin(), ds->entries.end(), [&entries, m](K k) {
            V vv;
            if(m->tryGetValue(k, &vv))
            {
                entries.emplace_back(MEntry<K, V>{K_RCIncF{}(k), V_RCIncF{}(vv)});
            }
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V, K_CMP>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename SetT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_exclude(Ty* m, SetT* ds)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(m->entries.begin(), m->entries.end(), [&entries, ds](MEntry<K, V>& e) {
            bool has = ds->has(e.key);
            if(!has)
            {
                entries.emplace_back(MEntry<K, V>{K_RCIncF{}(e.key), V_RCIncF{}(e.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename MapT, typename U, MIRNominalTypeEnum ntype, typename K_RCInc, typename LambdaF>
    static MapT* map_remap(Ty* m, LambdaF f)
    {
        std::vector<MEntry<K, U>> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [f](MEntry<K, V>& v) -> MEntry<K, U> {
            return MEntry<K, U>{K_RCInc{}(v.key), f(v.key, v.value)};
        });

        return BSQ_NEW_NO_RC(MapT, ntype, move(entries));
    }

    template <typename MapT, typename U, typename U_RCInc, MIRNominalTypeEnum ntype, typename K_RCInc, typename MapU>
    static MapT* map_compose(Ty* m1, MapU* m2)
    {
        std::vector<MEntry<K, U>> entries;
        entries.reserve(m1->entries.size());

        std::transform(m1->entries.begin(), m1->entries.end(), std::back_inserter(entries), [m2](MEntry<K, V>& v) -> MEntry<K, U> {
            U uu;
            bool ok = m2->tryGetValue(v.value, &uu);
            BSQ_ASSERT(ok, "abort -- missing Key for Map<K, V>::compose");

            return MEntry<K, U>{K_RCInc{}(v.key), U_RCInc{}(uu)};
        });

        return BSQ_NEW_NO_RC(MapT, ntype, move(entries));
    }

    template <typename MapT, typename U, typename MU, MIRNominalTypeEnum ntype, typename K_RCInc, typename MapU, typename UConvF>
    static MapT* map_trycompose(Ty* m1, MapU* m2, MU unone, UConvF uc)
    {
        std::vector<MEntry<K, MU>> entries;
        
        std::transform(m1->entries.begin(), m1->entries.end(), std::back_inserter(entries), [m2, uc, unone](MEntry<K, V>& v) -> MEntry<K, MU> {
            U uu;
            if(m2->tryGetValue(v.value, &uu))
            {
                return MEntry<K, MU>{K_RCInc{}(v.key), uc(uu)};
            }
            else
            {
                return MEntry<K, MU>{K_RCInc{}(v.key), unone};
            }
        });

        return BSQ_NEW_NO_RC(MapT, ntype, move(entries));
    }

    template <typename MapT, typename U, typename U_RCInc, MIRNominalTypeEnum ntype, typename K_RCInc, typename MapU>
    static MapT* map_defaultcompose(Ty* m1, MapU* m2, U dflt)
    {
        std::vector<MEntry<K, U>> entries;
        entries.reserve(m1->entries.size());

        std::transform(m1->entries.begin(), m1->entries.end(), std::back_inserter(entries), [m2, dflt](MEntry<K, V>& v) -> MEntry<K, U> {
            U uu;
            if(m2->tryGetValue(v.value, &uu))
            {
                return MEntry<K, U>{K_RCInc{}(v.key), U_RCInc{}(uu)};
            }
            else
            {
                return MEntry<K, U>{K_RCInc{}(v.key), U_RCInc{}(dflt)};
            }
        });

        return BSQ_NEW_NO_RC(MapT, ntype, move(entries));
    }

    template <typename MapT, MIRNominalTypeEnum ntype, typename K_RCInc, typename V_RCInc, typename V_CMP, typename V_EQ>
    static MapT* map_injinvert(Ty* m)
    {
        std::vector<MEntry<V, K>> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> MEntry<V, K> {
            return MEntry<V, K>{V_RCInc{}(v.value), K_RCInc{}(v.key)};
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<V, K, V_CMP>{});
        auto dup = std::adjacent_find(entries.begin(), entries.end(), MEntryEQ<V, K, V_EQ>{});
        BSQ_ASSERT(dup == entries.end(), "abort -- cannot injectively invert map with duplicate values");

        return BSQ_NEW_NO_RC(MapT, ntype, move(entries));
    }

    template <typename ListT, MIRNominalTypeEnum lntype, typename MapT, MIRNominalTypeEnum mntype, typename K_RCInc, typename V_RCInc, typename V_CMP>
    static MapT* map_relinvert(Ty* m)
    {
        std::map<V, std::vector<K>, V_CMP> partitions;
        std::for_each(m->entries.begin(), m->entries.end(), [&partitions](MEntry<K, V>& entry) {
            auto pp = partitions.find(entry.value);

            if(pp != partitions.end())
            {
                pp->second.emplace_back(K_RCInc{}(entry.key));
            }
            else 
            {
                partitions.emplace(V_RCInc{}(entry.value), std::vector<K>{K_RCInc{}(entry.key)});
            }
        });

        std::vector<MEntry<V, ListT*>> mentries;
        std::transform(partitions.begin(), partitions.end(), std::back_inserter(mentries), [](std::pair<V, std::vector<K>>&& me) -> MEntry<V, ListT*> {
            auto le = BSQ_NEW_NO_RC(ListT, lntype, std::move(me.second));
            return MEntry<V, ListT*>{me.first, INC_REF_DIRECT(ListT, le)};
        });

        return BSQ_NEW_NO_RC(MapT, mntype, move(mentries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_union(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.begin()), [](const MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](const MEntry<K, V>& e) {
            BSQ_ASSERT(rm.find(e.key) == rm.end(), "abort -- cannot have duplicate keys in Map<K, V>::union");

            rm.insert(std::make_pair(e.key, e.value));
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm.begin(), rm.end(), std::back_inserter(entries), [](const std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>{K_RCIncF{}(e.first), V_RCIncF{}(e.second)};
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, MIRNominalTypeEnum ntype, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_unionall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::for_each(maps.begin(), maps.end(), [&rm](Ty* om) {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](const MEntry<K, V>& e) {
                BSQ_ASSERT(rm.find(e.key) == rm.end(), "abort -- cannot have duplicate keys in Map<K, V>::unionAll");

                rm.insert(std::make_pair(e.key, e.value));
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm.begin(), rm.end(), std::back_inserter(entries), [](const std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>{K_RCIncF{}(e.first), V_RCIncF{}(e.second)};
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_merge(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.begin()), [](const MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](const MEntry<K, V>& e) {
            rm[e.key] = e.value;
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm.begin(), rm.end(), std::back_inserter(entries), [](const std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>{K_RCIncF{}(e.first), V_RCIncF{}(e.second)};
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, MIRNominalTypeEnum ntype, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_mergeall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::for_each(maps.begin(), maps.end(), [&rm](Ty* om) {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](const MEntry<K, V>& e) {
                rm[e.key] = e.value;
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm.begin(), rm.end(), std::back_inserter(entries), [](const std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>{K_RCIncF{}(e.first), V_RCIncF{}(e.second)};
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }
};
}
