//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmap_decl.h"

#pragma once

namespace BSQ
{
template <typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF>
class BSQMapOps
{
public:
    typedef BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, V, V_RCDecF, V_DisplayF> Ty;

    template <typename K_RCIncF, MIRNominalTypeEnum ntype>
    static BSQList<K, K_RCDecF, K_DisplayF>* map_key_list(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC((BSQList<K, K_RCDecF, K_DisplayF>), ntype, move(entries));
    }

    template <typename K_RCIncF, MIRNominalTypeEnum ntype>
    static BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* map_key_set(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC((BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>), ntype, move(entries));
    }

    template <typename V_RCIncF, MIRNominalTypeEnum ntype>
    static BSQList<V, V_RCDecF, V_DisplayF>* map_values(Ty* m)
    {
        std::vector<V> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return V_RCIncF{}(v.value);
        });

        return BSQ_NEW_NO_RC((BSQList<V, V_RCDecF, V_DisplayF>), ntype, move(entries));
    }

    template <typename ListT, typename MapEntryT, MIRNominalTypeEnum ntype, typename LambdaMEC>
    static ListT* map_entries(Ty* m)
    {
        std::vector<MapEntryT> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> MapEntryT {
            return LambdaMEC{}(v.key, v.value);
        });

        return BSQ_NEW_NO_RC((BSQList<K, K_RCDecF, K_DisplayF>), ntype, move(entries));
    }

    static bool map_has_all(Ty* m, BSQList<K, K_RCDecF, K_DisplayF>* kl)
    {
        return std::all_of(kl->entries.begin(), kl->entries.end(), [m](K& k) -> bool {
            MEntry<K, V> ekey{k};
            return std::binary_search(m->entries.begin(), m->entries.end(), ekey, MEntryCMP<K, V, K_CMP>{});
        });
    }

    static bool map_domainincludes(Ty* m, BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* s)
    {
        return std::all_of(s->entries.begin(), s->entries.end(), [m](K& k) -> bool {
            MEntry<K, V> ekey{k};
            return std::binary_search(m->entries.begin(), m->entries.end(), ekey, MEntryCMP<K, V, K_CMP>{});
        });
    }

    template <typename K_RCIncF, typename V_RCIncF, typename LambdaP>
    static Ty* map_submap(Ty* m)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            if(LambdaP{}(v.key, v.value))
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename T, typename T_RCDecF, typename T_DisplayF, typename T_CMP, typename T_EQ, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>* map_oftype(Ty* m)
    {
        std::vector<MEntry<T, U>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            if(LambdaTC{}(v.key, v.value))
            {
                entries.push_back(LambdaCC{}(v.key, v.value));
            }
        });

        return BSQ_NEW_NO_RC((BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename T, typename T_RCDecF, typename T_DisplayF, typename T_CMP, typename T_EQ, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>* map_cast(Ty* m)
    {
        std::vector<MEntry<T, U>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            BSQ_ASSERT(LambdaTC{}(v.key, v.value), "Invalid element in cast");

            entries.push_back(LambdaCC{}(v.key, v.value));
        });

        return BSQ_NEW_NO_RC((BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF, bool missingok>
    static Ty* map_project(Ty* m, BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* ds)
    {
        std::vector<MEntry<K, V>> entries;

        if(missingok)
        {
            std::for_each(ds->entries.begin(), ds->entries.end(), [&entries](K& k) -> void {
                MEntry<K, V> ekey{k};
                auto entry = m->entries.find(ekey);

                if(entry != m->entries.end())
                {
                    entries.push_back(MEntry<K, V>{K_RCIncF{}(entry->key), V_RCIncF{}(entry->value)});
                }
            });
        }
        else
        {
            std::for_each(ds->entries.begin(), ds->entries.end(), [&entries](K& k) -> void {
                MEntry<K, V> ekey{k};
                auto entry = m->entries.find(ekey);
                BSQ_ASSERT(entry != m->entries.end(), "Missing key in domain");
                
                entries.push_back(MEntry<K, V>{K_RCIncF{}(entry->key), V_RCIncF{}(entry->value)});
            });
        }

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_exclude(Ty* m, BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* ds)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& e) -> void {
            bool has = std::binary_search(ds->entries.begin(), ds->entries.end(), e.key, K_CMP{});
            if(!has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(e->key), V_RCIncF{}(e->value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaF>
    static BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, U, U_RCDecF, U_DisplayF>* map_remap(Ty* m)
    {
        std::vector<MapEntryT> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> MapEntryT {
            return MEntry<K, U>{K_RCIncF{}(v.key), LambdaP{}(v.key, v.value)};
        });

        return BSQ_NEW_NO_RC((BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_projectall(Ty* m, BSQList<K, K_RCDecF, K_DisplayF>* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(dl->entries.begin(), dl->entries.end(), [&entries](K& k) -> void {
            MEntry<K, V> ekey{k};
            auto entry = m->entries.find(ekey);
            BSQ_ASSERT(entry != m->entries.end(), "Missing key in domain");
                
            entries.push_back(MEntry<K, V>{K_RCIncF{}(entry->key), V_RCIncF{}(entry->value)});
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_excludeall(Ty* m, BSQList<K, K_RCDecF, K_DisplayF>* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::set<K, K_CMP> es(dl.begin(), dl.end());
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& e) -> void {
            bool has = es.find(e.key) != es.end();
            if(!has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(e->key), V_RCIncF{}(e->value)});
            }
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_union(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> std::pair<K, V> {
            rm.insert(e.key, e.value);
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_unionall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::transform(maps.begin()->entries.begin(), maps.begin()->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(maps.begin() + 1, maps.end(), [&rm](Ty* om) -> void {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> void {
                rm.insert(e.key, e.value);
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_merge(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> std::pair<K, V> {
            BSQ_ASSERT(rm.find(e.key) == rm.end(), "Cannot have duplicate keys");

            rm.insert(e.key, e.value);
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_mergeall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::transform(maps.begin()->entries.begin(), maps.begin()->entries.end(), std::inserter(rm, rm.begin()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(maps.begin() + 1, maps.end(), [&rm](Ty* om) -> void {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> void {
                BSQ_ASSERT(rm.find(e.key) == rm.end(), "Cannot have duplicate keys");

                rm.insert(e.key, e.value);
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }
};
}
