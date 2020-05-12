//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "../bsqvalue.h"
#include "bsqlist_decl.h"
#include "bsqset_decl.h"

#pragma once

namespace BSQ
{
template <typename K, typename V>
struct MEntry 
{
    K key;
    V value;
};

template <typename K, typename V, typename K_CMP>
struct MEntryCMP 
{
    bool operator()(const MEntry<K, V>& e1, const MEntry<K, V>& e2)
    {
        return K_CMP{}(e1.key, e2.key);
    } 
};

template <typename K, typename V, typename K_EQ>
struct MEntryEQ 
{
    bool operator()(const MEntry<K, V>& e1, const MEntry<K, V>& e2)
    {
        return K_EQ{}(e1.key, e2.key);
    } 
};

template <typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF>
class BSQMap : public BSQObject 
{
public:
    std::vector<MEntry<K, V>> entries;
    
    template <typename K_INC, typename V_INC>
    inline static std::vector<MEntry<K, V>> processSingletonMapInit(std::vector<std::pair<K, V>> src) {
        std::vector<MEntry<K, V>> res;
        res.reserve(src.size());

        std::transform(src.begin(), src.end(), back_inserter(res), [](const std::pair<K, V>& entry) {
            return MEntry<K, V>(K_INC{}(entry.first), V_INC{}(entry.second));
        });
    
        std::stable_sort(src.begin(), src.end(), MEntryCMP<K, V, K_CMP>{});
        auto dup = std::adjacent_find(src.begin(), src.end(), MEntryEQ<K, V, K_EQ>{});
        BSQ_ASSERT(dup == src.end(), "Duplicate key found in Map initialization");

        return src;
    }

    BSQMap(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQMap(MIRNominalTypeEnum ntype, std::vector<MEntry<K, V>>&& entries) : BSQObject(ntype), entries(entries) { ; }

    virtual ~BSQMap()
    {
        ;
    }

    virtual void destroy()
    {
        std::for_each(this->entries.begin(), this->entries.end(), [](T& e) -> void {
            K_RCDecF{}(e.key);
            V_RCDecF{}(e.value);
        });
    }

    virtual std::string display() const
    {
        std::string ms("{");
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ms += ", ";
            }
            first = false;

            ms += K_Display(iter->key) + " => " + V_Display(iter->value);
        }
        ms += "}";

        return ms;
    }
};

}
