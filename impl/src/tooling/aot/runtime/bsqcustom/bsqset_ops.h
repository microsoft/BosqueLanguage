//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqset_decl.h"

#pragma once

namespace BSQ
{
template <typename Ty, typename T, typename RCDecF, typename DisplayF, typename T_CMP, typename T_EQ>
class BSQSetOps
{
public:
    template <typename RCIncF, MIRNominalTypeEnum ntype>
    static BSQList<T, RCDecF, DisplayF>* set_entry_list(Ty* s)
    {
        std::vector<T> entries;
        entries.reserve(s->entries.size());

        std::transform(s->entries.begin(), s->entries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<T, RCDecF, DisplayF>), ntype, move(entries));
    }

    static bool set_hasall(Ty* s, BSQList<T, RCDecF, DisplayF>* l)
    {
        return std::all_of(l->entries.begin(), l->entries.end(), [s](const T& v) -> bool {
            return std::binary_search(s->entries.begin(), s->entries.end(), v, T_CMP{});
        });
    }
    
    static bool set_subsetof(Ty* s, Ty* os)
    {
        if(s->entries.size() > os->entries.size())
        {
            return false;
        }

        return std::all_of(s->entries.begin(), s->entries.end(), [s, os](const T& v) -> bool {
            return std::binary_search(os->entries.begin(), os->entries.end(), v, T_CMP{}); 
        });
    }

    static bool set_equal(Ty* s, Ty* os)
    {
        if(s->entries.size() != os->entries.size())
        {
            return false;
        }

        return std::equal(s->entries.begin(), s->entries.end(), os->entries.begin(), os->entries.end(), T_EQ{});
    }

    static bool set_disjoint(Ty* s, Ty* os)
    {
        if(s->entries.size() == 0 || os->entries.size() == 0)
        {
            return true;
        }

        return std::none_of(s->entries.begin(), s->entries.end(), [s, os](const T& v) -> bool {
            return std::binary_search(os->entries.begin(), os->entries.end(), v, T_CMP{});  
        });
    }

    template <typename RCIncF, typename LambdaP>
    static Ty* set_subset(Ty* s)
    {
        std::vector<T> entries;
        std::for_each(s->entries.begin(), s->entries.end(), [&entries](const T& v) {
            if(LambdaP{}(v))
            {
                return entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, s->nominalType, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, typename U_CMP, typename U_EQ, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQSet<U, U_RCDecF, U_DisplayF, U_CMP, U_EQ>* set_oftype(Ty* s)
    {
        std::vector<U> entries;
        std::for_each(s->entries.begin(), s->entries.end(), [&entries](T& v) {
            if(LambdaTC{}(v))
            {
                entries.push_back(LambdaCC{}(v));
            }
        });

        return BSQ_NEW_NO_RC((BSQSet<U, U_RCDecF, U_DisplayF, U_CMP, U_EQ>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, typename U_CMP, typename U_EQ, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQSet<U, U_RCDecF, U_DisplayF, U_CMP, U_EQ>* set_cast(Ty* s)
    {
        std::vector<U> entries;
        std::for_each(s->entries.begin(), s->entries.end(), [&entries](T& v) {
            BSQ_ASSERT(LambdaTC{}(v), "Invalid element to cast");

            entries.push_back(LambdaCC{}(v));
        });

        return BSQ_NEW_NO_RC((BSQSet<U, U_RCDecF, U_DisplayF, U_CMP, U_EQ>), ntype, move(entries));
    }

    template <typename RCIncF>
    static Ty* set_union(Ty* s, Ty* os)
    {
        std::vector<T> entries;
        std::set_union(s->entries.begin(), s->entries.end(), os->entries.begin(), os->entries.end(), std::back_inserter(entries), T_CMP{});

        //TODO: probably want to write our own union and integrate RC action in loop later
        std::for_each(s->entries.begin(), s->entries.end(), [](T& v) {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, s->nominalType, move(entries));
    }

    template <typename RCIncF>
    static Ty* set_intersect(Ty* s, Ty* os)
    {
        std::vector<T> entries;
        std::set_intersection(s->entries.begin(), s->entries.end(), os->entries.begin(), os->entries.end(), std::back_inserter(entries), T_CMP{});

        //TODO: probably want to write our own union and integrate RC action in loop later
        std::for_each(s->entries.begin(), s->entries.end(), [](T& v) {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, s->nominalType, move(entries));
    }

    template <typename RCIncF>
    static Ty* set_difference(Ty* s, Ty* os)
    {
        std::vector<T> entries;
        std::set_difference(s->entries.begin(), s->entries.end(), os->entries.begin(), os->entries.end(), std::back_inserter(entries), T_CMP{});

        //TODO: probably want to write our own union and integrate RC action in loop later
        std::for_each(s->entries.begin(), s->entries.end(), [](T& v) {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, s->nominalType, move(entries));
    }

    template <typename RCIncF>
    static Ty* set_symmetricdifference(Ty* s, Ty* os)
    {
        std::vector<T> entries;
        std::set_symmetric_difference(s->entries.begin(), s->entries.end(), os->entries.begin(), os->entries.end(), std::back_inserter(entries), T_CMP{});

        //TODO: probably want to write our own union and integrate RC action in loop later
        std::for_each(s->entries.begin(), s->entries.end(), [](T& v) {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, s->nominalType, move(entries));
    }

    template <typename RCIncF, typename ListT, MIRNominalTypeEnum ntype>
    static Ty* set_unionall(ListT* sl)
    {
        std::set<T, T_CMP> sentries(sl->entries[0]->entries.begin(), sl->entries[0]->entries.end());
        std::for_each(sl->entries.begin() + 1, sl->entries.end(), [&sentries](Ty* s) {
            sentries.insert(s->entries.begin(), s->entries.end());
        });

        std::vector<T> entries;
        entries.reserve(sentries.size());

        std::transform(sentries.begin(), sentries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }

    template <typename RCIncF, MIRNominalTypeEnum ntype, typename LL_RCDecF, typename LL_DisplayF>
    static Ty* set_intersectall(BSQList<Ty*, LL_RCDecF, LL_DisplayF>* sl)
    {
        std::set<T, T_CMP> sentries(sl->entries[0]->entries.begin(), sl->entries[0]->entries.end());
        std::for_each(sl->entries.begin() + 1, sl->entries.end(), [&sentries](Ty* s) {
            sentries.insert(s->entries.begin(), s->entries.end());
        });

        std::vector<T> entries;
        entries.reserve(sentries.size());

        std::transform(sentries.begin(), sentries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }
};

}
