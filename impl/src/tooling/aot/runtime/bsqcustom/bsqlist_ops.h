//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqlist_decl.h"

namespace BSQ
{
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