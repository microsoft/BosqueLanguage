//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "../bsqvalue.h"
#include "bsqlist_decl.h"

#pragma once

namespace BSQ
{
template <typename T, typename RCDecF, typename DisplayF, typename T_CMP, typename T_EQ>
class BSQSet : public BSQObject 
{
public:
    std::vector<T> entries;

    template <typename T_INC>
    inline static std::vector<T> processSingletonSetInit(std::vector<T> src)
    {
        std::stable_sort(src.begin(), src.end(), T_CMP{});
        auto end = std::unique(src.begin(), src.end(), T_EQ{});

        std::vector<T> res;
        res.reserve(std::distance(src.begin(), end));
        std::transform(src.begin(), end, back_inserter(res), T_INC{});

        return res;
    }

    BSQSet(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQSet(MIRNominalTypeEnum ntype, std::vector<T>&& entries) : BSQObject(ntype), entries(entries) { ; }

    virtual ~BSQSet()
    {
        ;
    }

    virtual void destroy()
    {
        std::for_each(this->entries.begin(), this->entries.end(), [](T& v) {
            RCDecF{}(v);
        });
    }

    virtual std::string display() const
    {
        std::string ss("{");
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ss += ", ";
            }
            first = false;

            ss += DisplayF{}(*iter);
        }
        ss += "}";

        return ss;
    }
};

}
