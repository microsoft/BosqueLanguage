//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "../bsqvalue.h"

#pragma once

namespace BSQ
{

template <typename T, typename RCDecF, typename DisplayF>
class BSQList : public BSQObject
{
public:
    std::vector<T> entries;

    BSQList(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQList(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    virtual ~BSQList()
    {
        ;
    }

    virtual void destroy()
    {
        std::for_each(this->entries.begin(), this->entries.end(), [](T& v) -> void {
            RCDecF{}(v);
        });
    }

    virtual std::string display() const
    {
        std::string ls("{");
        for (size_t i = 0; i < this->entries.size(); ++i)
        {
            if (i != 0)
            {
                ls += ", ";
            }
            ls += DisplayF{}(this->entries[i]);
        }
        ls += "}";

        return ls;
    }
};

}
