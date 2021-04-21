//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"

class BSQListEntityType : public BSQSpecialEntityType
{
public:
    virtual BSQNat getLength(void* data) const = 0;
};

class BSQListEmptyType : public BSQListEntityType
{
public:
    virtual BSQNat getLength(void* data) const override
    {
        return 0;
    }
};

template <uint16_t k>
struct BSQListFlatContents
{
    uint32_t length;
    uint8_t data[k];
};

template<uint16_t k>
class BSQListFlatType : public BSQListEntityType
{
public:
    virtual BSQNat getLength(void* data) const override
    {
        return ((BSQListFlatContents<k>*)data)->length;
    }
};
