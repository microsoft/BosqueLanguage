//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqtype.h"

template <>
GCProcessOperatorFP BSQType::getProcessFP<true>() const
{
    return this->fpProcessObjRoot;
}

template <>
inline GCProcessOperatorFP BSQType::getProcessFP<false>() const
{
    return this->fpProcessObjHeap;
}
