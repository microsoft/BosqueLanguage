//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

namespace BSQ
{
    GCStackEntry GCStack::frames[8192];
    uint32_t GCStack::stackp = 0;

    void GCOperator::collect()
    {
        this->alloc->collect();
    }

    Allocator Allocator::GlobalAllocator;
}
