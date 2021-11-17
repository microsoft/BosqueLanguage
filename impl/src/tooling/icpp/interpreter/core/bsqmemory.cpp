//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

GCStackEntry GCStack::frames[BSQ_MAX_STACK];
uint32_t GCStack::stackp = 0;

void BumpSpaceAllocator::ensureSpace_slow()
{
    Allocator::GlobalAllocator.collect();
}

Allocator Allocator::GlobalAllocator;
