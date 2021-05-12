//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

GCStackEntry GCStack::frames[8192];
uint32_t GCStack::stackp = 0;

uint8_t* NewSpaceAllocator::allocateBumpSlow(size_t rsize)
{
    //Note this is technically UB!!!!
    MEM_STATS_OP(this->totalalloc += (this->m_currPos - this->m_block));

    Allocator::GlobalAllocator.collect();

    uint8_t* res = this->m_currPos;
    this->m_currPos += rsize;

    return res;
}

void ensureSpace_slow()
{
    Allocator::GlobalAllocator.collect();
}

Allocator Allocator::GlobalAllocator;
