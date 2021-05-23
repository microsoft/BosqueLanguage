//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

GCStackEntry GCStack::frames[2048];
uint32_t GCStack::stackp = 0;

uint8_t* NewSpaceAllocator::allocateDynamicSizeSlow(size_t rsize)
{
    if((rsize <= BSQ_ALLOC_MAX_BLOCK_SIZE))
    {
        //Note this is technically UB!!!!
        MEM_STATS_OP(this->totalalloc += (this->m_currPos - this->m_block));

        Allocator::GlobalAllocator.collect();

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
    else
    {
        void* res = BSQ_FREE_LIST_ALLOC(rsize);
        this->m_bigallocs.push_back(res);

        return (uint8_t*)res;
    }
}

void NewSpaceAllocator::ensureSpace_slow()
{
    Allocator::GlobalAllocator.collect();
}

Allocator Allocator::GlobalAllocator;
