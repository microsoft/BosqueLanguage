//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

GCStackEntry GCStack::frames[2048];
uint32_t GCStack::stackp = 0;

template <size_t bsize>
void GCRefList<bsize>::enqueSlow(void* v)
{
    void** tmp = (void**)mi_zalloc_small(bsize * sizeof(void*));
    this->tailrl[0] = tmp;
    this->tailrl = tmp;
    this->epos = 1;
}

template <size_t bsize>
void* GCRefList<bsize>::dequeSlow()
{
    void** tmp  this->headrl;
    
    this->headrl = this->headrl[0];
    this->spos = 2;

    mi_free(tmp);
    return this->headrl[1];
}

template <size_t bsize>
void GCRefList<bsize>::iterAdvanceSlow(GCRefListIterator<bsize>& iter) const
{
    iter.crl = iter.crl[0];
    iter.cpos = 1;
}

uint8_t* NewSpaceAllocator::allocateDynamicSizeSlow(size_t rsize)
{
    if((rsize <= BSQ_ALLOC_MAX_BLOCK_SIZE))
    {
        //Note this is technically UB!!!!
        MEM_STATS_OP(this->totalbumpalloc += (this->m_currPos - this->m_block));

        Allocator::GlobalAllocator.collect();

        uint8_t* res = this->m_currPos;
        this->m_currPos += rsize;

        return res;
    }
    else
    {
        MEM_STATS_OP(this->totalbigalloc += rsize);

        void* res = BSQ_FREE_LIST_ALLOC(rsize);
        this->m_bigallocs.enque(res);
        this->m_bigallocsCount++;

        return (uint8_t*)res;
    }
}

void NewSpaceAllocator::ensureSpace_slow()
{
    Allocator::GlobalAllocator.collect();
}


Allocator Allocator::GlobalAllocator;
