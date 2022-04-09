//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "runtime/bsqop.h"
#include "runtime/bsqinvoke.h"

#include "runtime/bsqvalue.h"
#include "runtime/bsqlist.h"
#include "runtime/bsqmap.h"

//Forward Decl
class Evaluator;

class BSQListOps
{
public:
    static std::map<BSQTypeID, BSQListTypeFlavor> g_flavormap; //map from entry type to the flavors of the repr

    inline static void* list_consk(const BSQListTypeFlavor& lflavor, const std::vector<StorageLocationPtr>& params)
    {
        Allocator::GlobalAllocator.ensureSpace(sizeof(GC_META_DATA_WORD) + lflavor.pv8type->allocinfo.heapsize);

        auto res = Allocator::GlobalAllocator.allocateSafe((params.size() <= 4) ? lflavor.pv4type : lflavor.pv8type);
        BSQPartialVectorType::initializePVData(res, params, lflavor.entrytype);

        return res;
    }

    static void* list_cons(const BSQListTypeFlavor& lflavor, const std::vector<StorageLocationPtr>& params)
    {
        if(params.size() <= 8)
        {
            return list_consk(lflavor, params);
        }
        else
        {
            assert(false);
            return nullptr;
        }
    }

    static void* list_append(const BSQListTypeFlavor& lflavor, void* l, void* r)
    {
        if(l == nullptr & r == nullptr)
        {
            return nullptr;
        }
        else if(l == nullptr)
        {
            return r;
        }
        else if(r == nullptr)
        {
            return l;
        }
        else
        {
            auto ltype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(l));
            auto rtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(r));

            if((ltype->lkind != ListReprKind::TreeElement) & (rtype->lkind != ListReprKind::TreeElement))
            {
                auto count = BSQPartialVectorType::getPVCount(l) + BSQPartialVectorType::getPVCount(r);

                void* res = nullptr;
                if(count <= 4)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv4type);
                    BSQPartialVectorType::appendPVData(res, l, lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, r, lflavor.entrytype->allocinfo.inlinedatasize);
                } 
                else if(count <= 8)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv8type);
                    BSQPartialVectorType::appendPVData(res, l, lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, r, lflavor.entrytype->allocinfo.inlinedatasize);
                }
                else
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                    ((BSQListTreeRepr*)res)->l = l;
                    ((BSQListTreeRepr*)res)->r = r;
                    ((BSQListTreeRepr*)res)->size = count;
                }

                return res;
            }
            else
            {
                BSQListTreeRepr* res = (BSQListTreeRepr*)Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                res->l = l;
                res->r = r;
                res->size = ltype->getCount(l) + rtype->getCount(r);

                return res;
            }
        }
    }

    template <typename OP_PV>
    static void* list_tree_transform(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(reprnode, static_cast<const BSQPartialVectorType*>(reprtype));
        }
        else
        {
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto llnode = list_tree_transform(lflavor, lnode, fn_partialvector);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
            auto rrnode = list_tree_transform(lflavor, rnode, fn_partialvector);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
            return BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
        }
    }

    template <typename OP_PV>
    static void* list_tree_transform_idx(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode, uint64_t idx, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode->repr));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(reprnode, static_cast<const BSQPartialVectorType*>(reprtype), idx);
        }
        else
        {
            auto ltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto lsize = ltype->getCount(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);

            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->l);
            auto llnode = list_tree_transform_idx(lflavor, lnode, idx, fn_partialvector);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(reprnode->repr)->r);
            auto rrnode = list_tree_transform_idx(lflavor, rnode, idx + lsize, fn_partialvector);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
            return BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
        }
    }

    static void* s_temp_root_to_list_rec(const BSQListTypeFlavor& lflavor, std::list<BSQTempRootNode>::iterator& lelems, uint64_t count)
    {
        void* res = nullptr;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), lelems->root);
                lelems++;
            }
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv8type->get(res, i), lelems->root);
                lelems++;
            }
        }
        else
        {
            auto mid = count / 2;
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto llnode = BSQListOps::s_temp_root_to_list_rec(lflavor, lelems, mid);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rrnode = BSQListOps::s_temp_root_to_list_rec(lflavor, lelems, count - mid);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
            res = BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
        }
        return res;
    }

    static void s_enumerate_for_extract(const BSQListTypeFlavor& lflavor, void* tn, std::list<StorageLocationPtr>& ll)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(tn));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            auto pvtype = static_cast<const BSQPartialVectorType*>(reprtype);
            for(size_t i = 0; i < BSQPartialVectorType::getPVCount(tn); ++i)
            {
                ll.push_back(pvtype->get(tn, i));
            }
        }
        else
        {
            s_enumerate_for_extract(lflavor, static_cast<BSQListTreeRepr*>(tn)->l, ll);
            s_enumerate_for_extract(lflavor, static_cast<BSQListTreeRepr*>(tn)->r, ll);
        }
    }

    template <typename T>
    static std::pair<void*, T> s_range_ne_rec(const BSQListTypeFlavor& lflavor, T start, BSQNat count)
    {
        void* res = nullptr;
        T max = start;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            T curr = start;
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), &curr);
                curr = curr + (T)1;
            }
            max = start + (int16_t)count;
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            T curr = start;
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv8type->get(res, i), &curr);
                curr = curr + (T)1;
            }
            max = start + (int16_t)count;
        }
        else
        {
            auto llcount = count / 2;
            auto rrcount = count - llcount;

            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto llnode = BSQListOps::s_range_ne_rec(lflavor, start, llcount);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode.first);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rrnode = BSQListOps::s_range_ne_rec(lflavor, llnode.second + (T)1, rrcount);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode.first);

            Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
            res = BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
        }
        return std::make_pair(res, max);
    }

    static void* s_fill_ne_rec(const BSQListTypeFlavor& lflavor, StorageLocationPtr val, BSQNat count)
    {
        void* res = nullptr;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), val);
            }
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv8type->get(res, i), val);
            }
        }
        else
        {
            auto mid = count / 2;
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto llnode = BSQListOps::s_fill_ne_rec(lflavor, val, mid);
            auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);

            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rrnode = BSQListOps::s_fill_ne_rec(lflavor, val, count - mid);
            auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);

            Allocator::GlobalAllocator.ensureSpace(std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD));
            res = BSQListOps::list_append(lflavor, llres->repr, rrres->repr);
        }
        return res;
    }

    static void* s_slice_start(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, const BSQListReprType* ttype, BSQNat start, uint32_t alloc) 
    {
        if(start == 0)
        {
            return iter.lcurr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            Allocator::GlobalAllocator.ensureSpace(alloc + lflavor.pv8type->allocinfo.heapsize + sizeof(GC_META_DATA_WORD));

            auto count = BSQPartialVectorType::getPVCount(iter.lcurr);
            void* res = Allocator::GlobalAllocator.allocateSafe(((count - start) <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, iter.lcurr, start, (uint64_t)count - start, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(iter.lcurr)->l);

            if(start < llcount)
            {
                auto nalloc = alloc + std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD);

                iter.moveLeft();
                auto ll = BSQListOps::s_slice_start(lflavor, iter, lltype, start, nalloc);
                iter.pop();

                res = BSQListOps::list_append(lflavor, ll, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);
            }
            else
            {
                auto rrtype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);

                iter.moveRight();
                res = BSQListOps::s_slice_start(lflavor, iter, rrtype, start - llcount, alloc);
                iter.pop();
            }
        }
        return res;
    }

    static void* s_slice_end(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, const BSQListReprType* ttype, BSQNat end, uint32_t alloc) 
    {
        if(end == ttype->getCount(iter.lcurr))
        {
            return iter.lcurr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            Allocator::GlobalAllocator.ensureSpace(alloc + lflavor.pv8type->allocinfo.heapsize + sizeof(GC_META_DATA_WORD));

            void* res = Allocator::GlobalAllocator.allocateDynamic((end <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, iter.lcurr, 0, end, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(iter.lcurr)->l);

            auto rrtype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);

            if(end > llcount)
            {
                auto nalloc = alloc + std::max(lflavor.pv8type->allocinfo.heapsize, lflavor.treetype->allocinfo.heapsize) + sizeof(GC_META_DATA_WORD);

                iter.moveRight();
                auto rr = BSQListOps::s_slice_end(lflavor, iter, rrtype, end - llcount, nalloc);
                iter.pop();

                res = BSQListOps::list_append(lflavor, static_cast<BSQListTreeRepr*>(iter.lcurr)->l, rr);
            }
            else
            {
                iter.moveRight();
                res = BSQListOps::s_slice_end(lflavor, iter, lltype, end, alloc);
                iter.pop();
            }
        }
        return res;
    }

    static void s_safe_get(void* t, const BSQListReprType* ttype, BSQNat idx, const BSQType* oftype, StorageLocationPtr res) 
    {
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            oftype->storeValue(res, dynamic_cast<const BSQPartialVectorType*>(ttype)->get(t, idx));
        }
        else
        {
            auto trepr = static_cast<BSQListTreeRepr*>(t);
            auto ll = trepr->l;
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, ll);
            auto llcount = lltype->getCount(ll);

            if(idx < llcount)
            {
                return BSQListOps::s_safe_get(ll, lltype, idx, oftype, res);
            }
            else
            {
                return BSQListOps::s_safe_get(trepr->r, GET_TYPE_META_DATA_AS(BSQListReprType, trepr->r), idx - llcount, oftype, res);
            }
        }
    }

    static BSQNat s_size_ne(StorageLocationPtr sl)   
    {
        return LIST_LOAD_TYPE_INFO_REPR(sl)->getCount(LIST_LOAD_DATA(sl));
    }

    static void* s_set_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i, StorageLocationPtr v);
    static void* s_remove_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i);

    static void s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res);
    static void s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res);

    static void* s_reverse_ne(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* reprnode);

    static BSQNat s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQNat s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQNat s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQNat s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);

    static void* s_filter_pred_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static void* s_filter_pred_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);

    static void* s_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);
    static void* s_map_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);
    static void* s_map_sync_ne(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, void* t1, const BSQListReprType* ttype1, void* t2, const BSQListReprType* ttype2, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);

    static void s_reduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res);
    static void s_reduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res);

    static void s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres);
    static void s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres);

    static void* s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params);
    static void* s_unique_from_sorted_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* eq, const std::vector<StorageLocationPtr>& params);

    static BSQString s_strconcat_ne(void* t, const BSQListReprType* ttype);
    static BSQString s_strjoin_ne(void* t, const BSQListReprType* ttype, StorageLocationPtr sep);
};

class BSQMapOps
{
public:
    static std::map<std::pair<BSQTypeID, BSQTypeID>, BSQMapTypeFlavor> g_flavormap; //map from entry type to the flavors of the repr

    static void* map_cons(const BSQMapTypeFlavor& mflavor, const std::vector<StorageLocationPtr>& params)
    {
        if(params.size() == 1)
        {
            void* repr = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            const BSQTupleInfo* tupinfo = dynamic_cast<const BSQTupleInfo*>(mflavor.tupletype);

            mflavor.treetype->initializeLeaf(repr, mflavor.tupletype->indexStorageLocationOffset(params[0], tupinfo->idxoffsets[0]), mflavor.keytype, mflavor.tupletype->indexStorageLocationOffset(params[0], tupinfo->idxoffsets[1]), mflavor.valuetype);
            return repr;
        }
        else
        {
            assert(false);
            return nullptr;
        }
    }

    static void* s_lookup_ne(void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, const BSQType* ktype)
    {
        BSQMapTreeRepr* curr = static_cast<BSQMapTreeRepr*>(t);
        while(curr != nullptr)
        {
            auto ck = ttype->getKeyLocation(curr);
            if(ktype->fpkeycmp(ktype, kl, ck) < 0)
            {
                curr = static_cast<BSQMapTreeRepr*>(curr->l);
            }
            else if(ktype->fpkeycmp(ktype, ck, kl) < 0)
            {
                curr = static_cast<BSQMapTreeRepr*>(curr->r);
            }
            else
            {
                return curr;
            }
        }

        return nullptr;
    }

    template <typename OP_PV>
    static void* map_tree_transform(const BSQMapTypeFlavor& mflavor, BSQCollectionGCReprNode* reprnode, OP_PV fn_node)
    {
        BSQCollectionGCReprNode* llres = nullptr;
        if(BSQMapTreeType::getLeft(reprnode->repr) != nullptr)
        {
            auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto lnode = Allocator::GlobalAllocator.registerCollectionNode(BSQMapTreeType::getLeft(reprnode->repr));
            auto ll = map_tree_transform(mflavor, lnode, fn_node);
            llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, ll);
        }

        BSQCollectionGCReprNode* rrres = nullptr;
        if(BSQMapTreeType::getRight(reprnode->repr) != nullptr)
        {
            auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
            auto rnode = Allocator::GlobalAllocator.registerCollectionNode(BSQMapTreeType::getRight(reprnode->repr));
            auto rr = map_tree_transform(mflavor, rnode, fn_node);
            rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rr);
        }

        return fn_node(reprnode, llres, rrres);
    }

    template <typename OP_PV>
    static void map_tree_flatten(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, OP_PV pred)
    {
        if(BSQMapTreeType::getLeft(iter.lcurr) != nullptr)
        {
            iter.moveLeft();
            map_tree_flatten(mflavor, iter, pred);
            iter.pop();
        }

        if(pred(mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.treetype->getValueLocation(iter.lcurr)))
        {
            auto nn = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLeaf(nn, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype);

            auto root = Allocator::GlobalAllocator.registerTempRoot(mflavor.treetype);
            root->root = nn;
        }

        if(BSQMapTreeType::getRight(iter.lcurr) != nullptr)
        {
            iter.moveRight();
            map_tree_flatten(mflavor, iter, pred);
            iter.pop();
        }
    }

    static void* s_temp_root_to_map_rec(const BSQMapTypeFlavor& mflavor, std::list<BSQTempRootNode>::iterator& lelems, uint64_t count)
    {
        void* res = nullptr;
        if(count == 0)
        {
            ;
        }
        else if(count == 1)
        {
            res = lelems->root;
            lelems++;
        }
        else
        {
            auto mid = count / 2;
            auto llnode = BSQMapOps::s_temp_root_to_map_rec(mflavor, lelems, mid);

            auto rootitem = lelems;
            lelems++;

            auto rrnode = BSQMapOps::s_temp_root_to_map_rec(mflavor, lelems, count - mid);

            static_cast<BSQMapTreeRepr*>(rootitem->root)->l = llnode;
            static_cast<BSQMapTreeRepr*>(rootitem->root)->r = rrnode;
        }
        return res;
    }

    static void s_enumerate_for_extract(const BSQMapTypeFlavor& mflavor, void* tn, std::list<StorageLocationPtr>& ll)
    {
        if(BSQMapTreeType::getLeft(tn) != nullptr)
        {
            s_enumerate_for_extract(mflavor, BSQMapTreeType::getLeft(tn), ll);
        }

        ll.push_back(mflavor.treetype->getKeyLocation(tn));

        if(BSQMapTreeType::getRight(tn) != nullptr)
        {
            s_enumerate_for_extract(mflavor, BSQMapTreeType::getRight(tn), ll);
        }
    }

    static void* s_union_ne(const BSQMapTypeFlavor& mflavor, void* t1, const BSQMapTreeType* ttype1, void* t2, const BSQMapTreeType* ttype2, uint64_t ccount);

    static std::pair<void*, BSQNat> s_submap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static void* s_remap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQMapTypeFlavor& resflavor);

    static void* s_add_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl);
    static void* s_set_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl);
    static void* s_remove_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl);
};
