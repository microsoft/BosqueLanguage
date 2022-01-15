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

//Forward Decl
class Evaluator;

class BSQListOps
{
public:
    static std::map<BSQTypeID, BSQListTypeFlavor> g_flavormap; //map from entry type to the flavors of the repr

    static void* list_append(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* lnode, BSQCollectionGCReprNode* rnode)
    {
        if(lnode == nullptr & rnode == nullptr)
        {
            return nullptr;
        }
        else if(lnode == nullptr)
        {
            return rnode->repr;
        }
        else if(rnode == nullptr)
        {
            return lnode->repr;
        }
        else
        {
            auto ltype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(lnode->repr));
            auto rtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(rnode->repr));

            Allocator::GlobalAllocator.ensureSpace(sizeof(GC_META_DATA_WORD) + std::max(lflavor.pv8type->allocinfo.heapsize, sizeof(BSQListTreeRepr)));

            auto lrepr = lnode->repr;
            auto rrepr = rnode->repr;
            if((ltype->lkind != ListReprKind::TreeElement) & (rtype->lkind != ListReprKind::TreeElement))
            {
                auto count = BSQPartialVectorType::getPVCount(lrepr) + BSQPartialVectorType::getPVCount(rrepr);

                void* res = nullptr;
                if(count <= 4)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv4type);
                    BSQPartialVectorType::appendPVData(res, lrepr, lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, rrepr, lflavor.entrytype->allocinfo.inlinedatasize);
                } 
                else if(count <= 8)
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.pv8type);
                    BSQPartialVectorType::appendPVData(res, lrepr, lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, rrepr, lflavor.entrytype->allocinfo.inlinedatasize);
                }
                else
                {
                    res = Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                    ((BSQListTreeRepr*)res)->l = lrepr;
                    ((BSQListTreeRepr*)res)->r = rrepr;
                    ((BSQListTreeRepr*)res)->size = count;
                }

                return res;
            }
            else
            {
                BSQListTreeRepr* res = (BSQListTreeRepr*)Allocator::GlobalAllocator.allocateSafe(lflavor.treetype);
                res->l = lrepr;
                res->r = rrepr;
                res->size = ltype->getCount(lrepr) + rtype->getCount(rrepr);

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

            return BSQListOps::list_append(lflavor, llres, rrres);
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

            return BSQListOps::list_append(lflavor, llres, rrres);
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
            }
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv8type->get(res, i), lelems->root);
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

            res = BSQListOps::list_append(lflavor, llres, rrres);
        }
        return res;
    }

    template <typename T>
    static std::pair<void*, T> s_range_ne_rec(const BSQListTypeFlavor& lflavor, T start, BSQNat count)
    {
        void* res = nullptr;
        StorageLocationPtr max = nullptr;
        if(count <= 4)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv4type->get(res, i), start + (T)i);
            }
            max = start + (int16_t)count;
        }
        else if(count <= 8)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
            BSQPartialVectorType::setPVCount(res, (int16_t)count);
            for(int16_t i = 0; i < (int16_t)count; ++i)
            {
                lflavor.entrytype->storeValue(lflavor.pv8type->get(res, i), start + (T)i);
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

            res = BSQListOps::list_append(lflavor, llres, rrres);
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

            res = BSQListOps::list_append(lflavor, llres, rrres);
        }
        return res;
    }

    static void* s_slice_start(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* tnode, const BSQListReprType* ttype, BSQNat start) 
    {
        if(start == 0)
        {
            return tnode->repr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            auto count = BSQPartialVectorType::getPVCount(tnode->repr);

            void* res = Allocator::GlobalAllocator.allocateDynamic(((count - start) <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, tnode->repr, start, (uint64_t)count - start, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = LIST_LOAD_TYPE_INFO_REPR(static_cast<BSQListTreeRepr*>(tnode->repr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(tnode->repr)->l);

            if(start < llcount)
            {
                auto gclpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
                auto llnode = BSQListOps::s_slice_start(lflavor, Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->l), lltype, start);
                auto llres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gclpoint, llnode);
 
                auto rrres = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->r);

                res = BSQListOps::list_append(lflavor, llres, rrres);
            }
            else
            {
                auto rrtype = LIST_LOAD_TYPE_INFO_REPR(static_cast<BSQListTreeRepr*>(tnode->repr)->r);

                auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
                res = BSQListOps::s_slice_start(lflavor, Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->r), rrtype, start - llcount);
                Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint);
            }
        }
        return res;
    }

    static void* s_slice_end(const BSQListTypeFlavor& lflavor, BSQCollectionGCReprNode* tnode, const BSQListReprType* ttype, BSQNat end) 
    {
        if(end == ttype->getCount(tnode->repr))
        {
            return tnode->repr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            auto count = BSQPartialVectorType::getPVCount(tnode->repr);

            void* res = Allocator::GlobalAllocator.allocateDynamic((end <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, tnode->repr, 0, end, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = LIST_LOAD_TYPE_INFO_REPR(static_cast<BSQListTreeRepr*>(tnode->repr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(tnode->repr)->l);

            auto rrtype = LIST_LOAD_TYPE_INFO_REPR(static_cast<BSQListTreeRepr*>(tnode->repr)->r);

            if(end > llcount)
            {
                auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
                auto rrnode = BSQListOps::s_slice_end(lflavor, Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->r), rrtype, end - llcount);
                auto rrres = Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint, rrnode);
 
                auto llres = Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->l);

                res = BSQListOps::list_append(lflavor, llres, rrres);
            }
            else
            {
                auto gcrpoint = Allocator::GlobalAllocator.getCollectionNodeCurrentEnd();
                res = BSQListOps::s_slice_end(lflavor, Allocator::GlobalAllocator.registerCollectionNode(static_cast<BSQListTreeRepr*>(tnode->repr)->l), lltype, end);
                Allocator::GlobalAllocator.resetCollectionNodeEnd(gcrpoint);
            }
        }
        return res;
    }

    static void s_safe_get(void* t, const BSQListReprType* ttype, BSQNat idx, const BSQType* oftype, StorageLocationPtr res) 
    {
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            oftype->storeValue(dynamic_cast<const BSQPartialVectorType*>(ttype)->get(res, idx), res);
        }
        else
        {
            auto trepr = static_cast<BSQListTreeRepr*>(t);
            auto ll = trepr->l;
            auto lltype = LIST_LOAD_TYPE_INFO_REPR(ll);
            auto llcount = lltype->getCount(ll);

            if(idx < llcount)
            {
                return BSQListOps::s_safe_get(ll, lltype, idx, oftype, res);
            }
            else
            {
                return BSQListOps::s_safe_get(trepr->r, LIST_LOAD_TYPE_INFO_REPR(trepr->r), idx - llcount, oftype, res);
            }
        }
    }

    static BSQNat s_size_ne(StorageLocationPtr sl)   
    {
        return LIST_LOAD_TYPE_INFO_REPR(sl)->getCount(LIST_LOAD_DATA(sl));
    }

    static void s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res);
    static void s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res);

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

    static void* s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQType* etype, StorageLocationPtr eres);
    static void* s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQType* etype, StorageLocationPtr eres);

    static void* s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params);
    static void* s_unique_from_sorted_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* eq, const std::vector<StorageLocationPtr>& params);
};

