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
        auto res = Allocator::GlobalAllocator.allocateDynamic((params.size() <= 4) ? lflavor.pv4type : lflavor.pv8type);
        BSQPartialVectorType::initializePVData(res, params, lflavor.entrytype);

        return res;
    }

    static void* list_cons_rec(const BSQListTypeFlavor& lflavor, const std::vector<StorageLocationPtr>& params, size_t idx, size_t count)
    {
        if(count <= 8)
        {
            std::vector<StorageLocationPtr> psub(&params[idx], &params[idx + count]);
            return list_consk(lflavor, psub);
        }
        else
        {
            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);

            size_t lhscount = count / 2;
            size_t rhscount = count - lhscount;

            stck[0] = list_cons_rec(lflavor, params, idx, lhscount);
            stck[1] = list_cons_rec(lflavor, params, idx + lhscount, rhscount);

            void* res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
            ((BSQListTreeRepr*)res)->l = stck[0];
            ((BSQListTreeRepr*)res)->r = stck[1];
            ((BSQListTreeRepr*)res)->lcount = count;

            GCStack::popFrame(sizeof(void*) * 2);
            return res;
        }
    }
    static void* list_cons(const BSQListTypeFlavor& lflavor, const std::vector<StorageLocationPtr>& params)
    {
        if(params.size() <= 8)
        {
            return list_consk(lflavor, params);
        }
        else
        {
            return list_cons_rec(lflavor, params, 0, params.size());
        }
    }

    static void* list_append(const BSQListTypeFlavor& lflavor, void* l, void* r)
    {
        void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);
        stck[0] = l;
        stck[1] = r;

        void* res = nullptr;
        if((l == nullptr) & (r == nullptr))
        {
            res = nullptr;
        }
        else if(l == nullptr)
        {
            res = r;
        }
        else if(r == nullptr)
        {
            res = l;
        }
        else
        {
            auto ltype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(stck[0]));
            auto rtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(stck[1]));

            if((ltype->lkind != ListReprKind::TreeElement) & (rtype->lkind != ListReprKind::TreeElement))
            {
                auto count = BSQPartialVectorType::getPVCount(stck[0]) + BSQPartialVectorType::getPVCount(stck[1]);

                if(count <= 4)
                {
                    res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv4type);
                    BSQPartialVectorType::setPVCount(res, 0);

                    BSQPartialVectorType::appendPVData(res, stck[0], lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, stck[1], lflavor.entrytype->allocinfo.inlinedatasize);
                } 
                else if(count <= 8)
                {
                    res = Allocator::GlobalAllocator.allocateDynamic(lflavor.pv8type);
                    BSQPartialVectorType::setPVCount(res, 0);
                    
                    BSQPartialVectorType::appendPVData(res, stck[0], lflavor.entrytype->allocinfo.inlinedatasize);
                    BSQPartialVectorType::appendPVData(res, stck[1], lflavor.entrytype->allocinfo.inlinedatasize);
                }
                else
                {
                    res = Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
                    ((BSQListTreeRepr*)res)->l = stck[0];
                    ((BSQListTreeRepr*)res)->r = stck[1];
                    ((BSQListTreeRepr*)res)->lcount = count;
                }

            }
            else
            {
                res = (BSQListTreeRepr*)Allocator::GlobalAllocator.allocateDynamic(lflavor.treetype);
                ((BSQListTreeRepr*)res)->l = stck[0];
                ((BSQListTreeRepr*)res)->r = stck[1];
                ((BSQListTreeRepr*)res)->lcount = ltype->getCount(stck[0]) + rtype->getCount(stck[1]);
            }
        }

        GCStack::popFrame(sizeof(void*) * 2);
        return res;
    }

    template <typename OP_PV>
    static void* list_tree_transform(const BSQListTypeFlavor& lflavor, void* reprnode, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(reprnode, static_cast<const BSQPartialVectorType*>(reprtype));
        }
        else
        {
            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 3);
            stck[0] = reprnode;
        
            stck[1] = list_tree_transform(lflavor, static_cast<BSQListTreeRepr*>(stck[0])->l, fn_partialvector);
            stck[2] = list_tree_transform(lflavor, static_cast<BSQListTreeRepr*>(stck[0])->r, fn_partialvector);
            
            void* res = BSQListOps::list_append(lflavor, stck[1], stck[2]);

            GCStack::popFrame(sizeof(void*) * 3);
            return res;
        }
    }

    template <typename OP_PV>
    static void* list_tree_transform_idx(const BSQListTypeFlavor& lflavor, void* reprnode, uint64_t idx, OP_PV fn_partialvector)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(reprnode));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            return fn_partialvector(reprnode, static_cast<const BSQPartialVectorType*>(reprtype), idx);
        }
        else
        {
            auto ltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(reprnode)->l);
            auto lsize = ltype->getCount(static_cast<BSQListTreeRepr*>(reprnode)->l);

            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 3);
            stck[0] = reprnode;
        
            stck[1] = list_tree_transform_idx(lflavor, static_cast<BSQListTreeRepr*>(stck[0])->l, idx, fn_partialvector);
            stck[2] = list_tree_transform_idx(lflavor, static_cast<BSQListTreeRepr*>(stck[0])->r, idx + lsize, fn_partialvector);
            
            void* res = BSQListOps::list_append(lflavor, stck[1], stck[2]);

            GCStack::popFrame(sizeof(void*) * 3);
            return res;
        }
    }

    static void s_enumerate_for_extract(const BSQListTypeFlavor& lflavor, void* tn, std::list<StorageLocationPtr>& ll)
    {
        auto reprtype = static_cast<const BSQListReprType*>(GET_TYPE_META_DATA(tn));
        if(reprtype->lkind != ListReprKind::TreeElement)
        {
            auto pvtype = static_cast<const BSQPartialVectorType*>(reprtype);
            for(int16_t i = 0; i < BSQPartialVectorType::getPVCount(tn); ++i)
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
    static void* s_range_ne_rec(const BSQListTypeFlavor& lflavor, T start, T count)
    {
        void* res = nullptr;
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
        }
        else
        {
            auto llcount = count / 2;
            auto rrcount = count - llcount;

            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);
            
            stck[0] = BSQListOps::s_range_ne_rec(lflavor, start, llcount);
            stck[1] = BSQListOps::s_range_ne_rec(lflavor, start + llcount, rrcount);
            
            res = BSQListOps::list_append(lflavor, stck[0], stck[1]);

            GCStack::popFrame(sizeof(void*) * 2);
        }

        return res;
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

            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);

            stck[0] = BSQListOps::s_fill_ne_rec(lflavor, val, mid);
            stck[1] = BSQListOps::s_fill_ne_rec(lflavor, val, count - mid);

            res = BSQListOps::list_append(lflavor, stck[0], stck[1]);

            GCStack::popFrame(sizeof(void*) * 2);
        }

        return res;
    }

    static void* s_slice_start(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, const BSQListReprType* ttype, BSQNat start) 
    {
        if(start == 0)
        {
            return iter.lcurr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            auto count = BSQPartialVectorType::getPVCount(iter.lcurr);
            res = Allocator::GlobalAllocator.allocateDynamic(((count - start) <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, iter.lcurr, start, (uint64_t)count - start, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(iter.lcurr)->l);

            if(start < llcount)
            {
                iter.moveLeft();
                auto ll = BSQListOps::s_slice_start(lflavor, iter, lltype, start);
                iter.pop();

                res = BSQListOps::list_append(lflavor, ll, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);
            }
            else
            {
                auto rrtype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);

                iter.moveRight();
                res = BSQListOps::s_slice_start(lflavor, iter, rrtype, start - llcount);
                iter.pop();
            }
        }

        return res;
    }

    static void* s_slice_end(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, const BSQListReprType* ttype, BSQNat end) 
    {
        if(end == ttype->getCount(iter.lcurr))
        {
            return iter.lcurr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            res = Allocator::GlobalAllocator.allocateDynamic((end <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, iter.lcurr, 0, end, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(iter.lcurr)->l);

            auto rrtype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);

            if(end > llcount)
            {
                iter.moveRight();
                auto rr = BSQListOps::s_slice_end(lflavor, iter, rrtype, end - llcount);
                iter.pop();

                res = BSQListOps::list_append(lflavor, static_cast<BSQListTreeRepr*>(iter.lcurr)->l, rr);
            }
            else
            {
                iter.moveRight();
                res = BSQListOps::s_slice_end(lflavor, iter, lltype, end);
                iter.pop();
            }
        }
        return res;
    }

    static void* s_slice(const BSQListTypeFlavor& lflavor, BSQListSpineIterator& iter, const BSQListReprType* ttype, BSQNat start, BSQNat end) 
    {
        if(end == ttype->getCount(iter.lcurr))
        {
            return iter.lcurr;
        }

        void* res = nullptr;
        if(ttype->lkind != ListReprKind::TreeElement)
        {
            res = Allocator::GlobalAllocator.allocateDynamic((end <= 4) ? lflavor.pv4type : lflavor.pv8type);
            BSQPartialVectorType::slicePVData(res, iter.lcurr, start, end, lflavor.entrytype->allocinfo.inlinedatasize);
        }
        else
        {
            auto lltype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            auto rrtype = GET_TYPE_META_DATA_AS(BSQListReprType, static_cast<BSQListTreeRepr*>(iter.lcurr)->r);

            auto llcount = lltype->getCount(static_cast<BSQListTreeRepr*>(iter.lcurr)->l);
            if(end < llcount)
            {
                iter.moveLeft();
                res = BSQListOps::s_slice(lflavor, iter, lltype, start, end);
                iter.pop();
            }
            else if(start > llcount)
            {
                iter.moveRight();
                res = BSQListOps::s_slice(lflavor, iter, rrtype, start - llcount, end);
                iter.pop();
            }
            else
            {
                void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);

                iter.moveLeft();
                stck[0] = (start == 0) ? iter.lcurr : BSQListOps::s_slice_start(lflavor, iter, lltype, start);
                iter.pop();

                iter.moveRight();
                stck[1] = (end == llcount) ? iter.lcurr : BSQListOps::s_slice_end(lflavor, iter, rrtype, end - llcount);
                iter.pop();

                res = BSQListOps::list_append(lflavor, stck[0], stck[1]);

                GCStack::popFrame(sizeof(void*) * 2);
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
        return SLPTR_LOAD_HEAP_TYPE_AS(BSQListReprType, sl)->getCount(LIST_LOAD_DATA(sl));
    }

    static void* s_set_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i, StorageLocationPtr v);
    static void* s_push_back_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, StorageLocationPtr v);
    static void* s_push_front_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, StorageLocationPtr v);
    static void* s_remove_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i);
    static void* s_insert_ne(const BSQListTypeFlavor& lflavor, void* t, const BSQListReprType* ttype, BSQNat i, StorageLocationPtr v);

    static void s_range_ne(const BSQType* oftype, StorageLocationPtr start, StorageLocationPtr end, StorageLocationPtr count, StorageLocationPtr res);
    static void s_fill_ne(const BSQType* oftype, StorageLocationPtr val, StorageLocationPtr count, StorageLocationPtr res);

    static void* s_reverse_ne(const BSQListTypeFlavor& lflavor, void* reprnode);

    static BSQInt s_find_value_ne(void* t, const BSQListReprType* ttype, StorageLocationPtr v);
    static BSQInt s_find_value_last_ne(void* t, const BSQListReprType* ttype, StorageLocationPtr v);

    static BSQInt s_find_pred_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQInt s_find_pred_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQInt s_find_pred_last_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static BSQInt s_find_pred_last_idx_ne(LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);

    static void* s_filter_pred_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static void* s_filter_pred_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);

    static void* s_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);
    static void* s_map_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);
    static void* s_map_sync_ne(const BSQListTypeFlavor& lflavor1, const BSQListTypeFlavor& lflavor2, LambdaEvalThunk ee, uint64_t count, void* t1, const BSQListReprType* ttype1, void* t2, const BSQListReprType* ttype2, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);

    static void* s_filter_map_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* fn, const BSQPCode* p, const std::vector<StorageLocationPtr>& params, const BSQListTypeFlavor& resflavor);

    static void s_reduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res);
    static void s_reduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, StorageLocationPtr res);

    static void s_transduce_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres);
    static void s_transduce_idx_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQListTypeFlavor& uflavor, const BSQType* envtype, const BSQPCode* f, const std::vector<StorageLocationPtr>& params, const BSQEphemeralListType* rrtype, StorageLocationPtr eres);

    static void* s_sort_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* lt, const std::vector<StorageLocationPtr>& params);
    static void* s_unique_from_sorted_ne(const BSQListTypeFlavor& lflavor, LambdaEvalThunk ee, void* t, const BSQListReprType* ttype, const BSQPCode* eq, const std::vector<StorageLocationPtr>& params);
};

class BSQMapOps
{
public:
    static std::map<std::pair<BSQTypeID, BSQTypeID>, BSQMapTypeFlavor> g_flavormap; //map from entry type to the flavors of the repr

    static void* map_cons_one_element(const BSQMapTypeFlavor& mflavor, const BSQType* tupletype, const std::vector<StorageLocationPtr>& params)
    {
        void* repr = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
        const BSQTupleInfo* tupinfo = dynamic_cast<const BSQTupleInfo*>(tupletype);

        mflavor.treetype->initializeLeaf(repr, tupletype->indexStorageLocationOffset(params[0], tupinfo->idxoffsets[0]), mflavor.keytype, tupletype->indexStorageLocationOffset(params[0], tupinfo->idxoffsets[1]), mflavor.valuetype);
        return repr;
    }

    static void* s_lookup_ne(void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, const BSQType* ktype);
    static void* s_add_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl);
    static void* s_set_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl, StorageLocationPtr vl);
    static void* s_remove_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, StorageLocationPtr kl);

    static void* s_entries_ne(const BSQMapTypeFlavor& mflavor, void* t, const BSQMapTreeType* ttype, const BSQListTypeFlavor& lflavor);

    template <typename OP_PV>
    static void* map_tree_transform(const BSQMapTypeFlavor& mflavor, void* reprnode, OP_PV fn_node)
    {
        void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 3);
        stck[0] = reprnode;
        
        if(BSQMapTreeType::getLeft(stck[0]) != nullptr)
        {
            stck[1] = map_tree_transform(mflavor, BSQMapTreeType::getLeft(stck[0]), fn_node);
        }

        if(BSQMapTreeType::getRight(stck[0]) != nullptr)
        {
            stck[2] = map_tree_transform(mflavor, BSQMapTreeType::getRight(stck[0]), fn_node);
        }

        auto res = fn_node(stck[0], stck[1], stck[2]);

        GCStack::popFrame(sizeof(void*) * 3);
        return res;
    }

    static std::pair<void*, void*> extract_min_and_remaining_tree(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter)
    {
        BSQ_INTERNAL_ASSERT(iter.lcurr != nullptr);

        std::pair<void*, void*> res;
        if(BSQMapTreeType::getLeft(iter.lcurr) != nullptr)
        {
            void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 2);

            iter.moveLeft();
            auto tnp = BSQMapOps::extract_min_and_remaining_tree(mflavor, iter);
            stck[0] = tnp.first;
            stck[1] = tnp.second;
            iter.pop();

            res = std::make_pair((void*)Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype), stck[1]);
            mflavor.treetype->initializeLR(res.first, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], BSQMapTreeType::getRight(iter.lcurr));

            GCStack::popFrame(sizeof(void*) * 2);
        }
        else
        {
            res = std::make_pair(BSQMapTreeType::getRight(iter.lcurr), iter.lcurr);
        }

        return res;
    }

    template <typename OP_PV>
    static void* map_tree_flatten(const BSQMapTypeFlavor& mflavor, BSQMapSpineIterator& iter, OP_PV pred)
    {
        void** stck = (void**)GCStack::allocFrame(sizeof(void*) * 4);

        stck[0] = nullptr;
        if(BSQMapTreeType::getLeft(iter.lcurr) != nullptr)
        {
            iter.moveLeft();
            stck[0] = map_tree_flatten(mflavor, iter, pred);
            iter.pop();
        }

        stck[1] = nullptr;
        if(BSQMapTreeType::getRight(iter.lcurr) != nullptr)
        {
            iter.moveRight();
            stck[1] = map_tree_flatten(mflavor, iter, pred);
            iter.pop();
        }

        auto keepnode = pred(mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.treetype->getValueLocation(iter.lcurr));

        void* res = nullptr;
        if(keepnode)
        {
            res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
            mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(iter.lcurr), mflavor.keytype, mflavor.treetype->getValueLocation(iter.lcurr), mflavor.valuetype, stck[0], stck[1]);
        }
        else
        {
            if(stck[0] == nullptr && stck[1] == nullptr)
            {
                res = nullptr;
            }
            else if(stck[0] == nullptr)
            {
                res = stck[1];
            }
            else if(stck[1] == nullptr)
            {
                res = stck[0];
            }
            else
            {
                iter.moveRight();
                auto tnp = BSQMapOps::extract_min_and_remaining_tree(mflavor, iter);
                stck[2] = tnp.first;
                stck[3] = tnp.second;
                iter.pop();

                res = Allocator::GlobalAllocator.allocateDynamic(mflavor.treetype);
                mflavor.treetype->initializeLR(res, mflavor.treetype->getKeyLocation(stck[3]), mflavor.keytype, mflavor.treetype->getValueLocation(stck[3]), mflavor.valuetype, BSQMapTreeType::getLeft(iter.lcurr), stck[2]);
            }
        }

        GCStack::popFrame(sizeof(void*) * 4);
        return res;
    }

    static void s_enumerate_for_extract(const BSQMapTypeFlavor& mflavor, void* tn, std::list<StorageLocationPtr>& ll)
    {
        if(BSQMapTreeType::getLeft(tn) != nullptr)
        {
            s_enumerate_for_extract(mflavor, BSQMapTreeType::getLeft(tn), ll);
        }

        ll.push_back(mflavor.treetype->getKeyLocation(tn));
        ll.push_back(mflavor.treetype->getValueLocation(tn));

        if(BSQMapTreeType::getRight(tn) != nullptr)
        {
            s_enumerate_for_extract(mflavor, BSQMapTreeType::getRight(tn), ll);
        }
    }
    
    static void* s_fast_union_ne(const BSQMapTypeFlavor& mflavor, void* t1, const BSQMapTreeType* ttype1, void* t2, const BSQMapTreeType* ttype2);
    
    static void* s_submap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* pred, const std::vector<StorageLocationPtr>& params);
    static void* s_remap_ne(const BSQMapTypeFlavor& mflavor, LambdaEvalThunk ee, void* t, const BSQMapTreeType* ttype, const BSQPCode* fn, const std::vector<StorageLocationPtr>& params, const BSQMapTypeFlavor& resflavor);
};
