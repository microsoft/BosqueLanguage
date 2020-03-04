//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating the various MapEntry types
//

#ifndef Ty
#define Ty TName
#define T int
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define T_GET_KEY(X) 0
#define K int
#define INC_RC_K(X)
#define DEC_RC_K(X)
#define K_LIST TKName
#define KLCONS(K, KL) TCNAME
#define K_CMP(X, Y) false
#define K_EQ(X, Y) false
#define BSCOPE
#define TDisplay(X)
#endif

class Ty : public BSQObject {
public:
    std::map<K, T, K_CMP> entries;
    K_LIST* keys;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries(), keys(nullptr) { ; }
    Ty(MIRNominalTypeEnum ntype, std::map<K, T, K_CMP>&& entries, K_LIST* keys) : BSQObject(ntype), entries(move(entries)), keys(keys) { ; }

    virtual ~Ty()
    {
        ;
    }

    virtual void destroy()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            DEC_RC_K(iter->first);
            DEC_RC_T(iter->second);
        }
        BSQRef::decrementChecked(keys);
    }

    template <uint16_t n>
    static Ty* createFromSingle(BSQRefScope& scope, MIRNominalTypeEnum ntype, const T(&values)[n])
    {
        std::map<K, T, K_CMP> entries;
        K_LIST* keys = nullptr;

        for (int i = 0; i < n; i++)
        {
            auto val = values[i];
            auto key = T_GET_KEY(val);

            auto iter = entries.find(key);
            if(iter != entries.cend())
            {
                auto vv = INC_RC_T(val);
                DEC_RC_T(iter->second);
                entries[iter->first] = vv;
            }
            else
            {
                keys = INC_REF_CHECK(K_LIST, KLCONS(INC_RC_K(key), keys));

                entries[INC_RC_K(key)] = INC_RC_T(val);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, Ty, ntype, move(entries), keys);
    }

    Ty* add(K key, T val, K_LIST* nkeys, BSQRefScope& cscope)
    {
        std::map<K, T, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            entries[INC_RC_K(iter->first)] = INC_RC_T(iter->second);
        }

        entries[INC_RC_K(key)] = INC_RC_T(val);

        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), INC_REF_CHECK(K_LIST, nkeys));
    }

    Ty* update(K key, T val, BSQRefScope& cscope)
    {
        std::map<K, T, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(K_EQ(key, iter->first))
            {
                entries[INC_RC_K(iter->first)] = INC_RC_T(val);
            }
            else
            {
                entries[INC_RC_K(iter->first)] = INC_RC_T(iter->second);
            }
        }
       
        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), INC_REF_CHECK(K_LIST, this->keys));
    }

    Ty* clearKey(K key, K_LIST* nkeys, BSQRefScope& cscope)
    {
        std::map<K, T, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(!K_EQ(key, iter->first)) 
            {
                entries[INC_RC_K(iter->first)] = INC_RC_T(iter->second);
            }
        }

        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), INC_REF_CHECK(K_LIST, nkeys));
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        std::u32string ss(U"{");
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ss += U", ";
            }
            first = false;

            BSQRefScope BSCOPE;
            ss += FDisplay(iter->second);
        }
        ss += U"}";

        return ss;
    }
};

#undef Ty
#undef T
#undef INC_RC_T
#undef DEC_RC_T
#undef T_GET_KEY
#undef K
#undef INC_RC_K
#undef DEC_RC_K
#undef K_LIST
#undef KLCONS
#undef K_CMP
#undef K_EQ
#undef BSCOPE
#undef TDisplay
