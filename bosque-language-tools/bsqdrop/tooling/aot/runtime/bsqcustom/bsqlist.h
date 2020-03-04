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
#define FDisplay(X)
#define BSCOPE
#endif

class Ty : public BSQObject {
public:
    std::vector<T> entries;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    Ty(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    template <uint16_t n>
    static Ty* createFromSingle(BSQRefScope& scope, MIRNominalTypeEnum ntype, const T(&values)[n])
    {
        std::vector<T> entries;

        for (int i = 0; i < n; i++)
        {
            entries.push_back(INC_RC_T(values[i]));
        }

        return BSQ_NEW_ADD_SCOPE(scope, Ty, ntype, move(entries));
    }

    virtual ~Ty() = default;

    virtual void destroy()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            DEC_RC_T(this->entries[i]);
        }
    }

    Ty* unsafeAdd(BSQRefScope& scope, T v) const
    {
        std::vector<T> nv;
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            nv.push_back(INC_RC_T(this->entries[i]));
        }
        nv.push_back(INC_RC_T(v));

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->nominalType, move(nv));
    }

    Ty* unsafeSet(BSQRefScope& scope, int64_t idx, T v) const
    {
        std::vector<T> nv;
        for(int64_t i = 0; i < this->entries.size(); ++i)
        {
            if(i == idx)
            {
                nv.push_back(INC_RC_T(v));
            }
            else
            {
                nv.push_back(this->entries[i]);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->nominalType, move(nv));
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

        std::u32string ls(U"{");
        for (size_t i = 0; i < this->entries.size(); ++i)
        {
            if (i != 0)
            {
                ls += U", ";
            }

            BSQRefScope BSCOPE;
            ls += FDisplay(this->entries.at(i));
        }
        ls += U"}";

        return ls;
    }
};

#undef Ty
#undef T
#undef INC_RC_T
#undef DEC_RC_T
#undef BSCOPE
#undef FDisplay
