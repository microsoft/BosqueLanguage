//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#define COERSE_TO_BIG_INT(X) (BSQ_IS_VALUE_TAGGED_INT(X) ? BSQ_GET_VALUE_PTR(X, BSQBigInt) : BSQ_NEW_ADD_SCOPE(scope, BSQBigInt, BSQ_GET_VALUE_TAGGED_INT(X)))

namespace BSQ
{
BSQTuple* BSQTuple::_empty = INC_REF_DIRECT(BSQTuple, new BSQTuple({}, DATA_KIND_POD_FLAG));
BSQRecord* BSQRecord::_empty = INC_REF_DIRECT(BSQRecord, new BSQRecord({}, DATA_KIND_POD_FLAG));

size_t bsqKeyValueHash(KeyValue v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return 0;
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return (size_t)BSQ_GET_VALUE_BOOL(v);
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return BSQ_GET_VALUE_TAGGED_INT(v);
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef); 
        if(dynamic_cast<BSQBigInt*>(ptr) != nullptr)
        {
            return dynamic_cast<BSQBigInt*>(ptr)->hash();
        }
        else if(dynamic_cast<BSQString*>(ptr) != nullptr)
        {
            return BSQString::hash(dynamic_cast<BSQString*>(ptr));
        }
         else if(dynamic_cast<BSQSafeString*>(ptr) != nullptr)
        {
            return BSQSafeString::hash(dynamic_cast<BSQSafeString*>(ptr));
        }
        else if(dynamic_cast<BSQStringOf*>(ptr) != nullptr)
        {
            return BSQStringOf::hash(dynamic_cast<BSQStringOf*>(ptr));
        }
        else if(dynamic_cast<BSQGUID*>(ptr) != nullptr)
        {
            return BSQGUID::hash(dynamic_cast<BSQGUID*>(ptr));
        }
        else if(dynamic_cast<BSQDataHash*>(ptr) != nullptr)
        {
            return BSQDataHash::hash(*dynamic_cast<BSQDataHash*>(ptr));
        }
        else if(dynamic_cast<BSQCryptoHash*>(ptr) != nullptr)
        {
            return BSQCryptoHash::hash(dynamic_cast<BSQCryptoHash*>(ptr));
        }
        else if(dynamic_cast<BSQLogicalTime*>(ptr) != nullptr)
        {
            return BSQLogicalTime::hash(*dynamic_cast<BSQLogicalTime*>(ptr));
        }
        else if(dynamic_cast<BSQEnum*>(ptr) != nullptr)
        {
            return BSQEnum::hash(*dynamic_cast<BSQEnum*>(ptr));
        }
        else if(dynamic_cast<BSQIdKey*>(ptr) != nullptr)
        {
            return BSQIdKey::hash(dynamic_cast<BSQIdKey*>(ptr));
        }
        else if(dynamic_cast<BSQGUIDIdKey*>(ptr) != nullptr)
        {
            return BSQGUIDIdKey::hash(dynamic_cast<BSQGUIDIdKey*>(ptr));
        }
         else if(dynamic_cast<BSQLogicalTimeIdKey*>(ptr) != nullptr)
        {
            return BSQLogicalTimeIdKey::hash(*dynamic_cast<BSQLogicalTimeIdKey*>(ptr));
        }
        else
        {
            return BSQContentHashIdKey::hash(dynamic_cast<BSQContentHashIdKey*>(ptr));
        }
    }
}

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2)
{
    if(v1 == v2) {
        return true;
    }

    if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
    {
        return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONE(v2);
    }
    else if(BSQ_IS_VALUE_BOOL(v1) && BSQ_IS_VALUE_BOOL(v2))
    {
        return EqualFunctor_bool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v1) || BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return EqualFunctor_IntValue{}((IntValue)v1, (IntValue)v2);
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return false;
        }
        
        if(dynamic_cast<BSQBigInt*>(ptr1) != nullptr && dynamic_cast<BSQBigInt*>(ptr2) != nullptr)
        {
            return BSQBigInt::eq(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
        }
        else if(dynamic_cast<BSQString*>(ptr1) != nullptr && dynamic_cast<BSQString*>(ptr2) != nullptr)
        {
            return BSQString::keyEqual(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
        }
        else if(dynamic_cast<BSQSafeString*>(ptr1) != nullptr && dynamic_cast<BSQSafeString*>(ptr2) != nullptr)
        {
            return BSQSafeString::keyEqual(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
        }
        else if(dynamic_cast<BSQStringOf*>(ptr1) != nullptr && dynamic_cast<BSQStringOf*>(ptr2) != nullptr)
        {
            return BSQStringOf::keyEqual(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
        }
        else if(dynamic_cast<BSQGUID*>(ptr1) != nullptr && dynamic_cast<BSQGUID*>(ptr2) != nullptr)
        {
            return BSQGUID::keyEqual(dynamic_cast<BSQGUID*>(ptr1), dynamic_cast<BSQGUID*>(ptr2));
        }
        else if(dynamic_cast<BSQDataHash*>(ptr1) != nullptr && dynamic_cast<BSQDataHash*>(ptr2) != nullptr)
        {
            return BSQDataHash::keyEqual(*dynamic_cast<BSQDataHash*>(ptr1), *dynamic_cast<BSQDataHash*>(ptr2));
        }
        else if(dynamic_cast<BSQCryptoHash*>(ptr1) != nullptr && dynamic_cast<BSQCryptoHash*>(ptr2) != nullptr)
        {
            return BSQCryptoHash::keyEqual(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
        }
        else if(dynamic_cast<BSQLogicalTime*>(ptr1) != nullptr && dynamic_cast<BSQLogicalTime*>(ptr2) != nullptr)
        {
            return BSQLogicalTime::keyEqual(*dynamic_cast<BSQLogicalTime*>(ptr1), *dynamic_cast<BSQLogicalTime*>(ptr2));
        }
        else if(dynamic_cast<BSQEnum*>(ptr1) != nullptr && dynamic_cast<BSQEnum*>(ptr2) != nullptr)
        {
            return BSQEnum::keyEqual(*dynamic_cast<BSQEnum*>(ptr1), *dynamic_cast<BSQEnum*>(ptr2));
        }
        else if(dynamic_cast<BSQIdKey*>(ptr1) != nullptr && dynamic_cast<BSQIdKey*>(ptr2) != nullptr)
        {
            return BSQIdKey::keyEqual(dynamic_cast<BSQIdKey*>(ptr1), dynamic_cast<BSQIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQGUIDIdKey*>(ptr1) != nullptr && dynamic_cast<BSQGUIDIdKey*>(ptr2) != nullptr)
        {
            return BSQGUIDIdKey::keyEqual(dynamic_cast<BSQGUIDIdKey*>(ptr1), dynamic_cast<BSQGUIDIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQLogicalTimeIdKey*>(ptr1) != nullptr && dynamic_cast<BSQLogicalTimeIdKey*>(ptr2) != nullptr)
        {
            return BSQLogicalTimeIdKey::keyEqual(*dynamic_cast<BSQLogicalTimeIdKey*>(ptr1), *dynamic_cast<BSQLogicalTimeIdKey*>(ptr2));
        }
        else
        {
            return BSQContentHashIdKey::keyEqual(dynamic_cast<BSQContentHashIdKey*>(ptr1), dynamic_cast<BSQContentHashIdKey*>(ptr2));
        }
    }
}

bool bsqKeyValueLess(KeyValue v1, KeyValue v2)
{
    if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
    {
        return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONNONE(v2);
    }
    else if(BSQ_IS_VALUE_BOOL(v1) && BSQ_IS_VALUE_BOOL(v2))
    {
        return LessFunctor_bool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v1) || BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return LessFunctor_IntValue{}((IntValue)v1, (IntValue)v2);
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return ptr1->nominalType < ptr2->nominalType;
        }
        
        if(dynamic_cast<BSQBigInt*>(ptr1) != nullptr && dynamic_cast<BSQBigInt*>(ptr2) != nullptr)
        {
            return BSQBigInt::lt(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
        }
        else if(dynamic_cast<BSQString*>(ptr1) != nullptr && dynamic_cast<BSQString*>(ptr2) != nullptr)
        {
            return BSQString::keyLess(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
        }
        else if(dynamic_cast<BSQSafeString*>(ptr1) != nullptr && dynamic_cast<BSQSafeString*>(ptr2) != nullptr)
        {
            return BSQSafeString::keyLess(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
        }
        else if(dynamic_cast<BSQStringOf*>(ptr1) != nullptr && dynamic_cast<BSQStringOf*>(ptr2) != nullptr)
        {
            return BSQStringOf::keyLess(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
        }
        else if(dynamic_cast<BSQGUID*>(ptr1) != nullptr && dynamic_cast<BSQGUID*>(ptr2) != nullptr)
        {
            return BSQGUID::keyLess(dynamic_cast<BSQGUID*>(ptr1), dynamic_cast<BSQGUID*>(ptr2));
        }
        else if(dynamic_cast<BSQDataHash*>(ptr1) != nullptr && dynamic_cast<BSQDataHash*>(ptr2) != nullptr)
        {
            return BSQDataHash::keyLess(*dynamic_cast<BSQDataHash*>(ptr1), *dynamic_cast<BSQDataHash*>(ptr2));
        }
        else if(dynamic_cast<BSQCryptoHash*>(ptr1) != nullptr && dynamic_cast<BSQCryptoHash*>(ptr2) != nullptr)
        {
            return BSQCryptoHash::keyLess(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
        }
        else if(dynamic_cast<BSQLogicalTime*>(ptr1) != nullptr && dynamic_cast<BSQLogicalTime*>(ptr2) != nullptr)
        {
            return BSQLogicalTime::keyLess(*dynamic_cast<BSQLogicalTime*>(ptr1), *dynamic_cast<BSQLogicalTime*>(ptr2));
        }
        else if(dynamic_cast<BSQEnum*>(ptr1) != nullptr && dynamic_cast<BSQEnum*>(ptr2) != nullptr)
        {
            return BSQEnum::keyLess(*dynamic_cast<BSQEnum*>(ptr1), *dynamic_cast<BSQEnum*>(ptr2));
        }
        else if(dynamic_cast<BSQIdKey*>(ptr1) != nullptr && dynamic_cast<BSQIdKey*>(ptr2) != nullptr)
        {
            return BSQIdKey::keyLess(dynamic_cast<BSQIdKey*>(ptr1), dynamic_cast<BSQIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQGUIDIdKey*>(ptr1) != nullptr && dynamic_cast<BSQGUIDIdKey*>(ptr2) != nullptr)
        {
            return BSQGUIDIdKey::keyLess(dynamic_cast<BSQGUIDIdKey*>(ptr1), dynamic_cast<BSQGUIDIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQLogicalTimeIdKey*>(ptr1) != nullptr && dynamic_cast<BSQLogicalTimeIdKey*>(ptr2) != nullptr)
        {
            return BSQLogicalTimeIdKey::keyLess(*dynamic_cast<BSQLogicalTimeIdKey*>(ptr1), *dynamic_cast<BSQLogicalTimeIdKey*>(ptr2));
        }
        else
        {
            return BSQContentHashIdKey::keyLess(dynamic_cast<BSQContentHashIdKey*>(ptr1), dynamic_cast<BSQContentHashIdKey*>(ptr2));
        }
    }
}

MIRNominalTypeEnum getNominalTypeOf_KeyValue(KeyValue v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return MIRNominalTypeEnum_None;
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return MIRNominalTypeEnum_Bool;
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return MIRNominalTypeEnum_Int;
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
        return ptr->nominalType;
    }
}

MIRNominalTypeEnum getNominalTypeOf_Value(Value v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return MIRNominalTypeEnum_None;
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return MIRNominalTypeEnum_Bool;
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return MIRNominalTypeEnum_Int;
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
        return ptr->nominalType;
    }
}

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_POD_FLAG;
    }
    else {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);

        if(dynamic_cast<BSQTuple*>(ptr) != nullptr) {
            return dynamic_cast<BSQTuple*>(ptr)->flag;
        }
        else if(dynamic_cast<BSQRecord*>(ptr) != nullptr) {
            return dynamic_cast<BSQTuple*>(ptr)->flag;
        }
        else {
            return nominalDataKinds[(size_t)getNominalTypeOf_Value(v)];
        }
    }
}

std::string diagnostic_format(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return std::string(U"none");
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? std::string(U"true") : std::string(U"false");
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return std::to_string(BSQ_GET_VALUE_TAGGED_INT(v));
    }
    else
    {
        const BSQRef* vv = BSQ_GET_VALUE_PTR(v, const BSQRef);
        if(dynamic_cast<const BSQBigInt*>(vv) != nullptr)
        {
            return dynamic_cast<const BSQBigInt*>(vv)->display();
        }
        else if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQString{}(dynamic_cast<const BSQString*>(vv));
        }
        else if(dynamic_cast<const BSQSafeString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQSafeString{}(dynamic_cast<const BSQSafeString*>(vv));
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQStringOf{}(dynamic_cast<const BSQStringOf*>(vv));
        }
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUID{}(dynamic_cast<const BSQGUID*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQCryptoHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQCryptoHash{}(dynamic_cast<const BSQCryptoHash*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQLogicalTime*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQLogicalTime{}(*dynamic_cast<const BSQLogicalTime*>(vv));
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQEnum{}(*dynamic_cast<const BSQEnum*>(vv));
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQIdKey{}(dynamic_cast<const BSQIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQGUIDIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUIDIdKey{}(dynamic_cast<const BSQGUIDIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQContentHashIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQContentHashIdKey{}(dynamic_cast<const BSQContentHashIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQBuffer*>(vv) != nullptr)
        {
            auto pbuf = dynamic_cast<const BSQBuffer*>(vv);
            std::string rvals("PODBuffer{");
            for (size_t i = 0; i < pbuf->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += pbuf->sdata[i];
            }
            rvals += "}";

            return rvals;
        }
        else if(dynamic_cast<const BSQISOTime*>(vv) != nullptr)
        {
            return std::string{"ISOTime="} + std::to_string(dynamic_cast<const BSQISOTime*>(vv)->isotime) + "}";
        }
        else if(dynamic_cast<const BSQRegex*>(vv) != nullptr)
        {
            return std::string{"Regex="} + dynamic_cast<const BSQRegex*>(vv)->re;
        }
        else if(dynamic_cast<const BSQTuple*>(vv) != nullptr)
        {
            auto tv = dynamic_cast<const BSQTuple*>(vv);
            std::string tvals("[");
            for(size_t i = 0; i < tv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    tvals += ", ";
                }

                tvals += diagnostic_format(tv->entries.at(i));
            }
            tvals += "]";

            return tvals;
        }
        else if(dynamic_cast<const BSQRecord*>(vv) != nullptr)
        {
            auto rv = dynamic_cast<const BSQRecord*>(vv);
            std::string rvals("{");
            bool first = true;
            for(auto iter = rv->entries.cbegin(); iter != rv->entries.cend(); ++iter)
            {
                if(!first)
                {
                    rvals += ", ";
                }
                first = false;

                rvals += std::string(propertyNames[(int32_t)iter->first]) + "=" + diagnostic_format(iter->second);
            }
            rvals += "}";

            return rvals;
        }
        else
        {
            auto obj = dynamic_cast<const BSQObject*>(vv);
            return std::string(nominaltypenames[(uint32_t) obj->nominalType]) + obj->display();
        }
    }
}
}