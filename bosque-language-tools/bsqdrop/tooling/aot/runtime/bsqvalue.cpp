//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
BSQTuple BSQTuple::_empty({}, DATA_KIND_ALL_FLAG);
BSQRecord BSQRecord::_empty({}, DATA_KIND_ALL_FLAG);

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
        return EqualFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return false;
        }
        
        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr1->nominalType);
        switch(rcategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::eq(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyEqual(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyEqual(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyEqual(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyEqual(dynamic_cast<Boxed_BSQUUID*>(ptr1)->bval, dynamic_cast<Boxed_BSQUUID*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyEqual(dynamic_cast<Boxed_BSQLogicalTime*>(ptr1)->bval, dynamic_cast<Boxed_BSQLogicalTime*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyEqual(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyEqual(dynamic_cast<Boxed_BSQEnum*>(ptr1)->bval, dynamic_cast<Boxed_BSQEnum*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyEqual(dynamic_cast<Boxed_BSQIdKeySimple*>(ptr1)->bval, dynamic_cast<Boxed_BSQIdKeySimple*>(ptr2)->bval);
            default:
                return BSQIdKeyCompound::keyEqual(dynamic_cast<BSQIdKeyCompound*>(ptr1), dynamic_cast<BSQIdKeyCompound*>(ptr2));
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
        return LessFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return ptr1->nominalType < ptr2->nominalType;
        }
        
        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr1->nominalType);
        switch(rcategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::lt(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyLess(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyLess(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyLess(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyLess(dynamic_cast<Boxed_BSQUUID*>(ptr1)->bval, dynamic_cast<Boxed_BSQUUID*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyLess(dynamic_cast<Boxed_BSQLogicalTime*>(ptr1)->bval, dynamic_cast<Boxed_BSQLogicalTime*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyLess(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyLess(dynamic_cast<Boxed_BSQEnum*>(ptr1)->bval, dynamic_cast<Boxed_BSQEnum*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyLess(dynamic_cast<Boxed_BSQIdKeySimple*>(ptr1)->bval, dynamic_cast<Boxed_BSQIdKeySimple*>(ptr2)->bval);
            default:
                return BSQIdKeyCompound::keyLess(dynamic_cast<BSQIdKeyCompound*>(ptr1), dynamic_cast<BSQIdKeyCompound*>(ptr2));
        }
    }
}

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_ALL_FLAG;
    }
    else {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);

        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr->nominalType);
        if(rcategory == MIRNominalTypeEnum_Category_Tuple) {
            return dynamic_cast<BSQTuple*>(ptr)->flag;
        }
        else if(rcategory == MIRNominalTypeEnum_Category_Record) {
            return dynamic_cast<BSQRecord*>(ptr)->flag;
        }
        else {
            return nominalDataKinds[GET_MIR_TYPE_POSITION(getNominalTypeOf_Value(v))];
        }
    }
}

std::string diagnostic_format(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return std::string("none");
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? std::string("true") : std::string("false");
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return std::to_string(BSQ_GET_VALUE_TAGGED_INT(v));
    }
    else
    {
        BSQRef* vv = BSQ_GET_VALUE_PTR(v, BSQRef);
    
        auto rcategory = GET_MIR_TYPE_CATEGORY(vv->nominalType);
        switch(rcategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return DisplayFunctor_BSQBigInt{}(dynamic_cast<BSQBigInt*>(vv));
            case MIRNominalTypeEnum_Category_String:
                return DisplayFunctor_BSQString{}(dynamic_cast<BSQString*>(vv));
            case MIRNominalTypeEnum_Category_SafeString:
                return DisplayFunctor_BSQSafeString{}(dynamic_cast<BSQSafeString*>(vv));
            case MIRNominalTypeEnum_Category_StringOf:
                return DisplayFunctor_BSQStringOf{}(dynamic_cast<BSQStringOf*>(vv));
            case MIRNominalTypeEnum_Category_UUID:
                return DisplayFunctor_BSQUUID{}(dynamic_cast<Boxed_BSQUUID*>(vv)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return DisplayFunctor_BSQLogicalTime{}(dynamic_cast<Boxed_BSQLogicalTime*>(vv)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return DisplayFunctor_BSQCryptoHash{}(dynamic_cast<BSQCryptoHash*>(vv));
            case MIRNominalTypeEnum_Category_Enum:
                return DisplayFunctor_BSQEnum{}(dynamic_cast<Boxed_BSQEnum*>(vv)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return DisplayFunctor_BSQIdKeySimple{}(dynamic_cast<Boxed_BSQIdKeySimple*>(vv)->bval);
            case MIRNominalTypeEnum_Category_IdKeyCompound:
                return DisplayFunctor_BSQIdKeyCompound{}(dynamic_cast<BSQIdKeyCompound*>(vv));
            case MIRNominalTypeEnum_Category_Float64:
                return DisplayFunctor_double{}(dynamic_cast<Boxed_double*>(vv)->bval);
            case MIRNominalTypeEnum_Category_ByteBuffer:
                return DisplayFunctor_BSQByteBuffer{}(dynamic_cast<BSQByteBuffer*>(vv));
            case MIRNominalTypeEnum_Category_Buffer:
                return DisplayFunctor_BSQBuffer{}(dynamic_cast<BSQBuffer*>(vv));
            case MIRNominalTypeEnum_Category_BufferOf:
                return DisplayFunctor_BSQBufferOf{}(dynamic_cast<BSQBufferOf*>(vv));
            case MIRNominalTypeEnum_Category_ISOTime:
                return DisplayFunctor_BSQISOTime{}(dynamic_cast<Boxed_BSQISOTime*>(vv)->bval);
            case MIRNominalTypeEnum_Category_Regex:
                return DisplayFunctor_BSQRegex{}(dynamic_cast<BSQRegex*>(vv));
            case MIRNominalTypeEnum_Category_Tuple:
                return DisplayFunctor_BSQTuple{}(*dynamic_cast<BSQTuple*>(vv));
            case MIRNominalTypeEnum_Category_Record:
                return DisplayFunctor_BSQRecord{}(*dynamic_cast<BSQRecord*>(vv));
            default:
                return dynamic_cast<BSQObject*>(vv)->display();
        }
    }
}
}
