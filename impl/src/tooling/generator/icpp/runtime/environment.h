//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqvalue.h"
#include "bsqcollections.h"

typedef StorageLocationPtr (*ConstValueLoad)();

class Environment
{
public:
    //Well known types
    static BSQNoneType* g_typeNone;
    static BSQBoolType* g_typeBool;
    static BSQNatType* g_typeNat;
    static BSQIntType* g_typeInt;
    static BSQBigNatType* g_typeBigNat;
    static BSQBigIntType* g_typeBigInt;
    static BSQFloatType* g_typeFloat;
    static BSQDecimalType* g_typeDecimal;
    static BSQRationalType* g_typeRational;

    //String flavors
    static BSQStringKReprTypeAbstract g_typeStringKReprAbstract;
    static BSQStringKReprType<8>* g_typeStringKRepr8;
    static BSQStringKReprType<16>* g_typeStringKRepr16;
    static BSQStringKReprType<32>* g_typeStringKRepr32;
    static BSQStringKReprType<64>* g_typeStringKRepr64;
    static BSQStringKReprType<128>* g_typeStringKRepr128;
    static BSQStringKReprType<256>* g_typeStringKRepr256;

    static BSQStringConcatReprType* g_typeStringConcatRepr;
    static BSQStringSliceReprType* g_typeStringSliceRepr;

    static BSQStringType* g_typeString;

    //List flavors
    static BSQListEmptyType* g_typeListEmpty;
    static BSQListFlatKTypeAbstract* g_typeListFlatKAbstract;
    static BSQListFlatKType<8>* g_typeListFlatK8;
    static BSQListFlatKType<16>* g_typeListFlatK16;
    static BSQListFlatKType<32>* g_typeListFlatK32;
    static BSQListFlatKType<64>* g_typeListFlatK64;
    static BSQListFlatKType<128>* g_typeListFlatK128;
    static BSQListFlatKType<256>* g_typeListFlatK256;

    static BSQListConcatType* g_typeListConcat;
    static BSQListSliceType* g_typeListSlice;

    //Constant storage locations
    static BSQNone g_constNone;
    static BSQBool g_constTrue;
    static BSQBool g_constFalse;
    static BSQNat* g_constNats;
    static BSQInt* g_constInts;

    static BSQBigNat* g_constBigNats;
    static BSQBigInt* g_constBigInts;
    static BSQRational* g_constRationals;
    static BSQFloat* g_constFloats;
    static BSQDecimal* g_constDecimals;
    static BSQString* g_constStrings; 
    static BSQRegex* g_constRegexs;

    static ConstValueLoad* g_constLoads;
};
