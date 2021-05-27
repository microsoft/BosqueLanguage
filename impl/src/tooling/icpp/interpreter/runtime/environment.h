//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "bsqvalue.h"
#include "bsqcollections.h"

#include "../assembly/bsqassembly.h"

struct ListTypeConstructorInfo
{
    BSQListType list;
    BSQListFlatKType<4>* list4;
    BSQListFlatKType<8>* list8;
    BSQListFlatKType<12>* list12;
    BSQListFlatKType<16>* list16;
    BSQListFlatKType<24>* list24;
    BSQListFlatKType<32>* list32;
    BSQListFlatKType<40>* list40;
    BSQListSliceType* slice;
    BSQListConcatType* concat;
};

class Environment
{
public:
    static jmp_buf g_entrybuff;

    //Well known types
    static const BSQNoneType* g_typeNone;
    static const BSQBoolType* g_typeBool;
    static const BSQNatType* g_typeNat;
    static const BSQIntType* g_typeInt;
    static const BSQBigNatType* g_typeBigNat;
    static const BSQBigIntType* g_typeBigInt;
    static const BSQFloatType* g_typeFloat;
    static const BSQDecimalType* g_typeDecimal;
    static const BSQRationalType* g_typeRational;

    //String flavors
    static BSQStringKReprType<8>* g_typeStringKRepr8;
    static BSQStringKReprType<16>* g_typeStringKRepr16;
    static BSQStringKReprType<32>* g_typeStringKRepr32;
    static BSQStringKReprType<64>* g_typeStringKRepr64;
    static BSQStringKReprType<128>* g_typeStringKRepr128;
    static BSQStringKReprType<256>* g_typeStringKRepr256;

    static BSQStringConcatReprType* g_typeStringConcatRepr;
    static BSQStringSliceReprType* g_typeStringSliceRepr;

    static BSQStringType* g_typeString;

    static std::map<BSQTypeID, ListTypeConstructorInfo> g_listTypeMap;

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

    static std::vector<std::vector<BSQTypeID>> g_subtypes;
    static std::vector<BSQInvokeDecl*> g_invokes;
};
