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
    BSQListEmptyType* empty;
    BSQListFlatKType<64>* list64;
    BSQListFlatKType<96>* list96;
    BSQListFlatKType<128>* list128;
    BSQListFlatKType<160>* list160;
    BSQListFlatKType<192>* list192;
    BSQListFlatKType<224>* list224;
    BSQListFlatKType<256>* list256;
    BSQListSliceType* slice;
    BSQListConcatType* concat;
};

class Environment
{
public:
    static jmp_buf g_entrybuff;

    static std::map<BSQTypeID, BSQType*> g_typemap;
    static std::map<BSQRecordPropertyID, std::string> g_propertymap;
    static std::map<BSQFieldID, std::string> g_fieldmap;

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
