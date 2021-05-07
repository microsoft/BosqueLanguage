//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

BSQNoneType* Environment::g_typeNone;
BSQBoolType* Environment::g_typeBool;
BSQNatType* Environment::g_typeNat;
BSQIntType* Environment::g_typeInt;
BSQBigNatType* Environment::g_typeBigNat;
BSQBigIntType* Environment::g_typeBigInt;
BSQFloatType* Environment::g_typeFloat;
BSQDecimalType* Environment::g_typeDecimal;
BSQRationalType* Environment::g_typeRational;

BSQStringKReprTypeAbstract Environment::g_typeStringKReprAbstract;
BSQStringKReprType<8>* Environment::g_typeStringKRepr8;
BSQStringKReprType<16>* Environment::g_typeStringKRepr16;
BSQStringKReprType<32>* Environment::g_typeStringKRepr32;
BSQStringKReprType<64>* Environment::g_typeStringKRepr64;
BSQStringKReprType<128>* Environment::g_typeStringKRepr128;
BSQStringKReprType<256>* Environment::g_typeStringKRepr256;

BSQStringConcatReprType* Environment::g_typeStringConcatRepr;
BSQStringSliceReprType* Environment::g_typeStringSliceRepr;

BSQStringType* Environment::g_typeString;

std::map<BSQTypeID, ListTypeConstructorInfo> Environment::g_listTypeMap;

BSQNone Environment::g_constNone = 0;
BSQBool Environment::g_constTrue = (BSQBool)true;
BSQBool Environment::g_constFalse = (BSQBool)false;
BSQNat* Environment::g_constNats = nullptr;
BSQInt* Environment::g_constInts = nullptr;

BSQBigNat* Environment::g_constBigNats = nullptr;
BSQBigInt* Environment::g_constBigInts = nullptr;
BSQRational* Environment::g_constRationals = nullptr;
BSQFloat* Environment::g_constFloats = nullptr;
BSQDecimal* Environment::g_constDecimals = nullptr;
BSQString* Environment::g_constStrings = nullptr; 
BSQRegex* Environment::g_constRegexs = nullptr;

std::vector<BSQInvokeDecl*> Environment::g_invokes;

