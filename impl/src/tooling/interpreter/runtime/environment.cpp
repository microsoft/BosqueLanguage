//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "environment.h"

BSQNoneType* Environment::g_typeNone = new BSQNoneType();
BSQBoolType* Environment::g_typeBool = new BSQBoolType();
BSQNatType* Environment::g_typeNat = new BSQNatType();
BSQIntType* Environment::g_typeInt = new BSQIntType();
BSQBigNatType* Environment::g_typeBigNat = new BSQBigNatType();
BSQBigIntType* Environment::g_typeBigInt = new BSQBigIntType();
BSQFloatType* Environment::g_typeFloat = new BSQFloatType();
BSQDecimalType* Environment::g_typeDecimal = new BSQDecimalType();
BSQRationalType* Environment::g_typeRational = new BSQRationalType();

BSQStringKReprType<8>* Environment::g_typeStringKRepr8 = new BSQStringKReprType<8>();
BSQStringKReprType<16>* Environment::g_typeStringKRepr16 = new BSQStringKReprType<16>();
BSQStringKReprType<32>* Environment::g_typeStringKRepr32 = new BSQStringKReprType<32>(); 
BSQStringKReprType<64>* Environment::g_typeStringKRepr64 = new BSQStringKReprType<64>();
BSQStringKReprType<128>* Environment::g_typeStringKRepr128 = new BSQStringKReprType<128>();
BSQStringKReprType<256>* Environment::g_typeStringKRepr256 = new BSQStringKReprType<256>();

BSQStringConcatReprType* Environment::g_typeStringConcatRepr = new BSQStringConcatReprType();
BSQStringSliceReprType* Environment::g_typeStringSliceRepr = new BSQStringSliceReprType();

BSQStringType* Environment::g_typeString = new BSQStringType();

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

