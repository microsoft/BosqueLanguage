//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "bsqmemory.h"

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>
#include <boost/rational.hpp>

//All values must be passed as uniform representation -- so we pick a void* -- then we cast and load/store the value
//Compiler will want to distinguish between SLValues and values that can be passed by value
typedef void* SLValue;

////
//Primitive value representations

typedef uint64_t BSQNone;
#define NoneValue 0
#define BSQ_NONE_VALUE nullptr

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

typedef uint64_t BSQNat;
typedef int64_t BSQInt;

typedef boost::multiprecision::checked_uint256_t BSQBigNat;
typedef boost::multiprecision::checked_uint256_t BSQBigInt;

typedef boost::multiprecision::cpp_bin_float_double BSQFloat;
typedef boost::multiprecision::cpp_dec_float_100 BSQDecimal;

typedef boost::rational<BSQBigInt> BSQRational;

