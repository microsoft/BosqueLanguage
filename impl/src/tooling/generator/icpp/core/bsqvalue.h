//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../common.h"
#include "../assembly/bsqtype.h"
#include "bsqmemory.h"

//All values must be passed as uniform representation -- so we pick a void* -- then we cast and load/store the value
typedef void* InterpValue;

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
