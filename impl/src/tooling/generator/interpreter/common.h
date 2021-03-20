//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>

#include <string>
#include <regex>

#include <vector>
#include <stack>
#include <queue>
#include <set>
#include <map>

#include <initializer_list>
#include <algorithm>
#include <numeric>
#include <execution>

#define BSQ_INTERNAL_ASSERT(C) if(!(C)) { assert(false); }

#ifdef BDEBUG
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) { throw BSQAbort(MSG, F, L); }
#else
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) { throw BSQAbort(); }
#endif

#ifdef BDEBUG
#define BSQ_ABORT(MSG, F, L) (throw BSQAbort(MSG, F, L))
#else
#define BSQ_ABORT(MSG, F, L) (throw BSQAbort())
#endif

#ifdef BDEBUG
#define HANDLE_BSQ_ABORT(abrt) { printf("\"%s\" in %s on line %i\n", abrt.msg, abrt.bfile, abrt.bline); fflush(stdout); exit(1); }
#else
#define HANDLE_BSQ_ABORT(abrt) { printf("ABORT\n"); exit(1); }
#endif

namespace BSQ
{
class BSQAbort
{
#ifdef BDEBUG
public:
const char* msg;
const char* bfile;
int32_t bline;

BSQAbort(const char* msg, const char* bfile, int32_t bline) : msg(msg), bfile(bfile), bline(bline) { ; }
#else
public:
BSQAbort() { ; }
#endif
};

typedef uint8_t bsqbool;
typedef int64_t bsqint;
typedef uint64_t bsqnat;

} // namespace BSQ
