//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <stdarg.h>
#include <math.h>

#include <string>
#include <regex>
#include <iostream>
#include <codecvt>

#include <initializer_list>
#include <algorithm>
#include <numeric>
#include <execution>

#ifdef BDEBUG
#define BSQ_ASSERT(C, MSG) if(!(C)) { throw BSQAbort(MSG, __FILE__, __LINE__, __FILE__, __LINE__); }
#else
#define BSQ_ASSERT(C, MSG) if(!(C)) { throw BSQAbort(); }
#endif

#ifdef BDEBUG
#define BSQ_ABORT(MSG, F, L) (throw BSQAbort(MSG, F, L, __FILE__, __LINE__))
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
const char* cfile;
int32_t cline;

BSQAbort(const char* msg, const char* bfile, int32_t bline, const char* cfile, int32_t cline) : msg(msg), bfile(bfile), bline(bline), cfile(cfile), cline(cline) { ; }
#else
public:
BSQAbort() { ; }
#endif
};

} // namespace BSQ
