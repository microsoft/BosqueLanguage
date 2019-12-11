//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <cstdlib>
#include <cstdint>

#include <string>
#include <iostream>
#include <codecvt>

#include <regex>
#include <vector>
#include <set>
#include <map>

#include <algorithm>

#ifdef BDEBUG
#define BSQ_ASSERT(C, MSG) (bsqassert(C, MSG, __FILE__, __LINE__))
#else
#define BSQ_ASSERT(C, MSG)
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
void bsqassert(bool cond, const char* msg, const char* file, int32_t line);

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
