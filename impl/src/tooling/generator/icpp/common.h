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
#define HANDLE_BSQ_ABORT(MSG, F, L) { wprintf(L"\"%s\" in %s on line %i\n", MSG, F, L); fflush(stdout); exit(1); }
#else
#define HANDLE_BSQ_ABORT() { printf("ABORT\n"); exit(1); }
#endif

#ifdef BDEBUG
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT(MSG, F, L);
#else
#define BSQ_LANGUAGE_ASSERT(C, F, L, MSG) if(!(C)) HANDLE_BSQ_ABORT();
#endif

#ifdef BDEBUG
#define BSQ_LANGUAGE_ABORT(MSG, F, L) HANDLE_BSQ_ABORT(MSG, F, L)
#else
#define BSQ_LANGUAGE_ABORT(MSG, F, L) HANDLE_BSQ_ABORT()
#endif

