//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "common.h"

namespace BSQ
{
void bsqassert(bool cond, const char* msg, const char* file, int32_t line)
{
    if (!cond)
    {
        printf("\"%s\" in %s on line %i\n", msg, file, line); exit(1);
    }
}
} // namespace BSQ
