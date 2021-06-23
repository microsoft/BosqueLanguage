//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

IType* IType::jparse(json j)
{
    xxxx;
}

NoneType* NoneType::jparse(json j)
{
    return new NoneType("NSCore::None");
}

json NoneType::fuzz(RandGenerator& rnd) const
{
    return nullptr;
}

json NoneType::extract(ExtractionInfo* ex, z3::expr ctx) const
{
    return nullptr;
}

std::string NoneType::consprint(json j) const
{
    return "none";
}
