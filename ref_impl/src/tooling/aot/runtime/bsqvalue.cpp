//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
//
//TODO: we may want to do constexpr and statics for other literal tuples/records too
//

BSQTuple* BSQTuple::_empty = BSQRef::checkedIncrementFast<BSQTuple>(new BSQTuple({}));
BSQRecord* BSQRecord::_empty = BSQRef::checkedIncrementFast<BSQRecord>(new BSQRecord({}));
}
