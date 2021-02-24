//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqkeyvalues.h"

namespace BSQ
{
    BSQBigInt BSQBigInt::negate(const BSQBigInt& v)
    {
        return BSQBigInt{nullptr, -v.simpleint};
    }

    bool BSQBigInt::eq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return l.simpleint == r.simpleint;
    }

    bool BSQBigInt::lt(const BSQBigInt& l, const BSQBigInt& r)
    {
        return l.simpleint < r.simpleint;
    }

    BSQBigInt BSQBigInt::add(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint + r.simpleint};
    }

    BSQBigInt BSQBigInt::sub(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint - r.simpleint};
    }

    BSQBigInt BSQBigInt::mult(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint * r.simpleint};
    }

    BSQBigInt BSQBigInt::div(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint / r.simpleint};
    }

    BSQBigInt BSQBigInt::mod(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint % r.simpleint};
    }
}
