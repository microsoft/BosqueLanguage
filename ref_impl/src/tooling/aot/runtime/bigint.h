//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <cstdint>

//A big integer class for supporting Bosque -- right now it does not do much
class BigInt
{
    //TODO: want to refcount this 

public:
    BigInt() { ; }
    BigInt(int64_t value) { ; }
    BigInt(const char* bigstr) { ; }

    ~BigInt()
    {
        this->release();
    }

    size_t hash() const
    {
        return 0;
    }

    BigInt* copy() const
    {
        return nullptr;
    }

    void release()
    {
        ;
    }

    bool isZero() const
    {
        return false;
    }

    BigInt* negate() const
    {
        return nullptr;
    }

    static bool eq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool neq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool lt(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool lteq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

     static bool gt(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool gteq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static BigInt* add(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* sub(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* mult(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* div(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* mod(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }
};
