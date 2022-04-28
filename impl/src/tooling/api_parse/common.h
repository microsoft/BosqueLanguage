//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <cstdio>

#include <string>
#include <regex>
#include <optional>

#include <set>

#include <random>
typedef std::default_random_engine RandGenerator;

#include "json.hpp"
typedef nlohmann::json json;

typedef char CharCode;
typedef size_t StateID;

class CharCodeIterator
{
public:
    CharCodeIterator() {;}
    virtual ~CharCodeIterator() {;}

    virtual bool valid() const = 0;
    virtual void advance() = 0;

    virtual CharCode get() const = 0;

    virtual size_t distance() const = 0;
    virtual void resetTo(size_t distance) = 0;
};

class StdStringCodeIterator : public CharCodeIterator
{
public:
    const std::string sstr;
    int64_t curr;

    StdStringCodeIterator(std::string& sstr) : CharCodeIterator(), sstr(sstr), curr(0) {;}
    virtual ~StdStringCodeIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != this->sstr.size();
    }

    virtual void advance() override final
    {
        this->curr++;
    }

    virtual CharCode get() const override final
    {
        return this->sstr[this->curr];
    }

    virtual size_t distance() const override final
    {
        return this->curr;
    }

    virtual void resetTo(size_t distance) override final
    {
        this->curr = distance;
    }
};

class StdStringCodeReverseIterator : public CharCodeIterator
{
public:
    const std::string sstr;
    int64_t curr;

    StdStringCodeReverseIterator(std::string& sstr) : CharCodeIterator(), sstr(sstr), curr(sstr.size() - 1) {;}
    virtual ~StdStringCodeReverseIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != -1;
    }

    virtual void advance() override final
    {
        this->curr--;
    }

    virtual CharCode get() const override final
    {
        return this->sstr[this->curr];
    }

    virtual size_t distance() const override final
    {
        return (this->sstr.size() - 1) - this->curr;
    }

    virtual void resetTo(size_t distance) override final
    {
        this->curr = distance;
    }
};

