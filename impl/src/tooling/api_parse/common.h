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
#include <chrono>
#include <cstdio>

#include <string>
#include <regex>

#include <optional>
#include <vector>
#include <stack>
#include <map>

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
};

class StdStringCodeIterator : public CharCodeIterator
{
public:
    const std::string sstr;
    std::string::const_iterator curr;

    StdStringCodeIterator(std::string& sstr) : CharCodeIterator(), sstr(sstr), curr()
    {
        this->curr = this->sstr.cbegin();
    }
    
    virtual ~StdStringCodeIterator() {;}

    virtual bool valid() const override final
    {
        return this->curr != this->sstr.cend();
    }

    virtual void advance() override final
    {
        this->curr++;
    }

    virtual CharCode get() const override final
    {
        return *this->curr;
    }
};

