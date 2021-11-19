//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <cstdlib>
#include <string>

#include "json.hpp"
typedef nlohmann::json json;

enum class SpecialCharKind 
{
    Wildcard = 0x0,
    WhiteSpace
};

class BSQRegexOpt
{
public:
    BSQRegexOpt() {;}
    virtual ~BSQRegexOpt() {;}

    //
    //TODO: this is super inefficient but for now we just want it to run on small strings and regexs-- :(
    //      We will support matchTotal, matchMin, and matchMax as API ops rather than trying to do clever greedy lazy on operators and implicit defaults things
    //
    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const = 0;
    virtual size_t mconsume() const = 0;

    static BSQRegexOpt* parse(json j);
};

class BSQLiteralRe : public BSQRegexOpt
{
public:
    const std::string restr;
    const std::string escstr;
    const std::vector<uint8_t> litstr;

    BSQLiteralRe(std::string restr, std::string escstr, std::vector<uint8_t> litstr) : BSQRegexOpt(), restr(restr), escstr(escstr), litstr(litstr) {;}
    virtual ~BSQLiteralRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQLiteralRe* parse(json j);
};

class BSQCharRangeRe : public BSQRegexOpt
{
public:
    const uint64_t low;
    const uint64_t high;

    BSQCharRangeRe(uint64_t low, uint64_t high) : BSQRegexOpt(), low(low), high(high) {;}
    virtual ~BSQCharRangeRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQCharRangeRe* parse(json j);
};

class BSQCharClassRe : public BSQRegexOpt
{
public:
    const SpecialCharKind kind;

    BSQCharClassRe(SpecialCharKind kind) : BSQRegexOpt(), kind(kind) {;}
    virtual ~BSQCharClassRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQCharClassRe* parse(json j);
};

class BSQStarRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQStarRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQStarRepeatRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQStarRepeatRe* parse(json j);
};

class BSQPlusRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQPlusRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQPlusRepeatRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQPlusRepeatRe* parse(json j);
};

class BSQRangeRepeatRe : public BSQRegexOpt
{
public:
    const uint32_t low;
    const uint32_t high;
    const BSQRegexOpt* opt;

    BSQRangeRepeatRe(uint32_t low, uint32_t high, const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt), low(low), high(high) {;}
    virtual ~BSQRangeRepeatRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQRangeRepeatRe* parse(json j);
};

class BSQOptionalRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQOptionalRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQOptionalRe* parse(json j);
};

class BSQAlternationRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQAlternationRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQAlternationRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQAlternationRe* parse(json j);
};

class BSQSequenceRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQSequenceRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}
    virtual ~BSQSequenceRe() {;}

    virtual bool match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const override final;
    virtual size_t mconsume() const override final;

    static BSQSequenceRe* parse(json j);
};

class BSQRegex
{
public:
    const std::string restr;
    const BSQRegexOpt* re;

    BSQRegex(std::string restr, const BSQRegexOpt* re): restr(restr), re(re) {;}
    ~BSQRegex() {;}
};