//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

class NFAOpt
{
public:
    const StateID stateid;

    NFAOpt(StateID stateid) : stateid(stateid) {;}
    virtual ~NFAOpt() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const = 0;

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const = 0;
};

class NFAOptAccept : public NFAOpt
{
public:
    NFAOptAccept(StateID stateid) : NFAOpt(stateid) {;}
    virtual ~NFAOptAccept() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        return;
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        return std::make_pair(0, this->stateid);
    }
};

class NFAOptCharCode : public NFAOpt
{
public:
    const CharCode c;
    const StateID follow;

    NFAOptCharCode(StateID stateid, CharCode c, StateID follow) : NFAOpt(stateid), c(c), follow(follow) {;}
    virtual ~NFAOptCharCode() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        if(this->c == c)
        {
            nstates.push_back(this->follow);
        }
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        return std::make_pair(this->c, this->follow);
    }
};

class NFAOptRange : public NFAOpt
{
public:
    const CharCode low;
    const CharCode high;
    const StateID follow;

    NFAOptRange(StateID stateid, CharCode low, CharCode high, StateID follow) : NFAOpt(stateid), low(low), high(high), follow(follow) {;}
    virtual ~NFAOptRange() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        if(this->low <= c && c <= this->high)
        {
            nstates.push_back(this->follow);
        }
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        std::uniform_int_distribution<CharCode> cgen(this->low, this->high);
        return std::make_pair(cgen(rnd), this->follow);
    }
};

class NFAOptDot : public NFAOpt
{
public:
    const StateID follow;

    NFAOptDot(StateID stateid, StateID follow) : NFAOpt(stateid), follow(follow) {;}
    virtual ~NFAOptDot() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        nstates.push_back(this->follow);
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        std::uniform_int_distribution<CharCode> cgen(32, 126);
        return std::make_pair(cgen(rnd), this->follow);
    }
};

class NFAOptAlternate : public NFAOpt
{
public:
    const std::vector<StateID> follows;

    NFAOptAlternate(StateID stateid, std::vector<StateID> follows) : NFAOpt(stateid), follows(follows) {;}
    virtual ~NFAOptAlternate() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        for(size_t i = 0; i < this->follows.size(); ++i)
        {
            nfaopts[this->follows[i]]->advance(c, nfaopts, nstates);
        }
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        std::uniform_int_distribution<size_t> cgen(0, this->follows.size() - 1);
        auto choice = cgen(rnd);

        return nfaopts[choice]->generate(rnd, nfaopts);
    }
};

class NFAOptStar : public NFAOpt
{
public:
    const StateID matchfollow;
    const StateID skipfollow;

    NFAOptStar(StateID stateid, StateID matchfollow, StateID skipfollow) : NFAOpt(stateid), matchfollow(matchfollow), skipfollow(skipfollow) {;}
    virtual ~NFAOptStar() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        nfaopts[this->matchfollow]->advance(c, nfaopts, nstates);
        nfaopts[this->skipfollow]->advance(c, nfaopts, nstates);
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        std::uniform_int_distribution<size_t> cgen(0, 2);
        auto choice = cgen(rnd);
        
        return nfaopts[choice != 0 ? this->matchfollow : this->skipfollow]->generate(rnd, nfaopts);
    }
};

class NFA
{
public:
    const StateID startstate;
    const StateID acceptstate;

    const std::vector<NFAOpt*> nfaopts;

    NFA(StateID startstate, StateID acceptstate, std::vector<NFAOpt*> nfaopts) : startstate(startstate), acceptstate(acceptstate), nfaopts(nfaopts) 
    {
        ;
    }
    
    ~NFA() 
    {
        for(size_t i = 0; i < this->nfaopts.size(); ++i)
        {
            delete this->nfaopts[i];
        }
    }

    bool match(CharCodeIterator& cci) const
    {
        std::vector<StateID> cstates = { this->startstate };
        std::vector<StateID> nstates = { };

        while(cci.valid())
        {
            auto cc = cci.get();
            for(size_t i = 0; i < cstates.size(); ++i)
            {
                this->nfaopts[cstates[i]]->advance(cc, this->nfaopts, nstates);
            }

            std::sort(nstates.begin(), nstates.end());
            auto nend = std::unique(nstates.begin(), nstates.end());
            nstates.erase(nend, nstates.end());

            cstates = std::move(nstates);
        }

        return std::find(cstates.cbegin(), cstates.cend(), this->acceptstate) != cstates.cend();
    }

    std::string generate(RandGenerator& rnd) const
    {
        std::vector<CharCode> rr;
        StateID cstate = this->startstate;

        while(cstate != this->acceptstate)
        {
            auto adv = this->nfaopts[cstate]->generate(rnd, this->nfaopts);
            rr.push_back(adv.first);
            cstate = adv.second;
        }

        std::string rstr;
        std::transform(rr.cbegin(), rr.cend(), std::back_inserter(rstr), [](CharCode cc) {
            return (uint8_t)cc;
        });

        return rstr;
    }
};

class BSQRegexOpt
{
public:
    BSQRegexOpt() {;}
    virtual ~BSQRegexOpt() {;}

    static BSQRegexOpt* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const = 0;
};

class BSQLiteralRe : public BSQRegexOpt
{
public:
    const std::string litstr;
    const std::vector<uint8_t> utf8codes;

    BSQLiteralRe(std::string litstr, std::vector<uint8_t> utf8codes) : BSQRegexOpt(), litstr(litstr), utf8codes(utf8codes) {;}
    virtual ~BSQLiteralRe() {;}

    static BSQLiteralRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQCharRangeRe : public BSQRegexOpt
{
public:
    const uint64_t low;
    const uint64_t high;

    BSQCharRangeRe(uint64_t low, uint64_t high) : BSQRegexOpt(), low(low), high(high) {;}
    virtual ~BSQCharRangeRe() {;}

    static BSQCharRangeRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQCharClassDotRe : public BSQRegexOpt
{
public:
    BSQCharClassDotRe() : BSQRegexOpt() {;}
    virtual ~BSQCharClassDotRe() {;}

    static BSQCharClassDotRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQStarRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQStarRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}

    virtual ~BSQStarRepeatRe() 
    {
        delete this->opt;
    }

    static BSQStarRepeatRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQPlusRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQPlusRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    
    virtual ~BSQPlusRepeatRe()
    {
        delete this->opt;
    }

    static BSQPlusRepeatRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQRangeRepeatRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;
    const uint8_t low;
    const uint8_t high;

    BSQRangeRepeatRe(uint8_t low, uint8_t high, const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt), low(low), high(high) {;}
    
    virtual ~BSQRangeRepeatRe() 
    {
        delete this->opt;
    }

    static BSQRangeRepeatRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQOptionalRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQOptionalRe() {;}

    static BSQOptionalRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQAlternationRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQAlternationRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}

    virtual ~BSQAlternationRe()
    {
        for(size_t i = 0; i < this->opts.size(); ++i)
        {
            delete this->opts[i];
        }
    }

    static BSQAlternationRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQSequenceRe : public BSQRegexOpt
{
public:
    const std::vector<const BSQRegexOpt*> opts;

    BSQSequenceRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}

    virtual ~BSQSequenceRe()
    {
        for(size_t i = 0; i < this->opts.size(); ++i)
        {
            delete this->opts[i];
        }
    }

    static BSQSequenceRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQRegex
{
public:
    const std::string restr;
    const BSQRegexOpt* re;
    const NFA* nfare;

    BSQRegex(std::string restr, const BSQRegexOpt* re, NFA* nfare): restr(restr), re(re), nfare(nfare) {;}
    ~BSQRegex() {;}

    static BSQRegex* jparse(json j);

    bool match(CharCodeIterator& cci)
    {
        return this->nfare->match(cci);
    }

    bool match(std::string& s)
    {
        StdStringCodeIterator siter(s);
        return this->nfare->match(siter);
    }

    std::string generate(RandGenerator& rnd)
    {
        return this->nfare->generate(rnd);
    }
};
