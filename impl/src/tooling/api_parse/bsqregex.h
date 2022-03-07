//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

struct SingleCharRange
{
    CharCode low;
    CharCode high;
};

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
    const bool compliment;
    const std::vector<SingleCharRange> ranges;
    const StateID follow;

    NFAOptRange(StateID stateid, bool compliment, std::vector<SingleCharRange> ranges, StateID follow) : NFAOpt(stateid), compliment(compliment), ranges(ranges), follow(follow) {;}
    virtual ~NFAOptRange() {;}

    virtual void advance(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
    {
        auto chkrng = std::find_if(this->ranges.cbegin(), this->ranges.cend(), [c](const SingleCharRange& rr) {
            return (rr.low <= c && c <= rr.high);
        });

        if(!compliment) {
            if(chkrng != this->ranges.cend()) {
                nstates.push_back(this->follow);
            }
        }
        else {
            if(chkrng == this->ranges.cend()) {
                nstates.push_back(this->follow);
            }
        }
    }

    virtual std::pair<CharCode, StateID> generate(RandGenerator& rnd, const std::vector<NFAOpt*>& nfaopts) const override final
    {
        if(!compliment)
        {
            std::uniform_int_distribution<uint32_t> igen(0, this->ranges.size() - 1);
            auto ii = igen(rnd);

            auto range = this->ranges[ii];
            std::uniform_int_distribution<uint32_t> cgen(range.low, range.high);

            return std::make_pair((CharCode)cgen(rnd), this->follow);
        }
        else
        {
            uint32_t minrng = this->ranges.front().low == 0 ? 1 : 0;
            uint32_t maxrng = this->ranges.back().high == std::numeric_limits<CharCode>::max() ? this->ranges.size() - 1 : this->ranges.size();
            std::uniform_int_distribution<uint32_t> igen(minrng, maxrng);
            auto ii = igen(rnd);

            if(ii == 0)
            {
                auto range = this->ranges.front();
                std::uniform_int_distribution<uint32_t> cgen(0, range.low - 1);

                return std::make_pair((CharCode)cgen(rnd), this->follow);   
            }
            if(ii == this->ranges.size())
            {
                auto range = this->ranges.back();
                std::uniform_int_distribution<uint32_t> cgen(range.high + 1, std::numeric_limits<CharCode>::max());

                return std::make_pair((CharCode)cgen(rnd), this->follow);  
            }
            else
            {
                auto rangel = this->ranges[ii];
                auto ranger = this->ranges[ii + 1];
                assert(rangel.high + 1 < ranger.low); //should have merged them then

                std::uniform_int_distribution<uint32_t> cgen(rangel.high + 1, ranger.low - 1);
            
                return std::make_pair((CharCode)cgen(rnd), this->follow);
            }
        }
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
        std::uniform_int_distribution<uint32_t> cgen(32, 126);
        return std::make_pair((CharCode)cgen(rnd), this->follow);
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

    bool test(CharCodeIterator& cci) const
    {
        std::vector<StateID> cstates = { this->startstate };
        std::vector<StateID> nstates = { };

        while(cci.valid())
        {
            auto cc = cci.get();
            cci.advance();

            for(size_t i = 0; i < cstates.size(); ++i)
            {
                this->nfaopts[cstates[i]]->advance(cc, this->nfaopts, nstates);
            }

            std::sort(nstates.begin(), nstates.end());
            auto nend = std::unique(nstates.begin(), nstates.end());
            nstates.erase(nend, nstates.end());

            cstates = std::move(nstates);
            if(cstates.empty())
            {
                return false;
            }
        }

        return std::find(cstates.cbegin(), cstates.cend(), this->acceptstate) != cstates.cend();
    }

    std::optional<size_t> match(CharCodeIterator& cci) const
    {
        std::vector<StateID> cstates = { this->startstate };
        std::vector<StateID> nstates = { };

        while(cci.valid())
        {
            auto cc = cci.get();
            cci.advance();

            for(size_t i = 0; i < cstates.size(); ++i)
            {
                this->nfaopts[cstates[i]]->advance(cc, this->nfaopts, nstates);
            }

            std::sort(nstates.begin(), nstates.end());
            auto nend = std::unique(nstates.begin(), nstates.end());
            nstates.erase(nend, nstates.end());

            cstates = std::move(nstates);
            if(cstates.empty())
            {
                return std::nullopt;
            }

            if(std::find(cstates.cbegin(), cstates.cend(), this->acceptstate) != cstates.cend())
            {
                return std::make_optional(cci.distance());
            }
        }

        return std::nullopt;
    }

    std::optional<std::pair<size_t, size_t>> find(CharCodeIterator& cci) const
    {
        size_t rdist = cci.distance();
        std::vector<StateID> cstates = { this->startstate };
        std::vector<StateID> nstates = { };

        while(cci.valid())
        {
            auto cc = cci.get();
            cci.advance();

            for(size_t i = 0; i < cstates.size(); ++i)
            {
                this->nfaopts[cstates[i]]->advance(cc, this->nfaopts, nstates);
            }

            std::sort(nstates.begin(), nstates.end());
            auto nend = std::unique(nstates.begin(), nstates.end());
            nstates.erase(nend, nstates.end());

            cstates = std::move(nstates);
            if(cstates.empty())
            {
                //
                //TODO: this is a pretty slow way to search -- we probably want to do better in the future
                //
                cstates = { this->startstate };
                rdist++;
                cci.resetTo(rdist);
            }

            if(std::find(cstates.cbegin(), cstates.cend(), this->acceptstate) != cstates.cend())
            {
                return std::make_optional(std::make_pair(rdist, cci.distance() - rdist));
            }
        }

        return std::nullopt;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const = 0;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQCharRangeRe : public BSQRegexOpt
{
public:
    const bool compliment;
    const std::vector<SingleCharRange> ranges;

    BSQCharRangeRe(bool compliment, std::vector<SingleCharRange> ranges) : BSQRegexOpt(), compliment(compliment), ranges(ranges) {;}
    virtual ~BSQCharRangeRe() {;}

    static BSQCharRangeRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQCharClassDotRe : public BSQRegexOpt
{
public:
    BSQCharClassDotRe() : BSQRegexOpt() {;}
    virtual ~BSQCharClassDotRe() {;}

    static BSQCharClassDotRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQOptionalRe : public BSQRegexOpt
{
public:
    const BSQRegexOpt* opt;

    BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
    virtual ~BSQOptionalRe() {;}

    static BSQOptionalRe* parse(json j);
    virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
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
    virtual StateID compileReverse(StateID follows, std::vector<NFAOpt*>& states) const override final;
};

class BSQRegex
{
public:
    const std::string restr;
    const BSQRegexOpt* re;
    const NFA* nfare;
    const NFA* nfare_rev;

    BSQRegex(std::string restr, const BSQRegexOpt* re, NFA* nfare, NFA* nfare_rev): restr(restr), re(re), nfare(nfare), nfare_rev(nfare_rev) {;}
    ~BSQRegex() {;}

    static BSQRegex* jparse(json j);

    bool test(CharCodeIterator& cci)
    {
        return this->nfare->test(cci);
    }

    bool test(std::string& s)
    {
        StdStringCodeIterator siter(s);
        return this->nfare->test(siter);
    }

    std::optional<size_t> match(CharCodeIterator& cci)
    {
        return this->nfare->match(cci);
    }

    std::optional<size_t> match(std::string& s)
    {
        StdStringCodeIterator siter(s);
        return this->nfare->match(siter);
    }

    std::optional<std::pair<size_t, size_t>> find(CharCodeIterator& cci)
    {
        return this->nfare->find(cci);
    }

    std::optional<std::pair<size_t, size_t>> find(std::string& s)
    {
        StdStringCodeIterator siter(s);
        return this->nfare->find(siter);
    }

    std::optional<size_t> matchLast(CharCodeIterator& cci)
    {
        return this->nfare_rev->match(cci);
    }

    std::optional<size_t> matchLast(std::string& s)
    {
        StdStringCodeReverseIterator siter(s);
        return this->nfare_rev->match(siter);
    }

    std::optional<std::pair<size_t, size_t>> findLast(CharCodeIterator& cci)
    {
        return this->nfare->find(cci);
    }

    std::optional<std::pair<size_t, size_t>> findLast(std::string& s)
    {
        StdStringCodeReverseIterator siter(s);
        return this->nfare->find(siter);
    }

    std::string generate(RandGenerator& rnd)
    {
        return this->nfare->generate(rnd);
    }
};
