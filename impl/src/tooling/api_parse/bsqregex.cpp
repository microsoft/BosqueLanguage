//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqregex.h"

BSQRegexOpt* BSQRegexOpt::parse(json j)
{
   auto tag = j["tag"].get<std::string>();
    if(tag == "Literal")
    {
        return BSQLiteralRe::parse(j);
    }
    else if(tag == "CharClassDot")
    {
        return BSQCharClassDotRe::parse(j);
    }
    else if(tag == "CharRange")
    {
        return BSQCharRangeRe::parse(j);
    }
    else if(tag == "StarRepeat")
    {
        return BSQStarRepeatRe::parse(j);
    }
    else if(tag == "PlusRepeat")
    {
        return BSQPlusRepeatRe::parse(j);
    }
    else if(tag == "RangeRepeat")
    {
        return BSQRangeRepeatRe::parse(j);
    }
    else if(tag == "Optional")
    {
        return BSQOptionalRe::parse(j);
    }
    else if(tag == "Alternation")
    {
        return BSQAlternationRe::parse(j);
    }
    else
    {
        return BSQSequenceRe::parse(j);
    }
}

BSQLiteralRe* BSQLiteralRe::parse(json j)
{
    auto litstr = j["litstr"].get<std::string>();
    std::vector<uint8_t> utf8;
    std::transform(litstr.cbegin(), litstr.cend(), std::back_inserter(utf8), [](const char cc) {
        //TODO: this is ascii only
        return (uint8_t)cc;
    });

    return new BSQLiteralRe(litstr, utf8);
}

StateID BSQLiteralRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    for(int64_t i = this->utf8codes.size() - 1; i >= 0; --i)
    {
        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptCharCode(thisstate, this->utf8codes[i], follows));

        follows = thisstate;
    }

    return follows;
}

StateID BSQLiteralRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    for(int64_t i = 0; i < this->utf8codes.size(); ++i)
    {
        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptCharCode(thisstate, this->utf8codes[i], follows));

        follows = thisstate;
    }

    return follows;
}

BSQCharRangeRe* BSQCharRangeRe::parse(json j)
{
    const bool compliment = j["compliment"].get<bool>();

    std::vector<SingleCharRange> ranges;
    auto jranges = j["range"];
    std::transform(jranges.cbegin(), jranges.cend(), std::back_inserter(ranges), [](const json& rv) {
        auto lb = rv["lb"].get<CharCode>();
        auto ub = rv["ub"].get<CharCode>();

        return SingleCharRange{lb, ub};
    });

    return new BSQCharRangeRe(compliment, ranges);
}

StateID BSQCharRangeRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptRange(thisstate, this->compliment, this->ranges, follows));

    return thisstate;
}

StateID BSQCharRangeRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptRange(thisstate, this->compliment, this->ranges, follows));

    return thisstate;
}

BSQCharClassDotRe* BSQCharClassDotRe::parse(json j)
{
    return new BSQCharClassDotRe();
}

StateID BSQCharClassDotRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptDot(thisstate, follows));

    return thisstate;
}

StateID BSQCharClassDotRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptDot(thisstate, follows));

    return thisstate;
}

BSQStarRepeatRe* BSQStarRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQStarRepeatRe(repeat);
}

StateID BSQStarRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(nullptr); //placeholder

    auto optfollows = this->opt->compile(follows, states);
    states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

    return thisstate;
}

StateID BSQStarRepeatRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(nullptr); //placeholder

    auto optfollows = this->opt->compileReverse(follows, states);
    states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

    return thisstate;
}

BSQPlusRepeatRe* BSQPlusRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQPlusRepeatRe(repeat);
}

StateID BSQPlusRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(nullptr); //placeholder

    auto optfollows = this->opt->compile(follows, states);
    states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

    return this->opt->compile(thisstate, states);
}

StateID BSQPlusRepeatRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto thisstate = (StateID)states.size();
    states.push_back(nullptr); //placeholder

    auto optfollows = this->opt->compileReverse(follows, states);
    states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

    return this->opt->compile(thisstate, states);
}

BSQRangeRepeatRe* BSQRangeRepeatRe::parse(json j)
{
    auto min = j["min"].get<uint8_t>();
    auto max = j["max"].get<uint8_t>();
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQRangeRepeatRe(min, max, repeat);
}

StateID BSQRangeRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto followfinal = follows;
    for(int64_t i = this->high; i > this->low; --i)
    {
        auto followopt = this->opt->compile(follows, states);

        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptAlternate(thisstate, { followopt, followfinal }));

        follows = thisstate;
    }

    for(int64_t i = this->low; i > 0; --i)
    {
        follows = this->opt->compile(follows, states);
    }

    return follows;
}

StateID BSQRangeRepeatRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto followfinal = follows;
    for(int64_t i = this->high; i > this->low; --i)
    {
        auto followopt = this->opt->compileReverse(follows, states);

        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptAlternate(thisstate, { followopt, followfinal }));

        follows = thisstate;
    }

    for(int64_t i = this->low; i > 0; --i)
    {
        follows = this->opt->compileReverse(follows, states);
    }

    return follows;
}

BSQOptionalRe* BSQOptionalRe::parse(json j)
{
    auto opt = BSQRegexOpt::parse(j["opt"]);

    return new BSQOptionalRe(opt);
}

StateID BSQOptionalRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto followopt = this->opt->compile(follows, states);

    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptAlternate(thisstate, { followopt, follows }));

    return thisstate;
}

StateID BSQOptionalRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    auto followopt = this->opt->compileReverse(follows, states);

    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptAlternate(thisstate, { followopt, follows }));

    return thisstate;
}

BSQAlternationRe* BSQAlternationRe::parse(json j)
{
    std::vector<const BSQRegexOpt*> opts;
    auto jopts = j["opts"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](json arg) {
        return BSQRegexOpt::parse(arg);
    });

    return new BSQAlternationRe(opts);
}

StateID BSQAlternationRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    std::vector<StateID> followopts;
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        followopts.push_back(this->opts[i]->compile(follows, states));
    }

    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptAlternate(thisstate, followopts));

    return thisstate;
}

StateID BSQAlternationRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    std::vector<StateID> followopts;
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        followopts.push_back(this->opts[i]->compileReverse(follows, states));
    }

    auto thisstate = (StateID)states.size();
    states.push_back(new NFAOptAlternate(thisstate, followopts));

    return thisstate;
}

BSQSequenceRe* BSQSequenceRe::parse(json j)
{
    std::vector<const BSQRegexOpt*> elems;
    auto jopts = j["elems"];
    std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(elems), [](json arg) {
        return BSQRegexOpt::parse(arg);
    });

    return new BSQSequenceRe(elems);
}

StateID BSQSequenceRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
{
    for(int64_t i = this->opts.size() - 1; i >= 0; --i)
    {
        follows = this->opts[i]->compile(follows, states);
    }

    return follows;
}

StateID BSQSequenceRe::compileReverse(StateID follows, std::vector<NFAOpt*>& states) const
{
    for(int64_t i = 0; i < this->opts.size(); ++i)
    {
        follows = this->opts[i]->compileReverse(follows, states);
    }

    return follows;
}

BSQRegex* BSQRegex::jparse(json j)
{
    auto restr = j["restr"].get<std::string>();
    auto bsqre = BSQRegexOpt::parse(j["re"]);

    std::vector<NFAOpt*> nfastates = { new NFAOptAccept(0) };
    auto nfastart = bsqre->compile(0, nfastates);

    std::vector<NFAOpt*> nfastates_rev = { new NFAOptAccept(0) };
    auto nfastart_rev = bsqre->compileReverse(0, nfastates);

    auto nfare = new NFA(nfastart, 0, nfastates);
    auto nfare_rev = new NFA(nfastart_rev, 0, nfastates_rev);

    return new BSQRegex(restr, bsqre, nfare, nfare_rev);
}
