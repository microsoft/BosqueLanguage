


BSQRegexOpt* BSQRegexOpt::parse(json j)
{
   auto tag = j["tag"].get<std::string>();
    if(tag == "Literal")
    {
        return BSQLiteralRe::parse(j);
    }
    else if(tag == "CharClass")
    {
        return BSQCharClassRe::parse(j);
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

bool BSQLiteralRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if(!iteratorIsValid(&iter))
    {
        return false;
    }


    auto curr = this->litstr.cbegin();
    while(iteratorIsValid(&iter) && curr != this->litstr.cend())
    {
        if(iteratorGetUTF8Byte(&iter) != *curr)
        {
            return false;
        }

        incrementStringIterator_utf8byte(&iter);
        curr++;
    }

    if(curr != this->litstr.cend())
    {
        return false;
    }
    else
    {
        if(continuation.empty())
        {
            return !iteratorIsValid(&iter);
        }
        else 
        {
            std::vector<const BSQRegexOpt*> ncontinue(continuation.cbegin() + 1, continuation.cend());
            return continuation[0]->match(iter, ncontinue);
        }
    }
}

size_t BSQLiteralRe::mconsume() const
{
    return this->litstr.size();
}

BSQLiteralRe* BSQLiteralRe::parse(json j)
{
    auto litstr = j["litstr"].get<std::string>();
    std::vector<uint8_t> utf8;
    std::transform(litstr.cbegin(), litstr.cend(), std::back_inserter(utf8), [](const char cc) {
        return (uint8_t)cc;
    });

    return new BSQLiteralRe(j["restr"].get<std::string>(), j["escstr"].get<std::string>(), utf8);
}

bool BSQCharRangeRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if(!iteratorIsValid(&iter))
    {
        return false;
    }
    
    auto cp = iteratorGetCodePoint(&iter);
    incrementStringIterator_codePoint(&iter);
    if(this->low <= (uint32_t)cp && (uint32_t)cp <= this->high)
    {
        if(continuation.empty())
        {
            return !iteratorIsValid(&iter);
        }
        else
        {
            std::vector<const BSQRegexOpt*> ncontinue(continuation.cbegin() + 1, continuation.cend());
            return continuation[0]->match(iter, ncontinue);
        }
    }
    else
    {
        return false;
    }
}

size_t BSQCharRangeRe::mconsume() const
{
    return 1;
}

BSQCharRangeRe* BSQCharRangeRe::parse(json j)
{
    auto lb = j["lb"].get<uint64_t>();
    auto ub = j["ub"].get<uint64_t>();

    return new BSQCharRangeRe(lb, ub);
}

bool BSQCharClassRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if(!iteratorIsValid(&iter))
    {
        return false;
    }

    auto cp = iteratorGetCodePoint(&iter);
    incrementStringIterator_codePoint(&iter);

    if(this->kind == SpecialCharKind::Wildcard)
    {
        if(continuation.empty())
        {
            return !iteratorIsValid(&iter);
        }
        else
        {
            std::vector<const BSQRegexOpt*> ncontinue(continuation.cbegin() + 1, continuation.cend());
            return continuation[0]->match(iter, ncontinue);
        }
    }
    else
    {
        char ws_char[] = {' ', '\n', '\r', '\t' };
        if((cp == ' ') | (cp == '\n') | (cp == '\r') | (cp == '\t'))
        {
            if(continuation.empty())
            {
                return !iteratorIsValid(&iter);
            }
            else
            {
                std::vector<const BSQRegexOpt*> ncontinue(continuation.cbegin() + 1, continuation.cend());
                return continuation[0]->match(iter, ncontinue);
            }
        }
        else
        {
            return false;
        }
    }
}

size_t BSQCharClassRe::mconsume() const
{
    return 1;
}

BSQCharClassRe* BSQCharClassRe::parse(json j)
{
    auto kind = j["kind"].get<SpecialCharKind>();

    return new BSQCharClassRe(kind);
}

bool BSQStarRepeatRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if(continuation.empty())
    {
        if(!iteratorIsValid(&iter))
        {
            return true; //empty match at end 
        }
    }
    else
    {
        std::vector<const BSQRegexOpt*> nextcontinue(continuation.cbegin() + 1, continuation.cend());
        if(continuation[0]->match(iter, nextcontinue))
        {
            return true;
        }
    }

    auto mxiter = (BSQStringType::utf8ByteCount(iter.str) - iter.strpos) / std::max((size_t)1, this->mconsume());
    std::vector<const BSQRegexOpt*> matchcontinue;
    for(size_t i = 1; i < mxiter; ++i)
    {
        std::vector<const BSQRegexOpt*> rcontinue(matchcontinue.cbegin(), matchcontinue.cend());
        std::copy(continuation.cbegin(), continuation.cend(), std::back_inserter(rcontinue));

        if(this->opt->match(iter, rcontinue))
        {
            return true;
        }
        matchcontinue.push_back(this->opt);
    }
        
    return false;
}

size_t BSQStarRepeatRe::mconsume() const
{
    return 0;
}

BSQStarRepeatRe* BSQStarRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQStarRepeatRe(repeat);
}

bool BSQPlusRepeatRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    auto mxiter = (BSQStringType::utf8ByteCount(iter.str) - iter.strpos) / std::max((size_t)1, this->mconsume());
    std::vector<const BSQRegexOpt*> matchcontinue;
    for(size_t i = 1; i < mxiter; ++i)
    {
        std::vector<const BSQRegexOpt*> rcontinue(matchcontinue.cbegin(), matchcontinue.cend());
        std::copy(continuation.cbegin(), continuation.cend(), std::back_inserter(rcontinue));

        if(this->opt->match(iter, rcontinue))
        {
            return true;
        }
        matchcontinue.push_back(this->opt);
    }
        
    return false;
}

size_t BSQPlusRepeatRe::mconsume() const
{
    return this->opt->mconsume();
}

BSQPlusRepeatRe* BSQPlusRepeatRe::parse(json j)
{
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQPlusRepeatRe(repeat);
}

bool BSQRangeRepeatRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if (this->low == 0)
    {
        if (continuation.empty())
        {
            if (!iteratorIsValid(&iter))
            {
                return true; //empty match at end
            }
        }
        else
        {
            std::vector<const BSQRegexOpt *> nextcontinue(continuation.cbegin() + 1, continuation.cend());
            if (continuation[0]->match(iter, nextcontinue))
            {
                return true;
            }
        }
    }

    std::vector<const BSQRegexOpt*> matchcontinue;
    for(size_t i = (size_t)this->low; i <= (size_t)this->high; ++i)
    {
        std::vector<const BSQRegexOpt*> rcontinue(matchcontinue.cbegin(), matchcontinue.cend());
        std::copy(continuation.cbegin(), continuation.cend(), std::back_inserter(rcontinue));

        if(this->opt->match(iter, rcontinue))
        {
            return true;
        }
        matchcontinue.push_back(this->opt);
    }
        
    return false;
}

size_t BSQRangeRepeatRe::mconsume() const
{
    return this->opt->mconsume() * (size_t)this->low;
}

BSQRangeRepeatRe* BSQRangeRepeatRe::parse(json j)
{
    auto min = j["min"].get<uint64_t>();
    auto max = j["max"].get<uint64_t>();
    auto repeat = BSQRegexOpt::parse(j["repeat"]);

    return new BSQRangeRepeatRe(min, max, repeat);
}

bool BSQOptionalRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    if(continuation.empty())
    {
        if(!iteratorIsValid(&iter))
        {
            return true; //empty match at end 
        }
    }
    else
    {
        std::vector<const BSQRegexOpt*> nextcontinue(continuation.cbegin() + 1, continuation.cend());
        if(continuation[0]->match(iter, nextcontinue))
        {
            return true;
        }
    }

    return this->opt->match(iter, continuation);
}

size_t BSQOptionalRe::mconsume() const
{
    return 0;
}

BSQOptionalRe* BSQOptionalRe::parse(json j)
{
    auto opt = BSQRegexOpt::parse(j["opt"]);

    return new BSQOptionalRe(opt);
}

bool BSQAlternationRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    for(size_t i = 0; i < this->opts.size(); ++i)
    {
        if(this->opts[i]->match(iter, continuation))
        {
            return true;
        }
    }

    return false;
}

size_t BSQAlternationRe::mconsume() const
{
    std::vector<size_t> ml;
    std::transform(this->opts.cbegin(), this->opts.cend(), std::back_inserter(ml), [](const BSQRegexOpt* opt) {
        return opt->mconsume();
    });

    std::sort(ml.begin(), ml.end());
    return ml[0];
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

bool BSQSequenceRe::match(BSQStringIterator iter, const std::vector<const BSQRegexOpt*>& continuation) const
{
    std::vector<const BSQRegexOpt*> rcontinuation(this->opts.cbegin() + 1, this->opts.cend());
    std::copy(continuation.cbegin(), continuation.cend(), std::back_inserter(rcontinuation));

    return this->opts[0]->match(iter, rcontinuation);
}

size_t BSQSequenceRe::mconsume() const
{
    std::vector<size_t> ml;
    std::transform(this->opts.cbegin(), this->opts.cend(), std::back_inserter(ml), [](const BSQRegexOpt* opt) {
        return opt->mconsume();
    });

    return std::accumulate(ml.begin(), ml.end(), (size_t)0);
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
