//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#include "bsqcustom/bsqlist_decl.h"
#include "bsqcustom/bsqlist_ops.h"
//TODO: Stack defs here
//TODO: Queue defs here
#include "bsqcustom/bsqset_decl.h"
#include "bsqcustom/bsqset_ops.h"
#include "bsqcustom/bsqmap_decl.h"
#include "bsqcustom/bsqmap_ops.h"

#pragma once

#define GET_RC_OPS(TAG) (bsq_ops[GET_MIR_TYPE_POSITION(TAG)])

#define PARSER_INTERNAL_CHECK(C, M) { if(C) { printf("\"%s\" in %s on line %i\n", M, __FILE__, __LINE__); fflush(stdout); exit(1); } }
#define PARSER_PARSE_ERROR(M, P) BSQParseError(M, P->line, P->column, P->computeContext())

#define LEX_CFLOW(OP) if (OP) { return; }

namespace BSQ
{
class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

//%%STATIC_REGEX_DECLARE%%

//%%STATIC_INT_DECLARE%%

//%%EPHEMERAL_LIST_DECLARE
};
/*
class BSQParseError
{
public:
const char* msg;
const size_t line;
const std::string context;

BSQParseError(const char* msg, size_t line, size_t column, const std::string& context) : msg(msg), line(line), context(context) { ; }
};

enum APIFormatKind
{
    Invalid,

    Null,
    None,
    True,
    False,
    Int,
    BigInt,
    Float64,
    String,
    SafeString,
    ISOTime,
    UUID,
    LogicalTime,
    CryptoHash,
    Comma,
    Colon,
    Arrow,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    ListStart,
    ListEnd,
    MapStart,
    MapEnd,
    LParen,
    RParen,
    ResultOk,
    ResultErr,

    NAME_TOKEN,

    EOF_TOKEN,
    ERROR
};

template <BSQBufferEncoding enc, bool bmode>
class APITypeEncodingParser
{
public:
    APITypeEncodingParser(const std::string* data) { ; }

    std::string computeContext() { return "[INVALID]"; }

    APIFormatKind peekJSON() { return APIFormatKind::Invalid; }
    void pop() { ; }
    std::pair<const char*, const char*> read() { std::make_pair(nullptr, nullptr); }
};

class LexerRegexs
{
public:
    static std::regex whitespaceRe; 
    static std::regex commentRe;
    static std::regex intRe;
    static std::regex bigintRe;
    static std::regex floatRe;
    static std::regex stringRe;
    static std::regex typedStringRe;
    static std::regex isotimeRe;
    static std::regex uuidRe;
    static std::regex logicaltimeRe;
    static std::regex hashRe;

    static std::regex nameRe;

    static std::regex newlineRe;
};

template <bool bmode>
class APITypeEncodingParser<BSQBufferEncoding::UTF8, bmode>
{
private:
    const std::string* data;
    const char* pos;
    const char* max;

    APIFormatKind ctoken;
    const char* end;

    size_t line;

    void updateFilePos(const std::cmatch& m)
    {
        auto nl_begin = std::sregex_iterator(this->pos, this->pos + m.length(), LexerRegexs::newlineRe);
        auto nl_end = std::sregex_iterator();

        this->line += std::distance(nl_begin, nl_end);
    }

    void consumeWSAndComment() 
    {
        while(this->pos < this->max)
        {
            std::cmatch m;
            auto opos = this->pos;

            if (this->pos < this->max && std::regex_search(this->pos, this->max, m, LexerRegexs::whitespaceRe, std::regex_constants::match_continuous))
            {
                this->updateFilePos(m);
                this->pos += m.length();
            }

            if constexpr (bmode)
            {
                if (this->pos < this->max && std::regex_search(this->pos, this->max, m, LexerRegexs::commentRe, std::regex_constants::match_continuous))
                {
                    this->updateFilePos(m);
                    this->pos += m.length();
                }
            }

            if(this->pos == opos)
            {
                return;
            }
        }

        this->ctoken = APIFormatKind::EOF_TOKEN;
    }

    bool checkMatch(const std::regex& re, APIFormatKind token) 
    {
        std::cmatch m;
        bool mtch = std::regex_search(this->pos, this->max, m, LexerRegexs::whitespaceRe, std::regex_constants::match_continuous);
        if(mtch)
        {
            this->updateFilePos(m);

            this->ctoken = token;
            this->end = this->pos + m.length();
        }

        return mtch;
    }

    template <size_t n>
    bool checkLiteral(const char(&literal)[n], APIFormatKind token) 
    {
        bool mtch = (std::distance(this->pos, this->max) >= n) && std::equal(&literal, &literal + n, this->pos);
        if(mtch)
        {
            this->ctoken = token;
            this->end = this->pos + n;
        }

        return mtch;
    }

    void advance()
    {
        this->ctoken = APIFormatKind::Invalid;
        
        this->pos = this->end;
        this->end = nullptr;
    }

    void lexToken()
    {
        this->advance();
        this->consumeWSAndComment();

        if constexpr (bmode)
        {
            LEX_CFLOW(this->checkLiteral("none", APIFormatKind::None));
            LEX_CFLOW(this->checkLiteral("true", APIFormatKind::True));
            LEX_CFLOW(this->checkLiteral("false", APIFormatKind::False));

            LEX_CFLOW(this->checkMatch(LexerRegexs::intRe, APIFormatKind::Int));
            LEX_CFLOW(this->checkMatch(LexerRegexs::bigintRe, APIFormatKind::BigInt));
            LEX_CFLOW(this->checkMatch(LexerRegexs::floatRe, APIFormatKind::Float64));
            LEX_CFLOW(this->checkMatch(LexerRegexs::stringRe, APIFormatKind::String));
            LEX_CFLOW(this->checkMatch(LexerRegexs::typedStringRe, APIFormatKind::SafeString));
            LEX_CFLOW(this->checkMatch(LexerRegexs::isotimeRe, APIFormatKind::ISOTime));
            LEX_CFLOW(this->checkMatch(LexerRegexs::uuidRe, APIFormatKind::UUID));
            LEX_CFLOW(this->checkMatch(LexerRegexs::logicaltimeRe, APIFormatKind::LogicalTime));
            LEX_CFLOW(this->checkMatch(LexerRegexs::hashRe, APIFormatKind::CryptoHash));

            LEX_CFLOW(this->checkLiteral(",", APIFormatKind::Comma));
            LEX_CFLOW(this->checkLiteral(":", APIFormatKind::Colon));
            LEX_CFLOW(this->checkLiteral("=>", APIFormatKind::Arrow));

            LEX_CFLOW(this->checkLiteral("[", APIFormatKind::LBrack));
            LEX_CFLOW(this->checkLiteral("]", APIFormatKind::RBrack));
            LEX_CFLOW(this->checkLiteral("{", APIFormatKind::LBrace));
            LEX_CFLOW(this->checkLiteral("}", APIFormatKind::RBrace));

            LEX_CFLOW(this->checkLiteral("[|", APIFormatKind::ListStart));
            LEX_CFLOW(this->checkLiteral("|]", APIFormatKind::ListEnd));
            LEX_CFLOW(this->checkLiteral("{|", APIFormatKind::MapStart));
            LEX_CFLOW(this->checkLiteral("|}", APIFormatKind::MapEnd));
            LEX_CFLOW(this->checkLiteral("{|", APIFormatKind::MapStart));
            LEX_CFLOW(this->checkLiteral("|}", APIFormatKind::MapEnd));
            LEX_CFLOW(this->checkLiteral("(", APIFormatKind::LParen));
            LEX_CFLOW(this->checkLiteral(")", APIFormatKind::RParen));

            LEX_CFLOW(this->checkLiteral("ok(", APIFormatKind::ResultOk));
            LEX_CFLOW(this->checkLiteral("err(", APIFormatKind::ResultErr));

            LEX_CFLOW(this->checkMatch(LexerRegexs::nameRe, APIFormatKind::NAME_TOKEN));

            this->ctoken = APIFormatKind::ERROR;
        }
        else {
            LEX_CFLOW(this->checkLiteral("null", APIFormatKind::Null));
            LEX_CFLOW(this->checkLiteral("true", APIFormatKind::True));
            LEX_CFLOW(this->checkLiteral("false", APIFormatKind::False));

            LEX_CFLOW(this->checkMatch(LexerRegexs::intRe, APIFormatKind::Float64));
            LEX_CFLOW(this->checkMatch(LexerRegexs::floatRe, APIFormatKind::Float64));
            LEX_CFLOW(this->checkMatch(LexerRegexs::stringRe, APIFormatKind::String));

            LEX_CFLOW(this->checkLiteral(",", APIFormatKind::Comma));
            LEX_CFLOW(this->checkLiteral(":", APIFormatKind::Colon));

            LEX_CFLOW(this->checkLiteral("[", APIFormatKind::LBrack));
            LEX_CFLOW(this->checkLiteral("]", APIFormatKind::RBrack));
            LEX_CFLOW(this->checkLiteral("{", APIFormatKind::LBrace));
            LEX_CFLOW(this->checkLiteral("}", APIFormatKind::RBrace));

            this->ctoken = APIFormatKind::ERROR;
        }
    }

public:
    APITypeEncodingParser(const std::string* data) 
        : data(data), pos(data->c_str()), max(data->c_str() + data->size()), ctoken(APIFormatKind::Invalid), end(data->c_str()), line(1)
    { 
        this->lexToken();
    }

    std::string computeContext() 
    { 
        return "[INVALID]"; 
    }

    APIFormatKind peek() 
    {
        return this->ctoken;
    }

    void pop() 
    { 
        if(this->ctoken != APIFormatKind::EOF_TOKEN)
        {
            this->lexToken();
        }
    }

    std::pair<const char*, const char*> read() 
    {
        PARSER_INTERNAL_CHECK(this->ctoken != APIFormatKind::EOF_TOKEN && this->ctoken != APIFormatKind::ERROR, "BAD TOKEN");

        std::make_pair(this->pos, this->end); 
    }
};

template <BSQBufferEncoding enc, BSQBufferFormat fmt>
class APITypeParser
{
public:
    APITypeParser(const std::string* data) { ; }
};
*/
} // namespace BSQ
