//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "debugger.h"

DebuggerException::DebuggerException(uint32_t abortCode, int64_t optEventTime, int64_t optMoveMode, const char* staticAbortMessage)
    : m_abortCode(abortCode), m_optEventTime(optEventTime), m_optMoveMode(optMoveMode), m_staticAbortMessage(staticAbortMessage)
{
    ;
}

DebuggerException::~DebuggerException()
{
    ;
}

DebuggerException DebuggerException::CreateAbortEndOfLog(const char* staticMessage)
{
    return DebuggerException(1, -1, 0, staticMessage);
}

DebuggerException DebuggerException::CreateTopLevelAbortRequest(int64_t targetEventTime, int64_t moveMode, const char* staticMessage)
{
    return DebuggerException(2, targetEventTime, moveMode, staticMessage);
}

DebuggerException DebuggerException::CreateUncaughtExceptionAbortRequest(int64_t targetEventTime, const char* staticMessage)
{
    return DebuggerException(3, targetEventTime, 0, staticMessage);
}

bool DebuggerException::IsEndOfLog() const
{
    return this->m_abortCode == 1;
}

bool DebuggerException::IsEventTimeMove() const
{
    return this->m_abortCode == 2;
}

bool DebuggerException::IsTopLevelException() const
{
    return this->m_abortCode == 3;
}

int64_t DebuggerException::GetTargetEventTime() const
{
    return this->m_optEventTime;
}

int64_t DebuggerException::GetMoveMode() const
{
    return this->m_optMoveMode;
}

const char* DebuggerException::GetStaticAbortMessage() const
{
    return this->m_staticAbortMessage;
}

std::pair<DebuggerCmd, std::string> dbg_parseDebuggerCmd(Evaluator* vv)
{
    std::string opstr;
    int cc = 0;
    int hpos = vv->dbg_history.size() - 1;

    do
    {
        printf("> ");
        fflush(stdout);

        cc = std::getchar();
        if(opstr.empty() && cc == '.')
        {
            if(vv->dbg_history.size() != 0)
            {
                return vv->dbg_history.front();
            }
            else
            {
                printf("No debug action history...\n");
                fflush(stdout);
            }
        }
        else if(cc == 127)
        {
            if(!opstr.empty())
            {
                std::string outstr = std::string("> ") + opstr.substr(0, opstr.size() - 1);
                printf("\33[2K\r%s", outstr.c_str());
                fflush(stdout);
            }
        }
        else
        {
            opstr.push_back(cc);
        }
    } while (cc != '\n');


    if(opstr == "help")
    {
        return std::make_pair(DebuggerCmd::Help, opstr);
    }
    else if(opstr == "print" || opstr == "p")
    {
        return std::make_pair(DebuggerCmd::PrintFunction, opstr);
    }
    else if(opstr == "stack")
    {
        return std::make_pair(DebuggerCmd::CallStack, opstr);
    }
    else if(opstr == "locals" || opstr == "l")
    {
        return std::make_pair(DebuggerCmd::LocalDisplay, opstr);
    }
    else if(opstr == "step" || opstr == "s")
    {
        return std::make_pair(DebuggerCmd::Step, opstr);
    }
    else if(opstr == "into" || opstr == "i")
    {
        return std::make_pair(DebuggerCmd::StepInto, opstr);
    }
    else if(opstr == "reverse step" || opstr == "rs")
    {
        return std::make_pair(DebuggerCmd::ReverseStep, opstr);
    }
    else if(opstr == "reverse into" || opstr == "ri")
    {
        return std::make_pair(DebuggerCmd::ReverseStepInto, opstr);
    }
    else if(opstr == "quit" || opstr == "q")
    {
        return std::make_pair(DebuggerCmd::Quit, opstr);
    }
    else if(opstr.starts_with("display ") || opstr.starts_with("d "))
    {
        std::regex pfx("^(display|d)(\\s+)");
        std::smatch matchpfx;
        std::regex_match(opstr, matchpfx, pfx);

        std::string path = opstr.substr(matchpfx.str(0).size());

        std::regex pathx("^(([*][0-9]+)|([$]?[a-zA-Z]+))(([.][a-zA-Z0-9]+)?([\\[]([0-9]+|[\\\"]([^\\\"])+[\\\"])+[\\]])*)*$");
        std::smatch matchpath;
        auto pathok = std::regex_match(path, matchpath, pathx);
        if(pathok)
        {
            printf("Bad display argument...\n");
            fflush(stdout);

            return std::make_pair(DebuggerCmd::Invalid, path);
        }

        return std::make_pair(DebuggerCmd::ExpDisplay, path);
    }
    else if(opstr.starts_with("breakpoint ") || opstr.starts_with("b "))
    {
        std::regex pfx("^(breakpoint|b)(\\s+)");
        std::smatch matchpfx;
        std::regex_match(opstr, matchpfx, pfx);

        std::string actionstr = opstr.substr(matchpfx.str(0).size());

        std::regex afx("^(list|add|delete)(\\s+)");
        std::smatch matchaction;
        bool actionok = std::regex_match(actionstr, matchaction, afx);
        if(!actionok)
        {
            printf("Bad breakpoint action...\n");
            fflush(stdout);

            return std::make_pair(DebuggerCmd::Invalid, opstr);
        }

        std::string bpstr = actionstr.substr(matchaction.str(0).size());

        std::regex bpfx("^[a-zA-Z0-9_/]+:(0-9)+");
        std::smatch matchbp;
        bool bpok = std::regex_match(bpstr, matchbp, bpfx);
        if(!bpok)
        {
            printf("Bad breakpoint location...\n");
            fflush(stdout);

            return std::make_pair(DebuggerCmd::Invalid, bpstr);
        }

        if(opstr.starts_with("list"))
        {
            return std::make_pair(DebuggerCmd::ListBreakPoint, bpstr);
        }
        else if(opstr.starts_with("add"))
        {
            return std::make_pair(DebuggerCmd::AddBreakPoint, bpstr);
        }
        else
        {
            return std::make_pair(DebuggerCmd::DeleteBreakpoint, bpstr);
        }
    }
    else
    {
        return std::make_pair(DebuggerCmd::Help, "");
    }
}

void dbg_printHelp(std::string ofop)
{
    printf("Available commands are:\n");
    printf("----\n");
    printf("  (p)rint\n");
    printf("  stack\n");
    printf("----\n");
    printf("  (s)tep\n");
    printf("  (i)nto\n");
    printf("  (r)everse (s)tep\n");
    printf("  (r)everse (i)nto\n");
    printf("----\n");
    printf("  (l)ocals\n");
    printf("  (d)isplay vexp\n");
    printf("    (var|*id)(.name([literal])*)*\n");
    printf("----\n");
    printf("  (b)reakpoint list\n");
    printf("  (b)reakpoint add|delete bp\n");
    printf("    file:line");
    printf("  (q)uit\n");
}

void dbg_printFunction(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();

    std::string contents = MarshalEnvironment::g_srcMap.find(cframe->invoke->srcFile)->second;
    
    int64_t cpos = 0;
    for(int64_t i = 0; i <= cframe->invoke->sinfoEnd.line; ++i)
    {
        int64_t lcpos = cpos;
        while(cpos < contents.size() && contents[cpos] != '\n')
        {
            cpos++;
        }
        cpos++;

        if(i >= cframe->invoke->sinfoStart.line)
        {
            std::string line = contents.substr(lcpos, cpos);
            printf("%s", line.c_str());
        }
    }

    fflush(stdout);
}

void dbg_displayStack(Evaluator* vv)
{
    printf("++++\n");

    for(int32_t i = 0; i < vv->dbg_getCPos(); ++i)
    {
        printf("  %s\n", Evaluator::g_callstack[i].invoke->name.c_str());
    }

    printf("----\n");
    fflush(stdout);
}

void dbg_processStep(Evaluator* vv)
{
    vv->dbg_getCFrame()->dbg_mode_current = StepMode::Step;
}

void dbg_processStepInto(Evaluator* vv)
{
    vv->dbg_getCFrame()->dbg_mode_current = StepMode::StepInto;
}

void dbg_processReverseStep(Evaluator* vv)
{
    xxxx;
}

void dbg_processReverseStepInto(Evaluator* vv)
{
    xxxx;
}

void dbg_displayLocals(Evaluator* vv)
{
    xxxx;
}

void dbg_displayExp(Evaluator* vv, std::string vexp)
{
    xxxx;
}

void dbg_bpList(Evaluator* vv)
{
    xxxx;
}

void dbg_bpAdd(Evaluator* vv, std::string bpstr)
{
    xxxx;
}

void dbg_bpDelete(Evaluator* vv, std::string bpstr)
{
    xxxx;
}

void dbg_quit(Evaluator* vv)
{
    printf("Exiting debugging session...");
    exit(0);
}
