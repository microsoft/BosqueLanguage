//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "debugger.h"

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
    xxxx;
}

void dbg_displayStack(Evaluator* vv)
{
    xxxx;
}

void dbg_processStep(Evaluator* vv)
{
    xxxx;
}

void dbg_processStepInto(Evaluator* vv)
{
    xxxx;
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
