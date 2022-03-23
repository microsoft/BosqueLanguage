//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#ifdef BSQ_DEBUG_BUILD

#include "op_eval.h"

std::pair<DebuggerCmd, std::string> parseDebuggerCmd(Evaluator* vv)
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
    else if(opstr == "print")
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
        std::cmatch matchpfx;
        auto pfxok = std::regex_match(opstr.c_str(), matchpfx, pfx);
        if(!mpfx)
        {
            xxxx;
        }

        std::string path = ;

        std::regex pathx("^[a-zA-Z*$][a-zA-Z0-9._\\[\\]\\\\\\\"]$");
        std::cmatch matchpath;
        auto pathok = std::regex_match(opstr.c_str(), matchpath, pathx);
        if(pathok)
        {
            xxxx;
        }

        std::string path = opstr.substr(opstr.starts_with("display ") ? 7 : 1);

        return std::make_pair(DebuggerCmd::ExpDisplay, opstr);
    }
    else
    {
        return std::make_pair(DebuggerCmd::Help, "");
    }
}

void printHelp(std::string ofop)
{

}

void stepAction(Evaluator* vv)
{
    
}

#endif
