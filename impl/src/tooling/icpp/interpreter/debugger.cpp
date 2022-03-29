//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "debugger.h"

DebuggerException::DebuggerException(DebuggerExceptionMode abortMode, BreakPoint eTime)
    : m_abortMode(abortMode), m_eTime(eTime)
{
    ;
}

DebuggerException::~DebuggerException()
{
    ;
}

DebuggerException DebuggerException::CreateAbortEndOfLog()
{
    return DebuggerException(DebuggerExceptionMode::EndOfReplay, {});
}

DebuggerException DebuggerException::CreateMoveToBP(BreakPoint eTime)
{
    return DebuggerException(DebuggerExceptionMode::MoveToBP, eTime);
}

DebuggerException DebuggerException::CreateErrorAbortRequest(BreakPoint eTime)
{
    return DebuggerException(DebuggerExceptionMode::ErrorPreTime, eTime);
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
    else if(opstr == "continue" || opstr == "c")
    {
        return std::make_pair(DebuggerCmd::Continue, opstr);
    }
    else if(opstr == "reverse step" || opstr == "rs")
    {
        return std::make_pair(DebuggerCmd::ReverseStep, opstr);
    }
    else if(opstr == "reverse into" || opstr == "ri")
    {
        return std::make_pair(DebuggerCmd::ReverseStepInto, opstr);
    }
    else if(opstr == "reverse continue" || opstr == "rc")
    {
        return std::make_pair(DebuggerCmd::ReverseContinue, opstr);
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
    printf("  (c)ontinue\n");
    printf("  (r)everse (s)tep\n");
    printf("  (r)everse (i)nto\n");
    printf("  (r)everse (c)ontinue\n");
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
    vv->dbg_getCFrame()->dbg_step_mode = StepMode::Step;
}

void dbg_processStepInto(Evaluator* vv)
{
    vv->dbg_getCFrame()->dbg_step_mode = StepMode::StepInto;
}

void dbg_processContinue(Evaluator* vv)
{
    for(int32_t i = 0; i < vv->dbg_getCPos(); ++i)
    {
        Evaluator::g_callstack[i].dbg_step_mode = StepMode::Run;
    }
}

void dbg_processReverseStep(Evaluator* vv)
{
    if(vv->dbg_getCFrame()->dbg_prevbp.isValid())
    {
        throw DebuggerException::CreateMoveToBP(vv->dbg_getCFrame()->dbg_prevbp);
    }
}

void dbg_processReverseStepInto(Evaluator* vv)
{
    if(vv->dbg_getCFrame()->dbg_prevreturnbp.first == -1)
    {
        if(vv->dbg_getCFrame()->dbg_prevbp.isValid())
        {
            throw DebuggerException::CreateMoveToBP(vv->dbg_getCFrame()->dbg_prevbp);
        }
    }
    else
    {
        if(vv->dbg_getCFrame()->dbg_prevreturnbp.first == vv->dbg_getCFrame()->dbg_currentline || vv->dbg_getCFrame()->dbg_prevreturnbp.first == vv->dbg_getCFrame()->dbg_prevbp.line)
        {
            throw DebuggerException::CreateMoveToBP(vv->dbg_getCFrame()->dbg_prevreturnbp.second);
        }
    }
}

void dbg_processReverseContinue(Evaluator* vv)
{
    if(vv->ttdBreakpoint_LastHit.isValid())
    {
        throw DebuggerException::CreateMoveToBP(vv->ttdBreakpoint_LastHit);
    }
}

void dbg_displayLocals(Evaluator* vv)
{
    std::string locals("**params**\n");
    const std::vector<BSQFunctionParameter>& params = vv->dbg_getCFrame()->invoke->params;

    for(size_t i = 0; i < params.size(); ++i)
    {
        auto binvoke = dynamic_cast<const BSQInvokeBodyDecl*>(vv->dbg_getCFrame()->invoke);
        auto val = Evaluator::evalParameterInfo(binvoke->paraminfo[i], vv->dbg_getCFrame()->scalarbase, vv->dbg_getCFrame()->mixedbase);
        
        locals += "  " + params[i].name + ": " + params[i].ptype->fpDisplay(params[i].ptype, val, DisplayMode::CmdDebug) + "\n";
    }

    if(!params.empty())
    {
        locals += "\n";
    }

    locals += "**locals**\n";
    const std::list<VariableHomeLocationInfo>& vhomeinfo = vv->dbg_getCFrame()->dbg_locals;
    for(auto iter = vhomeinfo.cbegin(); iter != vhomeinfo.cend(); ++iter)
    {
        const std::string& vname = iter->vname;
        auto isparam = std::find_if(params.cbegin(), params.cend(), [&vname](const BSQFunctionParameter& pp) {
            return pp.name == vname;
        }) != params.cend();

        if(!isparam)
        {
            auto val = vv->evalArgument(iter->location);
            locals += "  " + iter->vname + ": " + iter->vtype->fpDisplay(iter->vtype, val, DisplayMode::CmdDebug) + "\n";
        }
    }

    printf(locals.c_str());
    fflush(stdout);
}

void dbg_displayExp(Evaluator* vv, std::string vexp)
{
    xxxx;
}

void dbg_bpList(Evaluator* vv)
{
    std::string bps("**breakpoints**\n");
    for(size_t i = 0; i < vv->breakpoints.size(); ++i)
    {
        bps += vv->breakpoints[i].invk->srcFile + ":" + std::to_string(vv->breakpoints[i].line) + "\n";
    }

    printf(bps.c_str());
    fflush(stdout);
}

void dbg_bpAdd(Evaluator* vv, std::string bpstr)
{
    auto spos = bpstr.find(':');
    assert(spos != -1);

    std::string file = bpstr.substr(0, spos);
    std::string lstr = bpstr.substr(spos + 1);
    int64_t ll = std::strtol(&lstr[0], nullptr, 10);

    auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [&bpstr, ll](const BreakPoint& bp) {
        return bp.invk->name.ends_with(bpstr) && bp.line == ll;
    });

    if(bpc != 0)
    {
        printf("Breakpoint already set at position\n");
        fflush(stdout);
    }
    else
    {
        std::string ffile = xxxx;

        //find file/invoke with line

        vv->breakpoints.emplace_back(ffile, ll, 0);
    }
}

void dbg_bpDelete(Evaluator* vv, std::string bpstr)
{
    auto spos = bpstr.find(':');
    assert(spos != -1);

    std::string file = bpstr.substr(0, spos);
    std::string lstr = bpstr.substr(spos + 1);
    int64_t ll = std::strtol(&lstr[0], nullptr, 10);

    auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [&bpstr, ll](const BreakPoint& bp) {
        return bp.invk->name.ends_with(bpstr) && bp.line == ll;
    });

    if(bpc == 0)
    {
        printf("No breakpoints match the spec\n");
        fflush(stdout);
    }
    else if(bpc > 1)
    {
        printf("Ambigious breakpoint spec -- multiple files match\n");
        fflush(stdout);
    }
    else
    {
        auto ebp = std::remove_if(vv->breakpoints.begin(), vv->breakpoints.end(), [&bpstr, ll](const BreakPoint& bp) {
            return bp.invk->name.ends_with(bpstr) && bp.line == ll;
        });

        vv->breakpoints.erase(ebp, vv->breakpoints.end());
    }
}

void dbg_quit(Evaluator* vv)
{
    printf("Exiting debugging session...");
    exit(0);
}
