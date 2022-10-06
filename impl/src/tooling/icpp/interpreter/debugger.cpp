//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "debugger.h"

DebuggerActionFP Evaluator::fpDebuggerAction = debuggerStepAction;

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

std::string trimWS(const std::string& str)
{
    std::string rstr = str;

    std::regex wsfront("^\\s+");
    std::smatch matchfront;
    bool foundfront = std::regex_search(rstr, matchfront, wsfront);
    if(foundfront)
    {
        rstr = rstr.substr(matchfront.str(0).size());
    }

    std::regex wsback("\\s+$");
    std::smatch matchback;
    bool foundback = std::regex_search(rstr, matchback, wsback);
    if(foundback)
    {
        rstr = rstr.substr(0, matchback.str(0).size());
    }  

    return rstr;
}

std::vector<std::string> splitString(const std::string& str)
{
    std::regex rgx("(?:\\r\\n|\\r|\\n)");
    std::sregex_token_iterator iter(str.begin(), str.end(), rgx, -1);

    std::vector<std::string> result;
    for (std::sregex_token_iterator end; iter != end; ++iter)
    {
        result.push_back(iter->str());
    }

    return result;
}

std::pair<DebuggerCmd, std::string> dbg_parseDebuggerCmd(Evaluator* vv)
{
    std::string opstr;
    int cc = 0;

    printf("> ");
    fflush(stdout);

    do
    {    
        cc = std::getchar();
        if(cc == 127)
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
            if(cc != '\n')
            {
                opstr.push_back(cc);
            }
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
        std::regex pfx("^(display|d)(\\s)+");
        std::smatch matchpfx;
        std::regex_search(opstr, matchpfx, pfx);
        
        std::string path = opstr.substr(matchpfx.str(0).size());
        return std::make_pair(DebuggerCmd::ExpDisplay, path);
    }
    else if(opstr.starts_with("breakpoint ") || opstr.starts_with("b "))
    {
        std::regex pfx("^(breakpoint|b)(\\s+)");
        std::smatch matchpfx;
        std::regex_search(opstr, matchpfx, pfx);

        std::string actionstr = opstr.substr(matchpfx.str(0).size());

        std::regex afx("^(list|add|delete)(\\s+)");
        std::smatch matchaction;
        bool actionok = std::regex_search(actionstr, matchaction, afx);
        if(!actionok)
        {
            printf("Bad breakpoint action...\n");
            fflush(stdout);

            return std::make_pair(DebuggerCmd::Invalid, opstr);
        }

        std::string bpstr = actionstr.substr(matchaction.str(0).size());

        if(opstr.starts_with("list"))
        {
            return std::make_pair(DebuggerCmd::ListBreakPoint, bpstr);
        }
        else if(opstr.starts_with("add"))
        {
            std::regex bpfx("^[.a-zA-Z0-9_/]+:[0-9]+");
            std::smatch matchbp;
            bool bpok = std::regex_search(bpstr, matchbp, bpfx);
            if(!bpok)
            {
                printf("Bad breakpoint location...\n");
                fflush(stdout);

                return std::make_pair(DebuggerCmd::Invalid, bpstr);
            }

            return std::make_pair(DebuggerCmd::AddBreakPoint, bpstr);
        }
        else
        {
            std::regex bpfx("^[0-9]+");
            std::smatch matchbp;
            bool bpok = std::regex_search(bpstr, matchbp, bpfx);
            if(!bpok)
            {
                printf("Bad breakpoint id...\n");
                fflush(stdout);

                return std::make_pair(DebuggerCmd::Invalid, bpstr);
            }

            return std::make_pair(DebuggerCmd::DeleteBreakpoint, bpstr);
        }
    }
    else
    {
        return std::make_pair(DebuggerCmd::Help, "");
    }
}

void dbg_printHelp()
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
    printf("----\n");
    printf("  (b)reakpoint list\n");
    printf("  (b)reakpoint add file:line\n");
    printf("  (b)reakpoint delete bpid\n");
    printf("  (q)uit\n");
}

void dbg_printOp(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();

    printf("> %s\n", cframe->dbg_currentbp.op->ssrc.c_str());
    fflush(stdout);
}

void dbg_printFunction(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();
    std::string contents = MarshalEnvironment::g_srcMap.find(cframe->invoke->srcFile)->second;
    
    auto lines = splitString(contents);
    for(int64_t i = cframe->invoke->sinfoStart.line; i <= cframe->invoke->sinfoEnd.line; ++i)
    {
        if(cframe->dbg_srcline != i) {
            printf("%3i: %s\n", (int)i, lines[i - 1].c_str());
        }
        else {
            printf("%3i >> : %s\n", (int)i, lines[i - 1].c_str());
        }
    }

    fflush(stdout);
}

void dbg_displayStack(Evaluator* vv)
{
    printf("++++\n");

    for(int32_t i = 0; i <= vv->dbg_getCPos(); ++i)
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
    for(int32_t i = 0; i <= vv->dbg_getCPos(); ++i)
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
    if(!vv->dbg_getCFrame()->dbg_prevreturnbp.isValid())
    {
        if(vv->dbg_getCFrame()->dbg_prevbp.isValid())
        {
            throw DebuggerException::CreateMoveToBP(vv->dbg_getCFrame()->dbg_prevbp);
        }
    }
    else
    {
        throw DebuggerException::CreateMoveToBP(vv->dbg_getCFrame()->dbg_prevreturnbp);
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
        auto val = Evaluator::evalParameterInfo(binvoke->paraminfo[i], vv->dbg_getCFrame()->frameptr);
        
        locals += "  " + params[i].name + ": " + params[i].ptype->fpDisplay(params[i].ptype, val, DisplayMode::CmdDebug) + "\n";
    }

    if(!params.empty())
    {
        locals += "\n";
    }

    locals += "**locals**\n";
    const std::map<std::string, VariableHomeLocationInfo>& vhomeinfo = vv->dbg_getCFrame()->dbg_locals;
    for(auto iter = vhomeinfo.cbegin(); iter != vhomeinfo.cend(); ++iter)
    {
        const std::string& vname = iter->first;
        auto isparam = std::find_if(params.cbegin(), params.cend(), [&vname](const BSQFunctionParameter& pp) {
            return pp.name == vname;
        }) != params.cend();

        if(!isparam)
        {
            auto val = vv->evalTargetVar(iter->second.location);
            locals += "  " + iter->first + ": " + iter->second.vtype->fpDisplay(iter->second.vtype, val, DisplayMode::CmdDebug) + "\n";
        }
    }

    printf("%s\n", locals.c_str());
    fflush(stdout);
}

void dbg_displayExp(Evaluator* vv, std::string vexp)
{
    const std::vector<BSQFunctionParameter>& params = vv->dbg_getCFrame()->invoke->params;
    auto ppos = std::find_if(params.cbegin(), params.cend(), [&vexp](const BSQFunctionParameter& param) {
        return param.name == vexp;
    });
        
    const std::map<std::string, VariableHomeLocationInfo>& vhomeinfo = vv->dbg_getCFrame()->dbg_locals;
    auto lpos = std::find_if(vhomeinfo.cbegin(), vhomeinfo.cend(), [&vexp](const std::pair<std::string, VariableHomeLocationInfo>& vinfo) {
        return vinfo.first == vexp;
    });

    if(ppos == params.cend() && lpos == vhomeinfo.cend())
    {
        printf("Unknown variable: %s\n", vexp.c_str());
        fflush(stdout);
    }
    else
    { 
        const BSQType* btype = nullptr;
        StorageLocationPtr sl = nullptr;
        if(ppos != params.cend())
        {
            auto binvoke = dynamic_cast<const BSQInvokeBodyDecl*>(vv->dbg_getCFrame()->invoke);
            auto pdist = std::distance(params.cbegin(), ppos);
            btype = ppos->ptype;
            sl = Evaluator::evalParameterInfo(binvoke->paraminfo[pdist], vv->dbg_getCFrame()->frameptr);
        }
        else
        {
            btype = lpos->second.vtype;
            sl = vv->evalTargetVar(lpos->second.location);
        }

        auto eval = btype->fpDisplay(btype, sl, DisplayMode::CmdDebug);
        printf("%s\n", eval.c_str());
        fflush(stdout);
    }
}

void dbg_bpList(Evaluator* vv)
{
    std::string bps("**breakpoints**\n");
    for(size_t i = 0; i < vv->breakpoints.size(); ++i)
    {
        bps += "[" + std::to_string(vv->breakpoints[i].bpid) + "] " + vv->breakpoints[i].invk->srcFile + ":" + std::to_string(vv->breakpoints[i].iline) + "\n";
    }

    printf("%s\n", bps.c_str());
    fflush(stdout);
}

void dbg_bpAdd(Evaluator* vv, std::string bpstr)
{
    auto spos = bpstr.find(':');
    assert(spos != std::string::npos);

    std::string file = bpstr.substr(0, spos);
    std::string lstr = bpstr.substr(spos + 1);
    int64_t ll = std::strtol(&lstr[0], nullptr, 10);

    std::vector<const BSQInvokeDecl*> candfuncs;
    std::copy_if(BSQInvokeDecl::g_invokes.cbegin(), BSQInvokeDecl::g_invokes.cend(), std::back_inserter(candfuncs), [&file, ll](const BSQInvokeDecl* iid) {
        return iid->srcFile.ends_with(file) && iid->sinfoStart.line == ll;
    });
        
    if(candfuncs.size() == 0)
    {
        printf("No files match the given breakpoint spec\n");
        fflush(stdout);
    }
    else if(candfuncs.size() > 1)
    {
        printf("Ambigious breakpoint spec -- multiple files match\n");
        fflush(stdout);
    }
    else
    {
        const BSQInvokeDecl* iid = candfuncs.front();

        auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [iid, ll](const BreakPoint& bp) {
            return bp.invk->srcFile == iid->srcFile && bp.iline == ll;
        });

        if(bpc != 0)
        {
            printf("Breakpoint already set at invoke\n");
            fflush(stdout);
        }
        else
        {
            auto opii = dynamic_cast<const BSQInvokeBodyDecl*>(iid)->body.cbegin();

            BreakPoint bp{(int64_t)vv->breakpoints.size(), -1, iid, ll, *opii};
            vv->breakpoints.push_back(bp);
        }
    }
}

void dbg_bpDelete(Evaluator* vv, std::string bpstr)
{
    int64_t ll = std::strtol(&bpstr[0], nullptr, 10);

    auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [&bpstr, ll](const BreakPoint& bp) {
        return bp.bpid == ll;
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
            return bp.bpid == ll;
        });

        vv->breakpoints.erase(ebp, vv->breakpoints.end());
    }
}

void dbg_quit(Evaluator* vv)
{
    printf("Exiting debugging session...\n");
    exit(0);
}

void debuggerStepAction(Evaluator* vv)
{
    dbg_printOp(vv);

    while(true)
    {
        auto cmd = dbg_parseDebuggerCmd(vv);

        if(cmd.first == DebuggerCmd::Help)
        {
            dbg_printHelp();
        }
        else if(cmd.first == DebuggerCmd::PrintFunction)
        {
            dbg_printFunction(vv);
        }
        else if(cmd.first == DebuggerCmd::CallStack)
        {
            dbg_displayStack(vv);
        }
        else if(cmd.first == DebuggerCmd::LocalDisplay)
        {
            dbg_displayLocals(vv);
        }
        else if(cmd.first == DebuggerCmd::ExpDisplay)
        {
            dbg_displayExp(vv, cmd.second);
        }
        else if(cmd.first == DebuggerCmd::Step)
        {
            dbg_processStep(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::StepInto)
        {
            dbg_processStepInto(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::Continue)
        {
            dbg_processContinue(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::ReverseStep)
        {
            dbg_processReverseStep(vv);
        }
        else if(cmd.first == DebuggerCmd::ReverseStepInto)
        {
            dbg_processReverseStepInto(vv);
        }
        else if(cmd.first == DebuggerCmd::ReverseContinue)
        {
            dbg_processReverseContinue(vv);
        }
        else if(cmd.first == DebuggerCmd::ListBreakPoint)
        {
            dbg_bpList(vv);
        }
        else if(cmd.first == DebuggerCmd::AddBreakPoint)
        {
            dbg_bpAdd(vv, cmd.second);
        }
        else if(cmd.first == DebuggerCmd::DeleteBreakpoint)
        {
            dbg_bpDelete(vv, cmd.second);
        }
        else if(cmd.first == DebuggerCmd::Quit)
        {
            dbg_quit(vv);
        }
        else
        {
            printf("Unknown command\n");
            fflush(stdout);
        }
    }
}