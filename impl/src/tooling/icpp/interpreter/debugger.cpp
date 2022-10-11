//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "debugger.h"

uint8_t debugger_in_buf[1024];
uint8_t debugger_out_buf[1024];

#ifdef _WIN32
bool initializeDebuggerIO()
{
    memset(debugger_in_buf, 0, sizeof(debugger_in_buf));
    memset(debugger_out_buf, 0, sizeof(debugger_out_buf));

    assert(false); //no network debugging yet
    return false;
}

void closeDebuggerIO()
{
    assert(false); //no network debugging yet
}

std::string readDebuggerCmd()
{
    std::string opstr;

    assert(false);

    return opstr;
}

void writeDebuggerOutput(std::string data)
{
    assert(false);
}
#else
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/ip.h>

struct hostent *hp;
struct sockaddr_in debugger_addr;
int debugger_socket = -1;

bool initializeDebuggerIO()
{
    memset(debugger_in_buf, 0, sizeof(debugger_in_buf));
    memset(debugger_out_buf, 0, sizeof(debugger_out_buf));

    memset((char*)&debugger_addr, 0, sizeof(debugger_addr));
    debugger_addr.sin_family = AF_INET;
    debugger_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    debugger_addr.sin_port = htons(1337);

    debugger_socket = socket(AF_INET, SOCK_STREAM, 0);
    if(debugger_socket < 0)
    {
        return false;
    }

    auto connectok = false;
    auto sleepct = 0;
    while(!connectok && sleepct < 10)
    {
        connectok = connect(debugger_socket, (struct sockaddr*)&debugger_addr, sizeof(debugger_addr));
        if(!connectok)
        {
            sleep(3);
            sleepct++;
        }
    }

    return connectok;
}

void closeDebuggerIO()
{
    shutdown(debugger_socket, SHUT_RDWR);
}

std::string readDebuggerCmd()
{
    std::string opstr;

    while(true)
    {
        memset(debugger_in_buf, 0, sizeof(debugger_in_buf));
        auto nbytes = read(debugger_socket, debugger_in_buf, sizeof(debugger_in_buf));
        
        auto niter = std::find(debugger_in_buf, debugger_in_buf + nbytes, '\0');
        
        opstr.reserve(opstr.size() + nbytes);
        std::transform(debugger_in_buf, debugger_in_buf + nbytes, std::back_inserter(opstr), [](uint8_t b) {
            return (char)b;
        });

        if(niter == debugger_in_buf + (nbytes - 1))
        {
            break;
        }
    }

    return opstr;
}

void writeDebuggerOutput(std::string data)
{
    data.push_back('\0');
    auto cpos = data.cbegin();

    while(true)
    {
        int64_t cbytes = (int64_t)std::min((size_t)std::distance(cpos, data.cend()), (size_t)sizeof(debugger_out_buf));

        memset(debugger_out_buf, 0, sizeof(debugger_out_buf));
        std::transform(cpos, cpos + cbytes, debugger_out_buf, [](char c) {
            return (uint8_t)c;
        });
        cpos += cbytes;

        int64_t nbytes = (int64_t)write(debugger_socket, debugger_out_buf, cbytes);
        while(nbytes < cbytes)
        {
            auto remainbytes = cbytes - nbytes;
            auto nnbytes = write(debugger_socket, debugger_out_buf + nbytes, remainbytes);

            nbytes += nnbytes;
        }

        if(cpos == data.end())
        {
            break;
        }
    }
}
#endif 

std::pair<DebuggerCmd, std::string> readDebugCmd()
{
    std::string opstr = readDebuggerCmd();

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

std::string dbg_printHelp()
{
    return 
    std::string("Available commands are:\n") +
    "----\n" +
    "  (p)rint\n" +
    "  stack\n" +
    "----\n" +
    "  (s)tep\n" +
    "  (i)nto\n" +
    "  (c)ontinue\n" +
    "  (r)everse (s)tep\n" +
    "  (r)everse (i)nto\n" +
    "  (r)everse (c)ontinue\n" +
    "----\n" +
    "  (l)ocals\n" +
    "  (d)isplay vexp\n" +
    "----\n" +
    "  (b)reakpoint list\n" +
    "  (b)reakpoint add file:line\n" +
    "  (b)reakpoint delete bpid\n" +
    "  (q)uit\n";
}

std::string dbg_printOp(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();
    return cframe->dbg_currentbp.op->ssrc + "\n";
}

std::string dbg_printFunction(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();
    std::string contents = MarshalEnvironment::g_srcMap.find(cframe->invoke->srcFile)->second;
    
    std::stringstream ss;
    auto lines = splitString(contents);
    for(int64_t i = cframe->invoke->sinfoStart.line; i <= cframe->invoke->sinfoEnd.line; ++i)
    {
        char line[16] = {0};
        if(cframe->dbg_srcline != i) {
            sprintf(line, "%3i: ", (int)i);
            ss << line << lines[i - 1] << "\n";
        }
        else {
            sprintf(line, "%3i >> : ", (int)i);
            ss << line << lines[i - 1] << "\n";
        }
    }

    return ss.str();
}

std::string dbg_displayStack(Evaluator* vv)
{
    std::stringstream ss;
    ss << "++++\n";

    for(int32_t i = 0; i <= vv->dbg_getCPos(); ++i)
    {
        ss << Evaluator::g_callstack[i].invoke->name << "\n";
    }

    ss << "----\n";

    return ss.str();
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

std::string dbg_displayLocals(Evaluator* vv)
{
    std::stringstream ss;
    ss << "**params**\n";

    const std::vector<BSQFunctionParameter>& params = vv->dbg_getCFrame()->invoke->params;
    for(size_t i = 0; i < params.size(); ++i)
    {
        auto binvoke = dynamic_cast<const BSQInvokeBodyDecl*>(vv->dbg_getCFrame()->invoke);
        auto val = Evaluator::evalParameterInfo(binvoke->paraminfo[i], vv->dbg_getCFrame()->frameptr);
        
        ss << "  " << params[i].name << ": " << params[i].ptype->fpDisplay(params[i].ptype, val, DisplayMode::CmdDebug) << "\n";
    }

    if(!params.empty())
    {
        ss << "\n";
    }

    ss << "**locals**\n";
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
            ss << "  " << iter->first << ": " << iter->second.vtype->fpDisplay(iter->second.vtype, val, DisplayMode::CmdDebug) << "\n";
        }
    }

    ss << "\n";
    return ss.str();
}

std::string dbg_displayExp(Evaluator* vv, std::string vexp)
{
    const std::vector<BSQFunctionParameter>& params = vv->dbg_getCFrame()->invoke->params;
    auto ppos = std::find_if(params.cbegin(), params.cend(), [&vexp](const BSQFunctionParameter& param) {
        return param.name == vexp;
    });
        
    const std::map<std::string, VariableHomeLocationInfo>& vhomeinfo = vv->dbg_getCFrame()->dbg_locals;
    auto lpos = std::find_if(vhomeinfo.cbegin(), vhomeinfo.cend(), [&vexp](const std::pair<std::string, VariableHomeLocationInfo>& vinfo) {
        return vinfo.first == vexp;
    });

    std::stringstream ss;
    if(ppos == params.cend() && lpos == vhomeinfo.cend())
    {
        ss << "Unknown variable: " << vexp << "\n";
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
        ss << eval << "\n";
    }

    return ss.str();
}

std::string dbg_bpList(Evaluator* vv)
{
    std::stringstream ss;
    ss << "**breakpoints**\n";
    for(size_t i = 0; i < vv->breakpoints.size(); ++i)
    {
        ss << "[" << std::to_string(vv->breakpoints[i].bpid) << "] " << vv->breakpoints[i].invk->srcFile << ":" << std::to_string(vv->breakpoints[i].iline) << "\n";
    }

    ss << "\n";
    return ss.str();
}

std::string dbg_bpAdd(Evaluator* vv, std::string bpstr)
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
        return std::string("No files match the given breakpoint spec\n");
    }
    else if(candfuncs.size() > 1)
    {
        return std::string("Ambigious breakpoint spec -- multiple files match\n");
    }
    else
    {
        const BSQInvokeDecl* iid = candfuncs.front();

        auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [iid, ll](const BreakPoint& bp) {
            return bp.invk->srcFile == iid->srcFile && bp.iline == ll;
        });

        if(bpc != 0)
        {
            return std::string("Breakpoint already set at invoke\n");
        }
        else
        {
            auto opii = dynamic_cast<const BSQInvokeBodyDecl*>(iid)->body.cbegin();

            BreakPoint bp{(int64_t)vv->breakpoints.size(), -1, iid, ll, *opii};
            vv->breakpoints.push_back(bp);

            return std::string("Added breakpoint [") + std::to_string(bp.bpid) + "]\n";
        }
    }
}

std::string dbg_bpDelete(Evaluator* vv, std::string bpstr)
{
    int64_t ll = std::strtol(&bpstr[0], nullptr, 10);

    auto bpc = std::count_if(vv->breakpoints.begin(), vv->breakpoints.end(), [ll](const BreakPoint& bp) {
        return bp.bpid == ll;
    });

    if(bpc == 0)
    {
        return std::string("No breakpoints match the spec\n");
    }
    else if(bpc > 1)
    {
        return std::string("Ambigious breakpoint spec -- multiple files match\n");
    }
    else
    {
        auto ebp = std::remove_if(vv->breakpoints.begin(), vv->breakpoints.end(), [ll](const BreakPoint& bp) {
            return bp.bpid == ll;
        });

        vv->breakpoints.erase(ebp, vv->breakpoints.end());
        return std::string("Deleted breakpoint [") + bpstr + "]\n";
    }
}

std::string dbg_quit()
{
    closeDebuggerIO();
    return("Exiting debugging session...\n");
}

void debuggerStepAction(Evaluator* vv)
{
    if(debugger_socket == -1)
    {
        return;
    }

    writeDebuggerOutput(dbg_printOp(vv));

    while(true)
    {
        writeDebuggerOutput("> ");
        
        auto cmd = readDebugCmd();
        std::string response;

        if(cmd.first == DebuggerCmd::Help)
        {
            writeDebuggerOutput(dbg_printHelp());
        }
        else if(cmd.first == DebuggerCmd::PrintFunction)
        {
            writeDebuggerOutput(dbg_printFunction(vv));
        }
        else if(cmd.first == DebuggerCmd::CallStack)
        {
            writeDebuggerOutput(dbg_displayStack(vv));
        }
        else if(cmd.first == DebuggerCmd::LocalDisplay)
        {
            writeDebuggerOutput(dbg_displayLocals(vv));
        }
        else if(cmd.first == DebuggerCmd::ExpDisplay)
        {
            writeDebuggerOutput(dbg_displayExp(vv, cmd.second));
        }
        else if(cmd.first == DebuggerCmd::Step)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processStep(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::StepInto)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processStepInto(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::Continue)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processContinue(vv);
            break;
        }
        else if(cmd.first == DebuggerCmd::ReverseStep)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processReverseStep(vv);
        }
        else if(cmd.first == DebuggerCmd::ReverseStepInto)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processReverseStepInto(vv);
        }
        else if(cmd.first == DebuggerCmd::ReverseContinue)
        {
            writeDebuggerOutput("$RESUME$");
            dbg_processReverseContinue(vv);
        }
        else if(cmd.first == DebuggerCmd::ListBreakPoint)
        {
            writeDebuggerOutput(dbg_bpList(vv));
        }
        else if(cmd.first == DebuggerCmd::AddBreakPoint)
        {
            writeDebuggerOutput(dbg_bpAdd(vv, cmd.second));
        }
        else if(cmd.first == DebuggerCmd::DeleteBreakpoint)
        {
            writeDebuggerOutput(dbg_bpDelete(vv, cmd.second));
        }
        else if(cmd.first == DebuggerCmd::Quit)
        {
            writeDebuggerOutput("$QUIT$");
            dbg_quit();
        }
        else
        {
            writeDebuggerOutput("$UNKNOWN$");
        }
    }
}
