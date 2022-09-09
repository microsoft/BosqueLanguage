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

        std::regex pathx("^(([*][0-9]+)|([$]?[a-zA-Z]+))(([.][a-zA-Z0-9]+)?([\\[]([0-9]+|[\\\"]([^\\\"])+[\\\"])+[\\]])*)*$");
        std::smatch matchpath;
        auto pathok = std::regex_search(path, matchpath, pathx);
        if(!pathok)
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

        std::regex bpfx("^[a-zA-Z0-9_/]+:[0-9]+");
        std::smatch matchbp;
        bool bpok = std::regex_search(bpstr, matchbp, bpfx);
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
    printf("    (var|*id)(.name([literal])*)*\n");
    printf("----\n");
    printf("  (b)reakpoint list\n");
    printf("  (b)reakpoint add|delete bp\n");
    printf("    file:line");
    printf("  (q)uit\n");
}

void dbg_printLine(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();
    std::string contents = MarshalEnvironment::g_srcMap.find(cframe->invoke->srcFile)->second;
    
    auto lines = splitString(contents);
    std::string line = trimWS(lines[cframe->dbg_currentline - 1]);

    printf("%i: %s\n", (int)cframe->dbg_currentline, line.c_str());
    fflush(stdout);
}

void dbg_printFunction(Evaluator* vv)
{
    auto cframe = vv->dbg_getCFrame();
    std::string contents = MarshalEnvironment::g_srcMap.find(cframe->invoke->srcFile)->second;
    
    auto lines = splitString(contents);
    for(int64_t i = cframe->invoke->sinfoStart.line; i <= cframe->invoke->sinfoEnd.line; ++i)
    { 
        printf("%3i: %s\n", (int)i, lines[i - 1].c_str());
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

std::optional<std::pair<int64_t, std::string>> dbg_extract_accessor_numeric(std::string vexp)
{
    size_t spos = 0;
    while(spos != vexp.size() && vexp[spos] != '.' && vexp[spos] != '[' && vexp[spos] != ']')
    {
        spos++;
    }

    auto nstr = vexp.substr(0, spos);
    std::regex nre("^[0-9]+$");
    bool nok = std::regex_match(nstr, nre);
    if(!nok)
    {
        return std::nullopt;
    }

    return std::make_optional(std::make_pair(std::strtol(&nstr[0], nullptr, 10), vexp.substr(spos)));
}

std::optional<std::pair<std::string, std::string>> dbg_extract_accessor_qstring(std::string vexp)
{
    size_t spos = 1;
    while(spos != vexp.size() && vexp[spos] != '"')
    {
        spos++;
    }

    if(vexp[0] != '"' || vexp[spos] != '"')
    {
        return std::nullopt;
    }

    return std::make_optional(std::make_pair(vexp.substr(1, spos), vexp.substr(spos + 2)));
}

std::optional<std::pair<std::string, std::string>> dbg_extract_accessor_name(std::string vexp)
{
    size_t spos = 0;
    while(spos != vexp.size() && vexp[spos] != '.' && vexp[spos] != '[')
    {
        spos++;
    }

    auto nstr = vexp.substr(0, spos);
    std::regex nre("^[$]?[_a-zA-Z0-9]+$");
    bool nok = std::regex_match(nstr, nre);
    if(!nok)
    {
        return std::nullopt;
    }

    return std::make_optional(std::make_pair(nstr, vexp.substr(spos)));
}

bool dbg_processTupleAccess(Evaluator* vv, const BSQType*& btype, StorageLocationPtr& cpos, int64_t idx)
{
    if(btype->isUnion())
    {
        auto utype = dynamic_cast<const BSQUnionType*>(btype);

        btype = utype->getVType(cpos);
        cpos = utype->getVData_StorageLocation(cpos);
    }
    
    const BSQTupleInfo* tinfo = dynamic_cast<const BSQTupleInfo*>(btype);
    if(tinfo == nullptr || idx >= tinfo->maxIndex)
    {
        return false;
    }

    cpos = btype->indexStorageLocationOffset(cpos, tinfo->idxoffsets[idx]);
    btype = BSQType::g_typetable[tinfo->ttypes[idx]];

    return true;
}

bool dbg_processNameAccess(Evaluator* vv, const BSQType*& btype, StorageLocationPtr& cpos, std::string name)
{
    if(btype->isUnion())
    {
        auto utype = dynamic_cast<const BSQUnionType*>(btype);

        btype = utype->getVType(cpos);
        cpos = utype->getVData_StorageLocation(cpos);
    }

    const BSQRecordInfo* rinfo = dynamic_cast<const BSQRecordInfo*>(btype);
    if(rinfo != nullptr)
    {
        auto pidii = MarshalEnvironment::g_propertyToIdMap.find(name);
        if(pidii == MarshalEnvironment::g_propertyToIdMap.cend())
        {
            return false;
        }

        auto pidxii = std::find(rinfo->properties.cbegin(), rinfo->properties.cend(), pidii->second);
        if(pidxii == rinfo->properties.cend())
        {
            return false;
        }

        auto idx = std::distance(rinfo->properties.cbegin(), pidxii);
        cpos = btype->indexStorageLocationOffset(cpos, rinfo->propertyoffsets[idx]);
        btype = BSQType::g_typetable[rinfo->rtypes[idx]];
    }
    else
    {
        const BSQEntityInfo* einfo = dynamic_cast<const BSQEntityInfo*>(btype);
        if(einfo == nullptr)
        {
            return false;
        }

        auto pidxii = std::find_if(einfo->fields.cbegin(), einfo->fields.cend(), [&name](BSQFieldID fid) {
            const BSQField* ff = BSQField::g_fieldtable[fid];
            return ff->fname == name;
        });

        if(pidxii == einfo->fields.cend())
        {
            return false;
        }

        auto idx = std::distance(einfo->fields.cbegin(), pidxii);
        cpos = btype->indexStorageLocationOffset(cpos, einfo->fieldoffsets[idx]);
        btype = BSQType::g_typetable[einfo->ftypes[idx]];
    }

    return true;
}

bool dbg_processNumberKey(Evaluator* vv, const BSQType*& btype, StorageLocationPtr& cpos, int64_t idx)
{
    if(btype->isUnion())
    {
        auto utype = dynamic_cast<const BSQUnionType*>(btype);

        btype = utype->getVType(cpos);
        cpos = utype->getVData_StorageLocation(cpos);
    }

    const BSQListType* ltype = dynamic_cast<const BSQListType*>(btype);
    if(ltype != nullptr)
    {
        if(LIST_LOAD_DATA(cpos) == nullptr)
        {
            return false;
        }

        auto count = (int64_t)LIST_LOAD_REPR_TYPE(cpos)->getCount(LIST_LOAD_DATA(cpos));
        if(idx >= count)
        {
            return false;
        }

        btype = BSQType::g_typetable[ltype->etype];
        BSQListOps::s_safe_get(LIST_LOAD_DATA(cpos), LIST_LOAD_REPR_TYPE(cpos), idx, btype, cpos);
    }
    else
    {
        const BSQMapType* mtype = dynamic_cast<const BSQMapType*>(btype);
        if(mtype == nullptr)
        {
            return false;
        }

        if(MAP_LOAD_DATA(cpos) == nullptr)
        {
            return false;
        }

        auto reprtype = MAP_LOAD_REPR_TYPE(cpos);
        auto ktype = BSQType::g_typetable[mtype->ktype];
        if(ktype->tid != BSQ_TYPE_ID_INT && ktype->tid != BSQ_TYPE_ID_NAT)
        {
            return false;
        }

        auto res = BSQMapOps::s_lookup_ne(MAP_LOAD_DATA(cpos), reprtype, &idx, ktype);
        if(res == nullptr)
        {
            return false;
        }

        btype = BSQType::g_typetable[mtype->vtype];
        ktype->storeValue(cpos, reprtype->getValueLocation(res));
    }

    return true;
}

bool dbg_processStringKey(Evaluator* vv, const BSQType*& btype, StorageLocationPtr& cpos, std::string key)
{
    const BSQMapType* mtype = dynamic_cast<const BSQMapType*>(btype);
    if(mtype == nullptr)
    {
        return false;
    }

    if(MAP_LOAD_DATA(cpos) == nullptr)
    {
        return false;
    }

    auto reprtype = MAP_LOAD_REPR_TYPE(cpos);
    auto ktype = BSQType::g_typetable[mtype->ktype];
    if(ktype->tid != BSQ_TYPE_ID_STRING)
    {
        return false;
    }

    if(key.size() > 15)
    {
        //small strings only for now
        return false;
    }

    BSQString kstr;
    kstr.u_inlineString = BSQInlineString::create((const uint8_t*)key.c_str(), key.size());
    auto res = BSQMapOps::s_lookup_ne(MAP_LOAD_DATA(cpos), reprtype, &kstr, ktype);
    if(res == nullptr)
    {
        return false;
    }

    btype = BSQType::g_typetable[mtype->vtype];
    ktype->storeValue(cpos, reprtype->getValueLocation(res));

    return true;
}

void dbg_displayExp(Evaluator* vv, std::string vexp)
{
    const BSQType* btype = nullptr;
    StorageLocationPtr cpos = nullptr;
    if(vexp.starts_with("*"))
    {
        printf("Object ID support not implemented\n");
        fflush(stdout);
        return;
    }
    else
    {   
        auto np = dbg_extract_accessor_name(vexp);
        if(!np.has_value())
        {
            printf("Bad value name format\n");
            fflush(stdout);
            return;
        }

        auto name = np.value().first;

        const std::vector<BSQFunctionParameter>& params = vv->dbg_getCFrame()->invoke->params;
        auto ppos = std::find_if(params.cbegin(), params.cend(), [&name](const BSQFunctionParameter& param) {
            return param.name == name;
        });
        
        const std::map<std::string, VariableHomeLocationInfo>& vhomeinfo = vv->dbg_getCFrame()->dbg_locals;
        auto lpos = std::find_if(vhomeinfo.cbegin(), vhomeinfo.cend(), [&name](const std::pair<std::string, VariableHomeLocationInfo>& vinfo) {
            return vinfo.first == name;
        });

        if(ppos == params.cend() && lpos == vhomeinfo.cend())
        {
            printf("Unknown variable: %s\n", np.value().first.c_str());
            fflush(stdout);
            return;
        }
        else if(ppos != params.cend())
        {
            auto binvoke = dynamic_cast<const BSQInvokeBodyDecl*>(vv->dbg_getCFrame()->invoke);
            auto pdist = std::distance(params.cbegin(), ppos);
            btype = ppos->ptype;
            cpos = Evaluator::evalParameterInfo(binvoke->paraminfo[pdist], vv->dbg_getCFrame()->frameptr);
        }
        else
        {
            btype = lpos->second.vtype;
            cpos = vv->evalTargetVar(lpos->second.location);
        }

        vexp = np.value().second;
    }

    while(!vexp.empty())
    {
        if(vexp[0] == '.')
        {
            vexp = vexp.substr(1);

            auto idxopt = dbg_extract_accessor_numeric(vexp);
            auto nameopt = dbg_extract_accessor_name(vexp);

            if(idxopt.has_value())
            {
                bool accessok = dbg_processTupleAccess(vv, btype, cpos, idxopt.value().first);
                if(!accessok)
                {
                    printf("Bad value access path\n");
                    fflush(stdout);
                    return;
                }
                vexp = idxopt.value().second;
            }
            else if(nameopt.has_value())
            {
                bool accessok = dbg_processNameAccess(vv, btype, cpos, nameopt.value().first);
                if(!accessok)
                {
                    printf("Bad value access path\n");
                    fflush(stdout);
                    return;
                }
                vexp = nameopt.value().second;
            }
            else
            {
                printf("Bad value access path\n");
                fflush(stdout);
                return;
            }
        }
        else if(vexp[0] == '[')
        {
            vexp = vexp.substr(1);

            auto idxopt = dbg_extract_accessor_numeric(vexp);
            auto qstropt = dbg_extract_accessor_qstring(vexp);

            if(idxopt.has_value())
            {
                bool accessok = dbg_processNumberKey(vv, btype, cpos, idxopt.value().first);
                if(!accessok)
                {
                    printf("Bad value access path\n");
                    fflush(stdout);
                    return;
                }
                vexp = idxopt.value().second;
            }
            else if(qstropt.has_value())
            {
                bool accessok = dbg_processStringKey(vv, btype, cpos, qstropt.value().first);
                if(!accessok)
                {
                    printf("Bad value access path\n");
                    fflush(stdout);
                    return;
                }
                vexp = qstropt.value().second;
            }
            else
            {
                printf("Bad value access path\n");
                fflush(stdout);
                return;
            }

            if(vexp.empty() || vexp[0] != ']')
            {
                printf("Bad value access path\n");
                fflush(stdout);
                return;
            }
            vexp = vexp.substr(1);
        }
        else
        {
            printf("Bad value access path\n");
            fflush(stdout);
            return;
        }
    }

    std::string disp = btype->fpDisplay(btype, cpos, DisplayMode::CmdDebug);
    printf("%s\n", disp.c_str());
    fflush(stdout);
}

void dbg_bpList(Evaluator* vv)
{
    std::string bps("**breakpoints**\n");
    for(size_t i = 0; i < vv->breakpoints.size(); ++i)
    {
        bps += vv->breakpoints[i].invk->srcFile + ":" + std::to_string(vv->breakpoints[i].line) + "\n";
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
        return iid->srcFile.ends_with(file) && iid->sinfoStart.line <= ll && ll <= iid->sinfoEnd.line;
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
            return bp.invk->srcFile == iid->srcFile && bp.line == ll;
        });

        if(bpc != 0)
        {
            printf("Breakpoint already set at position\n");
            fflush(stdout);
        }
        else
        {
            //TODO: need to get opcode to set here as well

            //BreakPoint bp{-1, -1, iid, ll, -1};
            //vv->breakpoints.push_back(bp);
        }
    }
}

void dbg_bpDelete(Evaluator* vv, std::string bpstr)
{
    auto spos = bpstr.find(':');
    assert(spos != std::string::npos);

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
    printf("Exiting debugging session...\n");
    exit(0);
}

void debuggerStepAction(Evaluator* vv)
{
    dbg_printLine(vv);

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