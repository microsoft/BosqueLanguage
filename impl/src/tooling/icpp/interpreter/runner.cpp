//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"
#include "asm_load.h"

#include <chrono>
#include <iostream>
#include <fstream>

std::optional<json> getIRFromStdIn()
{
    try
    {
        json payload;
        std::cin >> payload;

        return std::make_optional(payload);
    }
    catch(...)
    {
        return std::nullopt;
    }
}

std::optional<json> getIRFromFile(const std::string& file)
{
    try
    {
        json payload;
        std::ifstream infile(file);
        infile >> payload;

        return std::make_optional(payload);
    }
    catch(const std::exception& e)
    {
        return std::nullopt;
    }
}

const BSQInvokeBodyDecl* resolveInvokeForMainName(const std::string& main)
{
    return dynamic_cast<const BSQInvokeBodyDecl*>(BSQInvokeDecl::g_invokes[MarshalEnvironment::g_invokeToIdMap.find(main)->second]);
}

std::pair<bool, json> run(Evaluator& runner, const APIModule* api, const std::string& main, json args)
{
    auto filename = std::string("[MAIN INITIALIZE]");
    auto jsig = api->getSigForFriendlyName(main);
    const BSQInvokeBodyDecl* call = resolveInvokeForMainName(main);
    if(call == nullptr || !jsig.has_value())
    {
        return std::make_pair(false, "Could not load given entrypoint");
    }

    if(args.size() > jsig.value()->argtypes.size())
    {
        return std::make_pair(false, "Too many arguments provided to call");
    }

    //TODO: we need to check that all required arguments are provided

    //Create a 0 stack frame that we can parse the arguments onto and that will keep them live (for reuse)
    // -- may need to revisit as it creates hidden sharing if/when we support mutation in place
    uint8_t* istack = (uint8_t*)BSQ_STACK_SPACE_ALLOC(call->scalarstackBytes + call->mixedstackBytes);
    GC_MEM_ZERO(istack, call->scalarstackBytes + call->mixedstackBytes);
    GCStack::pushFrame((void**)(istack + call->scalarstackBytes), call->mixedMask);

    if(setjmp(Evaluator::g_entrybuff) > 0)
    {
        return std::make_pair(false, "Failed in argument parsing");
    }
    else
    {
        ICPPParseJSON jloader;
        for(size_t i = 0; i < args.size(); ++i)
        {
            auto itype = jsig.value()->argtypes[i];
            StorageLocationPtr pv = Evaluator::evalParameterInfo(call->paraminfo[i], istack, istack + call->scalarstackBytes);
            bool ok = itype->tparse(jloader, api, args[i], pv, runner);
            if(!ok)
            {
                return std::make_pair(false, "Failed in argument parsing");
            }
        }
    }

    Allocator::GlobalAllocator.reset();
    GCStack::reset();
    runner.reset();

    if(setjmp(Evaluator::g_entrybuff) > 0)
    {
        return std::make_pair(false, "Failed in evaluation");
    }
    else
    {
#ifdef BSQ_DEBUG_BUILD
        if(runner.debuggerattached)
        {
            auto result = BSQ_STACK_SPACE_ALLOC(call->resultType->allocinfo.inlinedatasize);
            std::optional<json> res = std::nullopt;

            while(true)
            {
                try
                {
                    runner.invokeMain(call, istack, result, call->resultType, call->resultArg);

                    ICPPParseJSON jextract;
                    auto rtype = jsig.value()->restype;
                    res = rtype->textract(jextract, api, result, runner);
                    break;
                }
                catch(const DebuggerException& e)
                {
                    if(e.m_abortMode == DebuggerExceptionMode::ErrorPreTime)
                    {
                        runner.ttdBreakpoint = e.m_eTime;
                    }
                    else if(e.m_abortMode == DebuggerExceptionMode::MoveToBP)
                    {
                        runner.ttdBreakpoint = e.m_eTime;
                    }
                    else
                    {
                        ;
                    }

                    Allocator::GlobalAllocator.reset();
                    GCStack::reset();
                    runner.reset();
                }
            }

            if(res == std::nullopt)
            {
                return std::make_pair(false, "Failed in result extraction");
            }
        
            return std::make_pair(true, res.value());
        }
        else
        {
#endif
            auto result = BSQ_STACK_SPACE_ALLOC(call->resultType->allocinfo.inlinedatasize);
            runner.invokeMain(call, istack, result, call->resultType, call->resultArg);

            ICPPParseJSON jextract;
            auto rtype = jsig.value()->restype;

            std::optional<json> res = rtype->textract(jextract, api, result, runner); //call->resultType->fpDisplay(call->resultType, result);
            if(res == std::nullopt)
            {
                return std::make_pair(false, "Failed in result extraction");
            }
        
            return std::make_pair(true, res.value());
#ifdef BSQ_DEBUG_BUILD
        }
#endif
    }
}

void parseArgs(int argc, char** argv, std::string& mode, bool& debugger, std::string& prog, std::string& input)
{
    bool isstream = false;
    debugger = false;
    for(int i = 0; i < argc; ++i)
    {
        std::string sarg(argv[i]);

        isstream |= (sarg == "--stream");
        debugger |= (sarg == "--debug");
    }

    if(isstream)
    {
        mode = "stream";
    }
    else if(argc == 3 || (argc == 4 && debugger))
    {
        mode = "run";
        prog = std::string(debugger ? argv[2] : argv[1]);
        input = std::string(debugger ? argv[3] : argv[2]);
    }
    else
    {
        fprintf(stderr, "Usage: icpp [--debug] bytecode.bsqir args[]\n");
        fprintf(stderr, "Usage: icpp [--debug] --stream\n");
        fflush(stderr);
        exit(1);
    }
}

int main(int argc, char** argv)
{
    std::string mode;
    bool debugger = false;
    std::string prog;
    std::string input;
    parseArgs(argc, argv, mode, debugger, prog, input);

    const char* outputenv = std::getenv("ICPP_OUTPUT_MODE");
    std::string outmode(outputenv != nullptr ? outputenv : "simple");

    if(mode == "stream")
    {
        auto payload = getIRFromStdIn();
        if(!payload.has_value() || !payload.value().contains("code") || !payload.value().contains("args"))
        {
            if(outmode == "simple")
            {
                printf("!ERROR! -- Failed to load JSON...\n");
            }
            else
            {
                printf("{\"status\": \"error:\", \"msg\": \"Failed to load JSON\"}\n");
            }
            fflush(stdout);
            exit(1);
        }

        json jcode = payload.value()["code"];
        json jmain = payload.value()["main"].get<std::string>();
        json jargs = payload.value()["args"];

        const APIModule* api = APIModule::jparse(jcode["api"]);

        Evaluator runner;
        loadAssembly(jcode["bytecode"], runner);

        auto start = std::chrono::system_clock::now();
        auto res = run(runner, api, jmain, jargs);
        auto end = std::chrono::system_clock::now();

        int delta_ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        auto jout = res.second.dump(4);
        if(res.first)
        {
            if(outmode == "simple")
            {
                printf("%s\n", jout.c_str());
            }
            else
            {
                printf("{\"status\": \"success\", \"time\": %i, \"value\": %s}\n", delta_ms, jout.c_str());
            }
            fflush(stdout);
            return 0;
        }
        else
        {
            if(outmode == "simple")
            {
                printf("%s\n", jout.c_str());
            }
            else
            {
                printf("{\"status\": \"failure\", \"time\": %i, \"msg\": %s}\n", delta_ms, jout.c_str());
            }
            fflush(stdout);

            return 1;
        }
    }
    else
    {
        auto cc = getIRFromFile(prog);
        if(!cc.has_value())
        {
            if(outmode == "simple")
            {
                printf("!ERROR! -- Failed to load file %s...\n", argv[1]);
            }
            else
            {
                printf("{\"status\": \"error:\", \"msg\": \"Failed to load file %s\"}\n", argv[1]);
            }
            fflush(stdout);
            exit(1);
        }

        json jcode = cc.value()["code"];
        auto jargs = json::parse(input);
        std::string jmain("__i__Main::main");
        if(jargs.is_object())
        {
            jargs = jargs["args"];
            jmain = "__i__" + jargs["main"].get<std::string>();
        }

        const APIModule* api = APIModule::jparse(jcode["api"]);

        Evaluator runner;
        loadAssembly(jcode["bytecode"], runner);

#ifdef BSQ_DEBUG_BUILD
        runner.debuggerattached = debugger;
#endif

        auto start = std::chrono::system_clock::now();
        auto res = run(runner, api, jmain, jargs);
        auto end = std::chrono::system_clock::now();

        int delta_ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        auto jout = res.second.dump(4);
        if(res.first)
        {
            if(outmode == "simple")
            {
                printf("> %s\n", jout.c_str());
                printf("Elapsed time %i...\n", (int)delta_ms);
            }
            else
            {
                printf("{\"status\": \"success\", \"time\": %i \"value\": %s}\n", (int)delta_ms, jout.c_str());
            }
            fflush(stdout);
            return 0;
        }
        else
        {
            if(outmode == "simple")
            {
                printf("!ERROR! %s\n", jout.c_str());
            }
            else
            {
                printf("{\"status\": \"failure\", \"msg\": %s}\n", jout.c_str());
            }
            fflush(stdout);
            return 1;
        }
    }
}
