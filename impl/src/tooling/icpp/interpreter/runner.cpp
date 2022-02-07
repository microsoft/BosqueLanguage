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
    if(call != nullptr || !jsig.has_value())
    {
        return std::make_pair(false, "Could not load given entrypoint");
    }

    if(setjmp(Evaluator::g_entrybuff) > 0)
    {
        return std::make_pair(false, "Failed in argument parsing");
    }
    else
    {
        ICPPParseJSON jloader;
        uint8_t* mstack = runner.prepareMainStack(call);

        for(size_t i = 0; i < args.size(); ++i)
        {
            auto itype = jsig.value()->argtypes[i];
            StorageLocationPtr pv = Evaluator::evalParameterInfo(call->paraminfo[i], mstack, mstack + call->scalarstackBytes);
            bool ok = itype->tparse(jloader, api, args[i], pv, runner);
            if(!ok)
            {
                return std::make_pair(false, "Failed in argument parsing");
            }
        }
    }

    if(setjmp(Evaluator::g_entrybuff) > 0)
    {
        return std::make_pair(false, "Failed in evaluation");
    }
    else
    {
        auto result = BSQ_STACK_SPACE_ALLOC(call->resultType->allocinfo.inlinedatasize);
        runner.invokeMain(call, &result, call->resultType, call->resultArg);

        ICPPParseJSON jextract;
        auto rtype = jsig.value()->restype;

        std::optional<json> res = rtype->textract(jextract, api, result, runner); //call->resultType->fpDisplay(call->resultType, result);
        if(res == std::nullopt)
        {
            return std::make_pair(false, "Failed in result extraction");
        }
        
        return std::make_pair(true, res.value());
    }
}

void parseArgs(int argc, char** argv, std::string& mode, std::string& prog, std::string& input)
{
    if(argc == 2 && std::string(argv[1]) == std::string("--stream"))
    {
        mode = "stream";
    }
    else if(argc == 3)
    {
        mode = "run";
        prog = std::string(argv[1]);
        input = std::string(argv[2]);
    }
    else
    {
        fprintf(stderr, "Usage: icpp bytecode.bsqir args[]\n");
        fprintf(stderr, "Usage: icpp --stream\n");
        fflush(stderr);
        exit(1);
    }
}

int main(int argc, char** argv)
{
    std::string mode; 
    std::string prog;
    std::string input;
    parseArgs(argc, argv, mode, prog, input);

    if(mode == "stream")
    {
        auto payload = getIRFromStdIn();
        if(!payload.has_value() || !payload.value().contains("code") || !payload.value().contains("args"))
        {
            fprintf(stderr, "Failed to load JSON...\n");
            fflush(stderr);
            exit(1);
        }

        json jcode = payload.value()["code"];
        json jmain = payload.value()["main"].get<std::string>();
        json jargs = payload.value()["args"];

        const APIModule* api = APIModule::jparse(jcode["api"]);

        Evaluator runner;
        loadAssembly(jcode["bytecode"], runner);

        auto res = run(runner, api, jmain, jargs);
        auto jout = res.second.dump(4);
        if(res.first)
        {
            printf("%s\n", jout.c_str());
            return 0;
        }
        else
        {
            printf("!ERROR! %s\n", jout.c_str());
            return 1;
        }
    }
    else
    {
        auto cc = getIRFromFile(prog);
        if(!cc.has_value())
        {
            fprintf(stderr, "Failed to load file %s\n", argv[1]);
            fflush(stderr);
            exit(1);
        }

        json jcode = cc.value();
        auto jargs = json::parse(input);
        std::string jmain("main");
        if(jargs.is_object())
        {
            jargs = jargs["args"];
            jmain = jargs["main"].get<std::string>();
        }

        const APIModule* api = APIModule::jparse(jcode["api"]);

        Evaluator runner;
        loadAssembly(jcode["bytecode"], runner);

        auto start = std::chrono::system_clock::now();
        auto res = run(runner, api, jmain, jargs);
        auto end = std::chrono::system_clock::now();

        auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        auto jout = res.second.dump(4);
        if(res.first)
        {
            printf("> %s\n", jout.c_str());
            printf("Elapsed time %i...\n", (int)delta_ms);
            return 0;
        }
        else
        {
            printf("!ERROR! %s\n", jout.c_str());
            return 1;
        }
    }
}
