//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "op_eval.h"

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

BSQInvokeBodyDecl* resolveInvokeForMainName(const std::string& main)
{
    return dynamic_cast<BSQInvokeBodyDecl*>(Environment::g_invokes[Environment::g_invokenameToIDMap[main]]);
}

bool parseJSONArgs(json args, const std::vector<BSQFunctionParameter>& params, uint8_t* argsroot, const std::map<size_t, size_t>& pposmap, std::vector<StorageLocationPtr>& argslocs)
{
    for(size_t i = 0; i < params.size(); ++i)
    {
        StorageLocationPtr trgt = (argsroot + pposmap.at(i));
        auto pptype = params[i].ptype;
        bool ok = pptype->consops.fpJSONParse(pptype, args[i], trgt);
        if(!ok)
        {
            return false;
        }

        argslocs.push_back(trgt);
    }
    return true;
}

bool run(Evaluator& runner, const std::string& main, json args, std::string& res)
{
    auto filename = std::string("[MAIN INITIALIZE]");
    BSQInvokeBodyDecl* call = resolveInvokeForMainName(main);
    BSQ_LANGUAGE_ASSERT(call != nullptr, &filename, -1, "Could not load given entrypoint");

    size_t argsbytes = call->resultType->allocinfo.inlinedatasize;
    std::string argsmask = call->resultType->allocinfo.inlinedmask;
    std::map<size_t, size_t> pposmap;
    for(size_t i = 0; i < call->params.size(); ++i)
    {
        pposmap[i] = argsbytes;

        argsbytes += call->params[i].ptype->allocinfo.inlinedatasize;
        argsmask += call->params[i].ptype->allocinfo.inlinedmask;
    }

    uint8_t* mframe = (uint8_t*)BSQ_STACK_SPACE_ALLOC(argsbytes);
    GCStack::pushFrame((void**)mframe, argsmask.c_str());

    std::vector<void*> argslocs;
    uint8_t* argsroot = mframe;

    if(setjmp(Environment::g_entrybuff) > 0)
    {
        return false;
    }
    else
    {
        bool argsok = parseJSONArgs(args, call->params, argsroot, pposmap, argslocs);
        BSQ_LANGUAGE_ASSERT(argsok, &filename, -1, "Could not parse entrypoint arguments");

        runner.invokeMain(call, argslocs, mframe, call->resultType, call->resultArg);

        res = call->resultType->fpDisplay(call->resultType, mframe);
        return true;
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
        json jargs = payload.value()["args"];

        Evaluator runner;
        std::string main = loadAssembly(jcode, runner);

        std::string res;
        bool success = run(runner, main, jargs, res);
        if(success)
        {
            printf("%s", res.c_str());
        }
        else
        {
            printf("!ERROR!");
        }

        return 0;
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

        Evaluator runner;
        std::string main = loadAssembly(jcode, runner);

        auto jargs = json::parse(input);

        std::string res;
        auto start = std::chrono::system_clock::now();
        bool success = run(runner, main, jargs, res);
        auto end = std::chrono::system_clock::now();

        auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        if(success)
        {
            printf("> %s\n", res.c_str());
        }
        else
        {
            printf("!ERROR!\n");
        }
        printf("Elapsed time %i...\n", (int)delta_ms);

        return 0;
    }
}
