//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "runner.h"

#include <boost/json/src.hpp>

bool loadJSONFromFile(const std::string& filename, boost::json::value& jval)
{
    return true;
}

void initialize()
{
    ;
}

void loadAssembly(const boost::json::value& jval)
{
    ;
}

BSQInvokeBodyDecl* resolveInvokeForMainName(const std::string& main)
{
    return nullptr;
}

bool parseJSONArgs(const boost::json::value& args, const std::vector<BSQFunctionParameter>& params, uint8_t* argsroot, std::vector<void*>& argslocs)
{
    return false;
}

void run(const std::string& main, const boost::json::value& args, uint64_t argsbytes, RefMask argsmask, StorageLocationPtr res)
{
    auto filename = std::string("[INITIALIZE]");
    BSQInvokeBodyDecl* call = resolveInvokeForMainName(main);
    BSQ_LANGUAGE_ASSERT(call != nullptr, &filename, -1, "Could not load given entrypoint");

    uint8_t* argsroot = (uint8_t*)BSQ_STACK_SPACE_ALLOC(argsbytes);
    GCStack::pushFrame(nullptr, 0, (void**)argsroot, argsmask);
 
    std::vector<void*> argslocs;
    bool argsok = parseJSONArgs(args, call->params, argsroot, argslocs);
    BSQ_LANGUAGE_ASSERT(argsok, &filename, -1, "Could not parse entrypoint arguments");

    Evaluator runner;
    runner.invokeMain(call, argslocs, res);
}

int main(int argc, char* argv)
{
    StorageLocationPtr res = nullptr;
    Allocator::GlobalAllocator.pushRoot(&res);

    std::string main = "NSMain::main";
    run(main, {}, 0, "", res);

    //TODO: print res

    return 0;
}
