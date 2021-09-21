//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

#include <fstream>

////
//Work flow #1 -- Refute an Error
//Given a smt decl + a signature that (1) havocs inputs, (2) invokes a call, (3) asserts the result is the error
//   
//Either:
//  Prove unsat and return the JSON payload -- {result: "unreachable", time: number}
//  Prove sat and return the JSON payload -- {result: "possible", time: number}
//  Solver timeout and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowInfeasible(std::string smt2decl, APIModule* apimodule, unsigned timeout)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    //check the formula
    auto start = std::chrono::system_clock::now();
    auto res = s.check();    
    auto end = std::chrono::system_clock::now();

    auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"result", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"result", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        return {
            {"result", "possible"},
            {"time", delta_ms}
        };
    }
}

////
//Work flow #2 -- Witness an Error
//Given a smt decl + a signature that (1) havocs inputs, (2) invokes a call, (3) asserts the result is the error
//   
//Either:
//  Prove unsat and return the JSON payload -- {result: "unreachable", time: number}
//  Prove sat and return the JSON payload -- {result: "witness", time: number, input: any}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowWitness(std::string smt2decl, APIModule* apimodule, unsigned timeout)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    ExtractionInfo einfo(apimodule);

    //check the formula
    auto start = std::chrono::system_clock::now();
    auto res = s.check();    
    auto end = std::chrono::system_clock::now();

    auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"result", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"result", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        z3::expr_vector chks(c);
        ParseInfo pinfo(apimodule, &chks);

        auto m = s.get_model();

        json argv = json::array();
        auto rootctx = genInitialContextArg(apimodule, c);
        for(size_t i = 0; i < apimodule->api->argtypes.size(); ++i)
        {
            auto argtype = apimodule->api->argtypes[i];
            auto ctx = extendContext(apimodule, c, rootctx, i);
            auto jarg = argtype->z3extract(einfo, ctx, s, m);

            if(!jarg.has_value())
            {
                return {
                    {"result", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            argv.push_back(jarg.value());
        }

        return {
            {"result", "witness"},
            {"time", delta_ms},
            {"input", argv}
        };
    }
}

////
//Work flow #3 -- Compute an API result
//Given a smt decl, a signature, and a JSON representation of the arg vector 
//Either:
//  Compute the output of the function return the JSON payload -- {result: "output" | "unreachable", time: number, output: JSON}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowCompute(std::string smt2decl, APIModule* apimodule, json jin, unsigned timeout)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    z3::expr_vector chks(c);
    ParseInfo pinfo(apimodule, &chks);

    auto rootctx = genInitialContextArg(apimodule, c);
    for(size_t i = 0; i < apimodule->api->argtypes.size(); ++i)
    {
        auto argtype = apimodule->api->argtypes[i];
        auto ctx = extendContext(apimodule, c, rootctx, i);
        auto ok = argtype->toz3arg(pinfo, jin[i], ctx, c);
        if(!ok) {
            return {
                {"result", "error"},
                {"info", "Could not initialize arg values"}
            };
        }
    }

    for(auto iter = pinfo.chks.top()->begin(); iter != pinfo.chks.top()->end(); ++iter)
    {
        s.add(*iter);
    }

    //check the formula
    auto start = std::chrono::system_clock::now();
    auto res = s.check();    
    auto end = std::chrono::system_clock::now();

    auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"result", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"result", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        ExtractionInfo einfo(apimodule);
        auto m = s.get_model();

        auto resctx = genInitialContextResult(apimodule, c);
        auto eres = apimodule->api->restype->z3extract(einfo, resctx, s, m);

        if(!eres.has_value())
        {
            return {
                {"result", "error"},
                {"info", "Could not extract result"}
            };
        }

        return {
            {"result", "output"},
            {"time", delta_ms},
            {"output", eres.value()}
        };
    }
}

////
//Work flow #4 -- Compute an API input
//Given a smt decl that (1) havocs inputs, (2) invokes a call
//      + a signature, smt output name, and JSON result 
//Either:
//  Prove unsat and return the JSON payload -- {result: "unreachable", time: number}
//  Prove sat and return the JSON payload -- {result: "witness", time: number, input: any}
//  Timeout a and return the JSON payload -- {result: "unknown", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowInvert(std::string smt2decl, APIModule* apimodule, json jout, unsigned timeout)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    z3::expr_vector chks(c);
    ParseInfo pinfo(apimodule, &chks);
  
    auto resctx = genInitialContextResult(apimodule, c);
    auto resok = apimodule->api->restype->toz3arg(pinfo, jout, resctx, c);
    if(!resok)
    {
        return {
                {"result", "error"},
                {"info", "Could not initialize result"}
            };
    }

    for(auto iter = pinfo.chks.top()->begin(); iter != pinfo.chks.top()->end(); ++iter)
    {
        s.add(*iter);
    }

    //check the formula
    auto start = std::chrono::system_clock::now();
    auto res = s.check();    
    auto end = std::chrono::system_clock::now();

    auto delta_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"result", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"result", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        ExtractionInfo einfo(apimodule);
        auto m = s.get_model();

        json argv = json::array();
        auto rootctx = genInitialContextArg(apimodule, c);
        for(size_t i = 0; i < apimodule->api->argtypes.size(); ++i)
        {
            auto argtype = apimodule->api->argtypes[i];
            auto ctx = extendContext(apimodule, c, rootctx, i);
            auto jarg = argtype->z3extract(einfo, ctx, s, m);

            if(!jarg.has_value())
            {
                return {
                    {"result", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            argv.push_back(jarg.value());
        }

        return {
            {"result", "witness"},
            {"time", delta_ms},
            {"input", argv}
        };
    }
}


json getPayload(int argc, char** argv, int argidx)
{
    try
    {
        json payload;
        if(argc == argidx + 1)
        {
            std::cin >> payload;
        }
        else
        {
            std::ifstream infile(argv[argidx + 1]);
            infile >> payload;
        }

        return payload;
    }
    catch(const std::exception& e)
    {
        std::cerr << "Failed in payload parsing... " << e.what() << std::endl;
        exit(1);
    }
}

int main(int argc, char** argv)
{
    int argidx = 1;

    if(argc > argidx && std::string(argv[argidx]) == "--unreachable")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);

            json result = workflowInfeasible(smt2decl, apimodule, timeout);
            
            std::cout << result << std::endl;
        }
        catch(const std::exception& e)
        {
            std::cerr << "Failed in processing... " << e.what() << std::endl;
            exit(1);
        }
    }
    else if(argc > argidx && std::string(argv[argidx]) == "--witness")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);

            json result = workflowWitness(smt2decl, apimodule, timeout);
            
            std::cout << result << std::endl;
        }
        catch(const std::exception& e)
        {
            std::cerr << "Failed in processing... " << e.what() << std::endl;
            exit(1);
        }
    }
    else if(argc > argidx && std::string(argv[argidx]) == "--eval")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);

            json result = workflowCompute(smt2decl, apimodule, payload["jin"], timeout);
            
            std::cout << result << std::endl;
        }
        catch(const std::exception& e)
        {
            std::cerr << "Failed in processing... " << e.what() << std::endl;
            exit(1);
        }
    }
    else if(argc > argidx && std::string(argv[argidx]) == "--invert")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);

            json result = workflowInvert(smt2decl, apimodule, payload["jout"], timeout);
            
            std::cout << result << std::endl;
        }
        catch(const std::exception& e)
        {
            std::cerr << "Failed in processing... " << e.what() << std::endl;
            exit(1);
        }
    }
    else
    {
        printf("Unknown usage (--unreachable|--witness|--eval|--invert) [file.json]\n");
    }

    return 0;
}
