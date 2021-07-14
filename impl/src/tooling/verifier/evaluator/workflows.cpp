//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

#include <fstream>

////
//Work flow #1 -- Refute or Witness an Error
//Given a smt decl + a signature that (1) havocs inputs, (2) invokes a call, (3) asserts the result is the error
//   
//Either:
//  Prove unsat and return the JSON payload -- {result: "infeasible", time: number}
//  Prove sat and return the JSON payload -- {result: "witness", time: number, input: any}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowValidate(std::string smt2decl, APIModule* apimodule, unsigned timeout, bool bsqon)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    ExtractionInfo einfo(apimodule, "_@smtres@_value");

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
            {"result", "infeasible"},
            {"time", delta_ms}
        };
    }
    else
    {
        z3::expr_vector chks(c);
        ParseInfo pinfo(apimodule, chks);

        auto m = s.get_model();

        json argv = json::array();
        auto rootctx = einfo.genInitialContext(m);
        for(size_t i = 0; i < apimodule->api->argtypes.size(); ++i)
        {
            auto argtype = apimodule->api->argtypes[i];
            auto ctx = einfo.extendContext(m, rootctx, i);
            auto jarg = argtype->argextract(einfo, ctx, s, m);

            if(!jarg.has_value())
            {
                return {
                    {"result", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            if(!bsqon)
            {
                argv.push_back(jarg.value());
            }
            else
            {
                std::optional<std::string> bsqarg = argtype->tobsqarg(pinfo, jarg.value(), "");
                argv.push_back(bsqarg.value());
            }
        }

        return {
            {"result", "witness"},
            {"time", delta_ms},
            {"input", argv}
        };
    }
}

////
//Work flow #2 -- Compute an API result
//Given a smt decl, a signature, and a JSON representation of the arg vector 
//Either:
//  Compute the output of the function return the JSON payload -- {result: "output" | "infeasible", time: number, output: JSON}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowCompute(std::string smt2decl, APIModule* apimodule, json jin, unsigned timeout, bool bsqon)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    z3::expr_vector chks(c);
    ParseInfo pinfo(apimodule, chks);

    for(size_t i = 0; i < apimodule->api->smtargnames.size(); ++i)
    {
        auto argname = apimodule->api->smtargnames[i];
        auto argtype = apimodule->api->argtypes[i];
        
        auto argvar = c.constant(argname.c_str(), getZ3SortFor(apimodule, argtype, c));
        auto argval = argtype->toz3arg(pinfo, jin[i], c).value();
        s.add(argvar == argval);
    }
    s.add(pinfo.chks);

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
            {"result", "infeasible"},
            {"time", delta_ms}
        };
    }
    else
    {
        ExtractionInfo einfo(apimodule, "_@smtres@_value");
        auto m = s.get_model();
        
        auto resexpr = c.constant("_@smtres@_value", getZ3SortFor(apimodule, apimodule->api->resType, c));
        auto eres = apimodule->api->resType->resextract(einfo, resexpr, s, m);
        
        if(bsqon && eres.has_value())
        {
            std::optional<std::string> bsqarg = apimodule->api->resType->tobsqarg(pinfo, eres.value(), "");
            eres = bsqarg.value();
        }

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
//Work flow #3 -- Compute an API input
//Given a smt decl that (1) havocs inputs, (2) invokes a call
//      + a signature, smt output name, and JSON result 
//Either:
//  Prove unsat and return the JSON payload -- {result: "infeasible", time: number}
//  Prove sat and return the JSON payload -- {result: "witness", time: number, input: any}
//  Timeout a and return the JSON payload -- {result: "unknown", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowInvert(std::string smt2decl, APIModule* apimodule, json jout, unsigned timeout, bool bsqon)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);
    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    z3::expr_vector chks(c);
    ParseInfo pinfo(apimodule, chks);
  
    auto resvar = c.constant("_@smtres@_value", getZ3SortFor(apimodule, apimodule->api->resType, c));
    auto resval = apimodule->api->resType->toz3arg(pinfo, jout, c).value();
    s.add(resvar == resval);

    s.add(pinfo.chks);

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
            {"result", "infeasible"},
            {"time", delta_ms}
        };
    }
    else
    {
        ExtractionInfo einfo(apimodule, "_@smtres@_value");
        auto m = s.get_model();

        json argv = json::array();
        auto rootctx = einfo.genInitialContext(m);
        for(size_t i = 0; i < apimodule->api->argtypes.size(); ++i)
        {
            auto argtype = apimodule->api->argtypes[i];
            auto ctx = einfo.extendContext(m, rootctx, i);
            auto jarg = argtype->resextract(einfo, ctx, s, m);

            if(!jarg.has_value())
            {
                return {
                    {"result", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            if(!bsqon)
            {
                argv.push_back(jarg.value());
            }
            else
            {
                std::optional<std::string> bsqarg = argtype->tobsqarg(pinfo, jarg.value(), "");
                argv.push_back(bsqarg.value());
            }
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
    bool bsqon = false;
    int argidx = 1;
    if(argc > 1 && std::string(argv[1]) == "--bsqon")
    {
        bsqon = true;
        argidx = 2;
    }

    if(argc > argidx && std::string(argv[argidx]) == "--check")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);

            json result = workflowValidate(smt2decl, apimodule, timeout, bsqon);
            
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

            json result = workflowCompute(smt2decl, apimodule, payload["jin"], timeout, bsqon);
            
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

            json result = workflowInvert(smt2decl, apimodule, payload["jout"], timeout, bsqon);
            
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
        printf("Unknown usage [--bsqon] (--check|--eval|--invert) [file.json]\n");
    }

    return 0;
}
