//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "args.h"

#include <iostream>
#include <fstream>
#include <chrono>

json workflowCheckError(std::string smt2decl, const APIModule* apimodule, const InvokeSignature* apisig, unsigned timeout)
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

    int delta_ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"status", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"status", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        SMTParseJSON jextract;
        json argv = json::array();

        for(size_t i = 0; i < apisig->argtypes.size(); ++i)
        {
            auto rootctx = SMTParseJSON::generateInitialArgContext(c, i);
            auto jarg = apisig->argtypes[i]->textract(jextract, apimodule, rootctx, s);

            if(!jarg.has_value())
            {
                return {
                    {"status", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            argv.push_back(jarg.value());
        }

        return {
            {"status", "witness"},
            {"time", delta_ms},
            {"witness", argv}
        };
    }
}

json workflowTestPass(std::string smt2decl, const APIModule* apimodule, const InvokeSignature* apisig, unsigned timeout)
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

    int delta_ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"status", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"status", "pass"},
            {"time", delta_ms}
        };
    }
    else
    {
        SMTParseJSON jextract;
        json argv = json::array();

        for(size_t i = 0; i < apisig->argtypes.size(); ++i)
        {
            auto rootctx = SMTParseJSON::generateInitialArgContext(c, i);
            auto jarg = apisig->argtypes[i]->textract(jextract, apimodule, rootctx, s);

            if(!jarg.has_value())
            {
                return {
                    {"status", "error"},
                    {"info", "Could not extract arg"}
                };
            }

            argv.push_back(jarg.value());
        }

        return {
            {"status", "witness"},
            {"time", delta_ms},
            {"witness", argv}
        };
    }
}

json workflowEvaluate(std::string smt2decl, const APIModule* apimodule, const InvokeSignature* apisig, json jin, unsigned timeout)
{
    z3::context c;
    z3::solver s(c);

    z3::params p(c);
    p.set(":timeout", timeout);

    //TODO: it would be nice to set a more specifc logic here (than the ALL from the smtfile)
    s.set(p);

    s.from_string(smt2decl.c_str());

    if(!jin.is_array() || jin.size() > apisig->argtypes.size())
    {
        return {
            {"status", "error"},
            {"info", "Bad input arguments"}
        };
    }

    SMTParseJSON jparse;
    for(size_t i = 0; i < jin.size(); ++i)
    {
        auto rootctx = SMTParseJSON::generateInitialArgContext(c, i);
        bool ok = apisig->argtypes[i]->tparse(jparse, apimodule, jin[i], rootctx, s);

        if(!ok)
        {
            return {
                {"status", "error"},
                {"info", "Bad input arguments"}
            };
        }
    }

    //check the formula
    auto start = std::chrono::system_clock::now();
    auto res = s.check();    
    auto end = std::chrono::system_clock::now();

    int delta_ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();    
    if(res == z3::check_result::unknown)
    {
        return {
            {"status", "timeout"},
            {"time", delta_ms}
        };
    }
    else if(res == z3::check_result::unsat)
    {
        return {
            {"status", "unreachable"},
            {"time", delta_ms}
        };
    }
    else
    {
        SMTParseJSON jextract;

        std::cout << s.get_model() << "\n";

        auto rootctx = SMTParseJSON::generateInitialResultContext(c);
        auto jarg = apisig->restype->textract(jextract, apimodule, rootctx, s);

        if(!jarg.has_value())
        {
            return {
                {"status", "error"},
                {"info", "Could not extract arg"}
            };
        }

        return {
            {"status", "output"},
            {"time", delta_ms},
            {"value", jarg.value()}
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
        std::cout << "{\"result\": \"error\", \"info\": \"" << e.what() << "\"}" << std::endl;
        exit(1);
    }
}

int main(int argc, char** argv)
{
    int argidx = 1;

    if(argc > argidx && std::string(argv[argidx]) == "--errorchk")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            const APIModule* apimodule = APIModule::jparse(payload["apimodule"]);
            const InvokeSignature* apisig = apimodule->getSigForFriendlyName(payload["mainfunc"]).value();

            json result = workflowCheckError(smt2decl, apimodule, apisig, timeout);
            
            std::cout << result << std::endl;
            fflush(stdout);
        }
        catch(const std::exception& e)
        {
            std::cout << "{\"result\": \"error\", \"info\": \"" << e.what() << "\"}" << std::endl;
            fflush(stdout);
            exit(1);
        }
    }
    else if(argc > argidx && std::string(argv[argidx]) == "--passchk")
    {
        json payload = getPayload(argc, argv, argidx);

        try
        {
            std::string smt2decl = payload["smt2decl"].get<std::string>();
            unsigned timeout = payload["timeout"].get<unsigned>();
            APIModule* apimodule = APIModule::jparse(payload["apimodule"]);
            const InvokeSignature* apisig = apimodule->getSigForFriendlyName(payload["mainfunc"]).value();

            json result = workflowTestPass(smt2decl, apimodule, apisig, timeout);
            
            std::cout << result << std::endl;
            fflush(stdout);
        }
        catch(const std::exception& e)
        {
            std::cout << "{\"result\": \"error\", \"info\": \"" << e.what() << "\"}" << std::endl;
            fflush(stdout);
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
            const InvokeSignature* apisig = apimodule->getSigForFriendlyName(payload["mainfunc"]).value();

            json result = workflowEvaluate(smt2decl, apimodule, apisig, payload["jin"], timeout);
            
            std::cout << result << std::endl;
            fflush(stdout);
        }
        catch(const std::exception& e)
        {
            std::cout << "{\"result\": \"error\", \"info\": \"" << e.what() << "\"}" << std::endl;
            fflush(stdout);
            exit(1);
        }
    }
    else
    {
        printf("Unknown usage (--errorchk|--passchk|--eval) [file.json]\n");
    }

    return 0;
}
