//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "decls.h"

////
//Work flow #1 -- Refute or Witness an Error
//Given a smt decl that (1) havocs inputs, (2) invokes a call, (3) asserts the result is the error
//      + a signature, and bvsize
//Either:
//  Prove unsat and return the JSON payload -- {result: "infeasible", time: number}
//  Prove sat and return the JSON payload -- {result: "witness", time: number, input: any}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowValidate(std::string smt2decl, APIModule* apimodule, std::string signame, size_t bvsize)
{
    z3::context c;
    z3::solver s(c);
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
            {"result", "infeasible"},
            {"time", delta_ms}
        };
    }
    else
    {
        auto m = s.get_model();
        ExtractionInfo einfo(apimodule->typemap, bvsize, &c, &m);

        auto sig = std::find_if(apimodule->siglist.cbegin(), apimodule->siglist.cend(), [&signame](const InvokeSignature* sig) {
            return sig->name == signame;
        });

        json argv = json::array();
        auto rootctx = einfo.initialArgsContext();
        for(size_t i = 0; i < (*sig)->argTypes.size(); ++i)
        {
            auto argtype = (*sig)->argTypes[i];
            auto ctx = einfo.stepContext(rootctx, i);
            auto jarg = argtype->extract(&einfo, ctx);

            argv.push_back(jarg);
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
//  Compute the output of the function return the JSON payload -- {result: "result" | "infeasible", time: number, output: JSON}
//  Timeout a and return the JSON payload -- {result: "timeout", time: number}
//  Main should also handle exceptions and -- {result: "error", info: string}

json workflowCompute(std::string smt2decl, APIModule* apimodule, std::string signame)
{
    z3::context c;
    z3::solver s(c);
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
            {"result", "infeasible"},
            {"time", delta_ms}
        };
    }
    else
    {
        xxxx;

        auto m = s.get_model();
        ExtractionInfo einfo(apimodule->typemap, 64, &c, &m);

        auto sig = std::find_if(apimodule->siglist.cbegin(), apimodule->siglist.cend(), [&signame](const InvokeSignature* sig) {
            return sig->name == signame;
        });

        json argv = json::array();
        auto rootctx = einfo.initialArgsContext();
        for(size_t i = 0; i < (*sig)->argTypes.size(); ++i)
        {
            auto argtype = (*sig)->argTypes[i];
            auto ctx = einfo.stepContext(rootctx, i);
            auto jarg = argtype->extract(&einfo, ctx);

            argv.push_back(jarg);
        }

        return {
            {"result", "witness"},
            {"time", delta_ms},
            {"input", argv}
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

void find_model_example1() 
{
    z3::context c;
    z3::solver s(c);
    s.from_file("C:\\Users\\marron\\Desktop\\doit.smt2");

    std::cout << "Loaded\n";

    //check the formula
    auto res = s.check();
    if(res == z3::check_result::unsat)
    {
         std::cout << "Error is unreachable under restrictions!!!" << "\n";
    }
    else
    {
        std::cout << "Error is reachable -- attempting to extract witness input..." << "\n";

        z3::model m = s.get_model();
        
        std::cout << "Getting constructor functions..." << "\n";

        std::map<std::string, std::optional<z3::func_decl>> consfuncs;
        for (unsigned i = 0; i < m.size(); i++) 
        {
            z3::func_decl v = m[i];
            if(!m.has_interp(v))
            {
                continue;
            }

            auto name = v.name().str();
            if(name == "Ctx@MakeStep")
            {
                consfuncs["MakeStep"] = v;
            }
            else if(name == "BNone@UFCons_API")
            {
                consfuncs["NSCore::None"] = v;
            }
            else if(name == "BBool@UFCons_API")
            {
                consfuncs["NSCore::Bool"] = v;
            }
            else if(name == "BInt@UFCons_API")
            {
                consfuncs["NSCore::Int"] = v;
            }
            else if(name == "BNat@UFCons_API")
            {
                consfuncs["NSCore::Nat"] = v;
            }
            else if(name == "BBigInt@UFCons_API")
            {
                consfuncs["NSCore::BigInt"] = v;
            }
            else if(name == "BBigNat@UFCons_API")
            {
                consfuncs["NSCore::BigNat"] = v;
            }
            else if(name == "BFloat@UFCons_API")
            {
                consfuncs["NSCore::Float"] = v;
            }
            else if(name == "BDecimal@UFCons_API")
            {
                consfuncs["NSCore::Decimal"] = v;
            }
            else if(name == "BRational@UFCons_API")
            {
                consfuncs["NSCore::Rational"] = v;
            }
            else if(name == "BString@UFCons_API")
            {
                consfuncs["NSCore::String"] = v;
            }
            else if(name == "BISOTime@UFCons_API")
            {
                consfuncs["NSCore::ISOTime"] = v;
            }
            else if(name == "BLogicalTime@UFCons_API")
            {
                consfuncs["NSCore::LogicalTime"] = v;
            }
            else if(name == "BUUID@UFCons_API")
            {
                consfuncs["NSCore::UUID"] = v;
            }
            else if(name == "BContentHash@UFCons_API")
            {
                consfuncs["NSCore::ContentHash"] = v;
            }
            else if(name == "ListSize@UFCons_API")
            {
                consfuncs["ListSize"] = v;
            }
            else if(name == "UnionItem@UFCons_API")
            {
                consfuncs["UnionItem"] = v;
            }
            else
            {
                ;
            }
        }

        auto ictx = z3::concat(consfuncs["MakeStep"].value()(c.bv_val(0, 5)), consfuncs["MakeStep"].value()(c.bv_val(0, 5))); 
        std::cout << "ictx = " << m.eval(ictx, true) << "\n";

        auto argv = consfuncs["NSCore::Nat"].value()(ictx);
        std::cout << "arg = " << m.eval(argv, true) << "\n";
    }

    /*
    z3::model m = s.get_model();
    std::cout << m << "\n";
    // traversing the model
    for (unsigned i = 0; i < m.size(); i++) {
        z3::func_decl v = m[i];
        // this problem contains only constants
        assert(v.arity() == 0); 
        std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
    }
    // we can evaluate expressions in the model.
    std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";
    */
}


int main(int argc, char** argv)
{
    find_model_example1();

    return 0;
}
