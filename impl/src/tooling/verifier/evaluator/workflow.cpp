//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "workflow.h"

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
