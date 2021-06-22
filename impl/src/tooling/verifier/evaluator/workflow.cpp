//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "workflow.h"

void find_model_example1() {
    std::cout << "find_model_example1\n";
    z3::context c;
    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::solver s(c);

    s.add(x >= 1);
    s.add(y < x + 3);
    std::cout << s.check() << "\n";

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
}


int main(int argc, char** argv)
{
    find_model_example1();

    return 0;
}