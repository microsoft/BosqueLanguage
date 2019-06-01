//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Interpreter } from "../interpreter/interpreter";
import { TestInfo } from "./test_runner";
import { ValueOps } from "../interpreter/value";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";

const regression_test = `
namespace NSTestRegression;

entrypoint function stringTIncludes(): Bool {
    var test = "a";
    return test->includes("a");
}

function allOdd(...args: List[Int]): Bool {
    return args->all(fn(x) => x % 2 == 1);
}

entrypoint function invokeLambdaInfer(): Bool {
    return allOdd(1, 3, 4);
}

function convert(x: Any) : Int {
    return x->as[Int]();
}

entrypoint function vInvoke1(): Int {
    var x: Int = 3;
    return convert(x);
}

entrypoint function vInvoke2(): Int {
    var x: String = "ok";
    return convert(x);
}

function phimulti_doit(x: Int): Int
{
    var! res = 1;
    if (x == 1) {
        res = 2;
    }
    elif (x == 2) {
        ;
    }
    else {
        ;
    }

    return res;
}

entrypoint function phimulti(): Bool {
    var r1 = phimulti_doit(1);
    var r2 = phimulti_doit(2);
    var r3 = phimulti_doit(3);
    return r1 == 2 && r2 == r3;
}

function argTypeFlow(x?: Int): Int {
    if(x == none) {
        return 0;
    }

    return x + 1;
}

entrypoint function argTypeFlow_entry(x?: Int): Int {
    return argTypeFlow() + argTypeFlow(0);
}
`;

const regression_tests: TestInfo[] = [
    { name: "stringTIncludes", input: ["stringTIncludes"], expected: "true" },
    { name: "invokeLambdaInfer", input: ["invokeLambdaInfer"], expected: "false" },
    { name: "vInvoke1", input: ["vInvoke1"], expected: "3" },
    { name: "vInvoke2", input: ["vInvoke2"], expected: "[NO RESULT]", expectedError: true },
    { name: "phimulti", input: ["phimulti"], expected: "true" },
    { name: "argTypeFlow_entry", input: ["argTypeFlow_entry"], expected: "1" },
];

function regression_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "regression_tests.bsq", contents: regression_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function regression_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestRegression", args[0], []));
}

const testRegression = { name: "Regressions", setup: regression_setup, action: regression_action, tests: regression_tests, xmlid: "RegressionUnitTests" };

export { testRegression };
