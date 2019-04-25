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
`;

const regression_tests: TestInfo[] = [
    { name: "stringTIncludes", input: ["stringTIncludes"], expected: "true" },
    { name: "invokeLambdaInfer", input: ["invokeLambdaInfer"], expected: "false" },
    { name: "vInvoke1", input: ["vInvoke1"], expected: "3" },
    { name: "vInvoke2", input: ["vInvoke2"], expected: "[NO RESULT]", expectedError: true }
];

function regression_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "regression_tests.fl", contents: regression_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function regression_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestRegression", args[0], []));
}

const testRegression = { name: "Regressions", setup: regression_setup, action: regression_action, tests: regression_tests, xmlid: "RegressionUnitTests" };

export { testRegression };
