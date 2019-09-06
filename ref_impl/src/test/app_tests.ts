//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Interpreter } from "../interpreter/interpreter";
import { TestInfo, TestSet } from "./test_runner";
import { ValueOps } from "../interpreter/value";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";

import * as FS from "fs";

function appTestGenerator(app: string, expected: string): TestSet {
    const app_tests: TestInfo[] = [
        { name: "main", input: [], expected: expected }
    ];

    function setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
        const appdata = FS.readFileSync("./src/test/apps/" + app + "/main.bsq").toString();

        const files = core.concat([{ relativePath: "corelib_tests.bsq", contents: appdata }]);

        const cu = MIREmitter.generateMASM(new PackageConfig(), true, true, true, files);
        if (cu.masm === undefined || cu.errors.length !== 0) {
            return cu;
        }
        else {
            const jmasm = JSON.stringify(cu.masm.jemit());
            const rtmasm = MIRAssembly.jparse(JSON.parse(jmasm));
            if (jmasm !== JSON.stringify(rtmasm.jemit())) {
                return { masm: undefined, errors: ["Bad serialize round-trip"] };
            }

            return { masm: rtmasm, errors: [] };
        }
    }

    function action(assembly: MIRAssembly, args: any[]): any {
        let ip = new Interpreter(assembly, true, true, true);
        return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSMain", "main", args));
    }

    return { name: app, setup: setup, action: action, tests: app_tests, xmlid: "AppUnitTest_" + app };
}

const applist = [
    {app: "angles", expected: "NSMain::Angle{ degrees=221, primes=1, seconds=0 }"},
    {app: "max", expected: "20"},
    {app: "nbody", expected: "-0.16907302171469984"},
    {app: "tictactoe", expected: "NSMain::Game{ board=NSMain::Board{ cells=NSCore::List<T=NSCore::None|NSCore::StringOf<NSMain::PlayerMark>>{ none, NSMain::PlayerMark'o', NSMain::PlayerMark'o', NSMain::PlayerMark'x', NSMain::PlayerMark'x', NSMain::PlayerMark'x', none, none, none } }, winner=NSMain::PlayerMark'x' }"},
];

const tests = applist.map((entry) => appTestGenerator(entry.app, entry.expected));

export { tests };
