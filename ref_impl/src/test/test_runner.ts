//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as BasicExpresion from "./basic_evaluation_test";
import * as Libraries from "./library_tests";
import * as Regressions from "./regression_tests";

import * as Apps from "./app_tests";

import * as FS from "fs";
import chalk from "chalk";
import { RuntimeError } from "../interpreter/interpreter_environment";
import { MIRAssembly } from "../compiler/mir_assembly";

const testxml = `<?xml version="1.0" encoding="UTF-8"?>
<testsuites>
  TSLIST
</testsuites>`;

type TestInfo = {
    name: string;
    input: any[];
    expected: any;
    expectedError?: boolean;
};

type TestSet = {
    readonly name: string;
    readonly setup: (core: { relativePath: string, contents: string }[]) => { masm: MIRAssembly | undefined, errors: string[] };
    readonly action: (assembly: MIRAssembly, input: any[]) => any;
    readonly tests: TestInfo[];
    readonly xmlid: string
};

class TestRunner {
    readonly core: { relativePath: string, contents: string }[];
    testSets: TestSet[];

    constructor(core: { relativePath: string, contents: string }[]) {
        this.core = core;
        this.testSets = [];
    }

    addSet(testSet: TestSet) {
        this.testSets.push(testSet);
    }

    private runSingle(ts: TestSet, id: number): [number, string] {
        process.stdout.write("--------\n");
        process.stdout.write(`Running ${chalk.bold(ts.name)} suite with ${chalk.bold(ts.tests.length.toString())} tests...\n`);

        let fail = 0;
        const { masm, errors } = ts.setup(this.core);

        const tsstring = new Date().toISOString().slice(0, -5);
        const start = Date.now();
        if (errors.length !== 0) {
            for (let j = 0; j < errors.length; ++j) {
                process.stdout.write(chalk.red(`Compiler error: ${errors[j]}\n`));
            }

            const tsinfoerr = `<testsuite name="${ts.xmlid}" tests="${ts.tests.length}" errors="1" failures="0" id="${id}" time="${0}" timestamp="${tsstring}" hostname="localhost" package="${ts.xmlid}"><properties></properties><system-out/><system-err/><testcase name="Compile and Type Check" class="" time="0.0"/></testsuite>`;
            return [ts.tests.length, tsinfoerr];
        }

        let tresults: string[] = [];
        for (let i = 0; i < ts.tests.length; ++i) {
            process.stdout.write(`Running ${ts.tests[i].name}...`);

            const tstart = Date.now();
            let res: any = undefined;
            try {
                res = ts.action(masm as MIRAssembly, ts.tests[i].input);
                if (res === ts.tests[i].expected) {
                    process.stdout.write(chalk.green("pass\n"));
                    tresults.push(`<testcase name="${ts.tests[i].name}" class="" time="${(Date.now() - tstart) / 1000}"/>`);

                }
                else {
                    fail++;
                    const failmsg = `fail with ${res} expected ${ts.tests[i].expected}`;
                    tresults.push(`<testcase name="${ts.tests[i].name}" class="" time="${(Date.now() - tstart) / 1000}"><failure message="${failmsg}"/></testcase>`);

                    process.stdout.write(chalk.red(`${failmsg}\n`));
                }
            }
            catch (ex) {
                if (ts.tests[i].expectedError && ex instanceof RuntimeError) {
                    process.stdout.write(chalk.green("pass\n"));
                    tresults.push(`<testcase name="${ts.tests[i].name}" class="" time="${(Date.now() - tstart) / 1000}"/>`);

                }
                else {
                    fail++;
                    const failmsg = `fail with exception -- ${ex}`;
                    tresults.push(`<testcase name="${ts.tests[i].name}" class="" time="${(Date.now() - tstart) / 1000}"><failure message="${failmsg}"/></testcase>`);

                    process.stdout.write(chalk.red(`${failmsg}\n`));
                }
            }
        }

        const tsinfook = `<testsuite name="${ts.xmlid}" tests="${ts.tests.length}" errors="0" failures="${fail}" id="${id}" time="${(Date.now() - start) / 1000}" timestamp="${tsstring}" hostname="localhost" package="${ts.xmlid}"><properties></properties><system-out/><system-err/>${tresults.join("\n")}</testsuite>`;

        if (fail === 0) {
            process.stdout.write(chalk.green("Completed successfully.\n\n"));
            return [fail, tsinfook];
        }
        else {
            process.stdout.write(chalk.red(`Completed with ${chalk.bold(fail.toString())} failures.\n\n`));
            return [fail, tsinfook];
        }
    }

    run() {
        let fail = 0;

        let tr = [];
        for (let i = 0; i < this.testSets.length; ++i) {
            const [tfail, info] = this.runSingle(this.testSets[i], i);
            if (tfail !== 0) {
                fail++;
            }

            tr.push(info);
        }

        FS.writeFileSync("TEST-RESULTS.xml", testxml.replace("TSLIST", tr.join("\n")));

        if (fail === 0) {
            process.stdout.write(chalk.green(chalk.bold(`\nAll ${this.testSets.length} test suites passed!\n`)));
        }
        else {
            process.stdout.write(chalk.red(chalk.bold(`\n${fail} test suites had failures...\n`)));
        }
    }
}

function runAll() {
    const coredir = "./src/core/core.bsq";
    const coredata = FS.readFileSync(coredir).toString();

    const collectionsdir = "./src/core/collections.bsq";
    const collectionsdata = FS.readFileSync(collectionsdir).toString();

    const runner = new TestRunner([{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }]);

    runner.addSet(BasicExpresion.testExpression);
    runner.addSet(BasicExpresion.testStatement);

    runner.addSet(Libraries.testCoreLibs);
    runner.addSet(Libraries.testCollectionLibs);

    runner.addSet(Regressions.testRegression);

    Apps.tests.forEach((test) => runner.addSet(test));

    runner.run();
}

export { runAll, TestInfo, TestSet };

////
//Entrypoint

setImmediate(() => runAll());
