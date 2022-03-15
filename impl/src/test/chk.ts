//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as readline from "readline";

import { PackageConfig, SymbolicActionMode } from "../compiler/mir_assembly";
import { generateStandardVOpts, workflowEmitToFile, workflowEvaluate, workflowLoadUserSrc, workflowPassCheck } from "../tooling/checker/smt_workflows";

const mode = process.argv[2];
const args = process.argv.slice(3);

const usercode = workflowLoadUserSrc(args);
if(usercode === undefined) {
    process.stdout.write("Could not load code files\n");
    process.exit(1);
}

const TIMEOUT = 10000;
const STD_OPTS = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);
const EVAL_OPTS = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);

const noerrtrgt = {file: "[No Error Trgt]", line: -1, pos: -1};
const userpackage = new PackageConfig([], usercode);

if(mode === "-smt") {
    const ofile = args[0].slice(0, args[0].length - 3) + "smt2";
    process.stdout.write(`Writing file to ${ofile}\n`);

    workflowEmitToFile(ofile, userpackage, "debug", false, TIMEOUT, STD_OPTS, {filename: args[0], name: "main", fkey: "__i__Main::main"}, noerrtrgt, true);
}
else if(mode === "-test") {
    workflowPassCheck(userpackage, "debug", false, TIMEOUT, STD_OPTS, {filename: args[0], name: "main", fkey: "__i__Main::main"}, (res: string) => {
        process.stdout.write(res + "\n");
    });
}
else if(mode === "-ttout") {
    const ofile = args[0].slice(0, args[0].length - 3) + "json";
    process.stdout.write(`Writing file to ${ofile}\n`);

    workflowEmitToFile(ofile, userpackage, "debug", false, TIMEOUT, STD_OPTS, {filename: args[0], name: "main", fkey: "__i__Main::main"}, noerrtrgt, false);
}
else if(mode === "-eeout") {
    const ofile = args[0].slice(0, args[0].length - 3) + "json";
    process.stdout.write(`Writing file to ${ofile}\n`);

    workflowEmitToFile(ofile, userpackage, "debug", false, TIMEOUT, EVAL_OPTS, {filename: args[0], name: "main", fkey: "__i__Main::main"}, noerrtrgt, false);
}
else if (mode === "-eval") {
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jinput = JSON.parse(input) as any[];
            workflowEvaluate(userpackage, "debug", false, TIMEOUT, EVAL_OPTS, {filename: args[0], name: "main", fkey: "__i__Main::main"}, jinput, (res: string) => {
                try {
                    const jres = JSON.parse(res);

                    if (jres["status"] === "unreachable") {
                        process.stdout.write(`No valid (non error) result exists for this input!\n`);
                    }
                    else if (jres["status"] === "output") {
                        process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                        process.stdout.write(JSON.stringify(jres["value"], undefined, 2) + "\n");
                    }
                    else if (jres["status"] === "timeout") {
                        process.stdout.write(`Solver timeout :(\n`);
                    }
                    else {
                        process.stdout.write(`Failed with -- ${JSON.stringify(jres)}`);
                    }

                    process.exit(0);
                }
                catch (ex) {
                    process.stderr.write(`Failure ${ex}\n`);
                    process.exit(1);
                }
            });
        }
        catch (ex) {
            process.stderr.write(`Failure ${ex}\n`);
            process.exit(1);
        }
    });
}
else {
    process.stdout.write("usage: node check.js <-smt | -test | -ttout | -eeout | -eval> file.bsq");
    process.exit(0);
}
