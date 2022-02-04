//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as readline from "readline";

import { PackageConfig, SymbolicActionMode } from "../compiler/mir_assembly";
import { generateStandardVOpts, workflowEmitToFile, workflowEvaluate, workflowLoadUserSrc, workflowPassCheck } from "../tooling/verifier/smt_workflows";

const mode = process.argv[2];
const args = process.argv.slice((mode === "--output" || mode === "--smt") ? 4 : 3);

const usercode = workflowLoadUserSrc(args);
if(usercode === undefined) {
    process.stdout.write("Could not load code files\n");
    process.exit(1);
}

const TIMEOUT = 30;
const STD_OPTS = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);
const EVAL_OPTS = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);

const noerrtrgt = {file: "[No Error Trgt]", line: -1, pos: -1};
const userpackage = new PackageConfig([], usercode);

if(mode === "--output") {
    process.stdout.write(`Writing file to ${process.argv[3]}\n`);

    workflowEmitToFile(process.argv[3], userpackage, false, TIMEOUT, STD_OPTS, {filename: args[0], name: "Main::main"}, noerrtrgt, false);
}
else if(mode === "--smt") {
    process.stdout.write(`Writing file to ${process.argv[3]}\n`);

    workflowEmitToFile(process.argv[3], userpackage, false, TIMEOUT, STD_OPTS, {filename: args[0], name: "Main::main"}, noerrtrgt, true);
}
else if(mode === "--test") {
    workflowPassCheck(userpackage, false, TIMEOUT, STD_OPTS, {filename: args[0], name: "Main::main"}, (res: string) => {
        process.stdout.write(res + "\n");
    });
}
else {
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jinput = JSON.parse(input) as any[];
            workflowEvaluate(userpackage, false, TIMEOUT, EVAL_OPTS, {filename: args[0], name: "Main::main"}, jinput, (res: string) => {
                try {
                    const jres = JSON.parse(res);

                    if (jres["result"] === "unreachable") {
                        process.stdout.write(`No valid (non error) result exists for this input!\n`);
                    }
                    else if (jres["result"] === "output") {
                        process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                        process.stdout.write(JSON.stringify(jres["output"], undefined, 2) + "\n");
                    }
                    else if (jres["result"] === "timeout") {
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
