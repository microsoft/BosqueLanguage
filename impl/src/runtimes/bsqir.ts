//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import chalk from "chalk";
import * as readline from "readline";

import { DEFAULT_TOPTS, workflowEmitICPPFile, workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";

const mode = process.argv[2];
const args = process.argv.slice(mode === "--output" ? 4 : 3);

if (args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file as argument\n"));
    process.exit(1);
}

process.stdout.write(`Processing Bosque sources in:\n${args.join("\n")}\n...\n`);

if (mode === "--output") {
    process.stdout.write(`Processing and writing IR to ${process.argv[3]}...\n`);
    const ok = workflowEmitICPPFile(process.argv[3], args, DEFAULT_TOPTS, "NSMain::main");
    if(ok) {
        process.stdout.write("done");
    }
    else {
        process.stdout.write(chalk.red("failed to generate IR"));
    }
}
else {
    const files = args;
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jargs = JSON.parse(input);

            process.stdout.write(`Evaluating...\n`);

            const res = workflowRunICPPFile(jargs, files, DEFAULT_TOPTS, "NSMain::main");
            
            if (res !== undefined) {
                process.stdout.write(`${res}\n`);
            }
            else {
                process.stdout.write(`failure\n`);
            }
        }
        catch (ex) {
            process.stderr.write(`Failure ${ex}\n`)
        }
    });
}

