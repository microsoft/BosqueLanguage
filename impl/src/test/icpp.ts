//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import chalk from "chalk";
import * as readline from "readline";

import { PackageConfig } from "../compiler/mir_assembly";
import { workflowEmitICPPFile, workflowLoadUserSrc, workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";

const mode = process.argv[2];
const args = process.argv.slice(mode === "--output" ? 4 : 3);

if (args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file as argument\n"));
    process.exit(1);
}

const usercode = workflowLoadUserSrc(args);
if(usercode === undefined) {
    process.stdout.write("Could not load code files\n");
    process.exit(1);
}

const userpackage = new PackageConfig([], usercode);

process.stdout.write(`Processing Bosque sources in:\n${args.join("\n")}\n...\n`);

if (mode === "-output") {
    process.stdout.write(`Processing and writing IR to ${process.argv[3]}...\n`);
    const ok = workflowEmitICPPFile(process.argv[3], userpackage, false, {}, {filename: args[0], names: ["Main::main"]});
    if(ok) {
        process.stdout.write("done\n");
    }
    else {
        process.stdout.write(chalk.red("failed to generate IR"));
    }
}
else {
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jargs = JSON.parse(input);

            process.stdout.write(`Evaluating...\n`);

            workflowRunICPPFile(jargs, userpackage, false, {}, {filename: args[0], names: ["Main::main"]}, (result: string | undefined) => {
                if (result !== undefined) {
                    process.stdout.write(`${result}\n`);
                }
                else {
                    process.stdout.write(`failure\n`);
                }

                process.exit(0);
            });
        }
        catch (ex) {
            process.stderr.write(`Failure ${ex}\n`);
            process.exit(1);
        }
    });
}
