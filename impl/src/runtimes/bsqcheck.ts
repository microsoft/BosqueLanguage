//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import *  as readline from "readline";

import { DEFAULT_TIMEOUT, DEFAULT_VOPTS, workflowBSQCheck, workflowBSQSingle, workflowEmitToFile, workflowEvaluateSingle, workflowGetErrors, workflowInvertSingle } from "../tooling/verifier/smt_workflows";

function parseLocation(location: string): { file: string, line: number, pos: number } | undefined {
    try {
        const errfile = location.slice(0, location.indexOf("@"));
        const errline = Number.parseInt(location.slice(location.indexOf("@") + 1, location.indexOf("#")));
        const errpos = Number.parseInt(location.slice(location.indexOf("#") + 1));
        return { file: errfile, line: errline, pos: errpos };
    }
    catch (ex) {
        return undefined;
    }
}

const mode = process.argv[1];

if(mode === "--output") {
    const into = process.argv[2];
    process.stdout.write(`Writing SMT file to ${into}`);

    const mode = process.argv[3];
    if(mode !== "check" && mode !== "evaluate" && mode !== "invert") {
        process.stdout.write("Valid mode options are check | evaluate | invert\n");
        process.exit(1);
    }

    const location = parseLocation(process.argv[4]);
    if(location === undefined) {
        process.stdout.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = process.argv.slice(5);

    workflowEmitToFile(into, files, mode as "check" | "evaluate" | "invert", DEFAULT_TIMEOUT, DEFAULT_VOPTS, location, "NSMain::main")
}
else if(mode === "--chksingle") {
    const location = parseLocation(process.argv[2]);
    if(location === undefined) {
        process.stderr.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = process.argv.slice(3);

    const res = workflowBSQSingle(true, files, DEFAULT_VOPTS, DEFAULT_TIMEOUT, location, "NSMain::main");
    process.stdout.write(res);
}
else if(mode === "--chk") {
    const files = process.argv.slice(2);
    const errors = workflowGetErrors(files, DEFAULT_VOPTS, "NSMain::main");
    if(errors === undefined) {
        process.stdout.write("Failed to load error lines\n");
        process.exit(1);
    }

    //
    //TODO: we probably want to make this a process parallel process
    //
    for(let i = 0; i < errors.length; ++i) {
        process.stdout.write(`Checking error ${errors[i].msg} at ${errors[i].file}@${errors[i].line}...\n`);
        const res = workflowBSQCheck(true, files, DEFAULT_TIMEOUT, errors[i], "NSMain::main", true);
        const jres = JSON.parse(res);

        if(jres["result"] === "infeasible") {
            process.stdout.write(`Proved infeasible in ${jres["time"]} millis!\n`);
        }
        else if(jres["result"] === "witness") {
            process.stdout.write(`Generated witness input in ${jres["time"]} millis!\n`);
            process.stdout.write(jres["input"] + "\n");
        }
        else if(jres["result"] === "timeout") {
            process.stdout.write(`Solver timeout :(\n`);
        }
        else {
            process.stdout.write(`Failed with -- ${jres}`);
        }
    }
}
else if(mode === "--evaluate") {
    const files = process.argv.slice(2);
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jinput = JSON.parse(input) as any[];

            const res = workflowEvaluateSingle(true, files, jinput, DEFAULT_VOPTS, DEFAULT_TIMEOUT, "NSMain::main");
            const jres = JSON.parse(res);

            if (jres["result"] === "infeasible") {
                process.stdout.write(`No valid (non error) result exists for this input!\n`);
            }
            else if (jres["result"] === "output") {
                process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                process.stdout.write(jres["output"] + "\n");
            }
            else if (jres["result"] === "timeout") {
                process.stdout.write(`Solver timeout :(\n`);
            }
            else {
                process.stdout.write(`Failed with -- ${jres}`);
            }
        }
        catch (ex) {
            process.stderr.write(`Failure ${ex}\n`)
        }
    });
}
else if(mode === "--invert") {
    const files = process.argv.slice(2);
    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const joutput = JSON.parse(input);

            const res = workflowInvertSingle(true, files, joutput, DEFAULT_VOPTS, DEFAULT_TIMEOUT, "NSMain::main");
            const jres = JSON.parse(res);

            if (jres["result"] === "infeasible") {
                process.stdout.write(`No valid (non error) input exists for this input!\n`);
            }
            else if (jres["result"] === "witness") {
                process.stdout.write(`Generated candidate input in ${jres["time"]} millis!\n`);
                process.stdout.write(jres["input"] + "\n");
            }
            else if (jres["result"] === "timeout") {
                process.stdout.write(`Solver timeout :(\n`);
            }
            else {
                process.stdout.write(`Failed with -- ${jres}`);
            }
        }
        catch (ex) {
            process.stderr.write(`Failure ${ex}\n`)
        }
    });
}
else {
    const files = process.argv.slice(2);
    const errors = workflowGetErrors(files, DEFAULT_VOPTS, "NSMain::main");
    if(errors === undefined) {
        process.stderr.write("Failed to load error lines\n");
        process.exit(1);
    }

    process.stdout.write("Possible Errors:\n");
    process.stdout.write(JSON.stringify(errors, undefined, 2) + "\n");
}
