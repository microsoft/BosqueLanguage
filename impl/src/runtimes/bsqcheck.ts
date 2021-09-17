//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import chalk from "chalk";
import * as readline from "readline";
import * as path from "path";

import { AssemblyFlavor, DEFAULT_TIMEOUT, workflowBSQCheck, workflowBSQInfeasibleSingle, workflowBSQWitnessSingle, workflowEmitToFile, workflowEvaluateSingle, workflowGetErrors, workflowInvertSingle, workflowLoadUserSrc } from "../tooling/verifier/smt_workflows";
import { VerifierOptions } from "../tooling/verifier/smt_exp";

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

const mode = process.argv[2];
const args = process.argv.slice(3);

if(mode === "--output") {
    let smtmode = args[0];
    if(smtmode !== "unreachable" && smtmode !== "witness" && smtmode !== "evaluate" && smtmode !== "invert") {
        process.stdout.write("Valid mode options are unreachable | witness | evaluate | invert\n");
        process.exit(1);
    }

    const smtonly = args[1] === "--smt";

    const location = parseLocation(args[smtonly ? 2 : 1]);
    if(location === undefined) {
        process.stdout.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = args.slice(smtonly ? 3 : 2);
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const fparse = path.parse(files[0]);
    const into = path.join(fparse.dir, fparse.name + (smtonly ? ".smt2" : ".json"));
    process.stdout.write(`Writing file to ${into}\n`);

    const asmflavor = smtmode === "unreachable" ? AssemblyFlavor.UFOverApproximate : AssemblyFlavor.RecuriveImpl;

    const vopts = {
        ISize: 8,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: smtmode === "unreachable" ? false : true,
        EnableCollection_LargeHavoc: smtmode === "unreachable" ? true : false,
        EnableCollection_SmallOps: smtmode === "unreachable" ? false : true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    workflowEmitToFile(into, usercode, asmflavor, smtmode, DEFAULT_TIMEOUT, vopts, location, "NSMain::main", smtonly)
}
else if(mode === "--unreachable") {
    const location = parseLocation(args[0]);
    if(location === undefined) {
        process.stderr.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = args.slice(1);
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const vopts = {
        ISize: 8,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: false,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: false,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    workflowBSQInfeasibleSingle(usercode, vopts, DEFAULT_TIMEOUT, location, "NSMain::main", (res: string) => {
        process.stdout.write(res + "\n");
    });
}
else if(mode === "--smallwitness") {
    const location = parseLocation(args[0]);
    if(location === undefined) {
        process.stderr.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = args.slice(1);
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const vopts = {
        ISize: 5,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: false,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: false
    } as VerifierOptions;

    workflowBSQWitnessSingle(usercode, vopts, DEFAULT_TIMEOUT, location, "NSMain::main", (res: string) => {
        process.stdout.write(res + "\n");
    });
}
else if(mode === "--largewitness") {
    const location = parseLocation(args[0]);
    if(location === undefined) {
        process.stderr.write("Location should be of the form file.bsq@line#pos\n");
        process.exit(1);
    }

    const files = args.slice(1);
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const vopts = {
        ISize: 8,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    workflowBSQWitnessSingle(usercode, vopts, DEFAULT_TIMEOUT, location, "NSMain::main", (res: string) => {
        process.stdout.write(res + "\n");
    });
}
else if(mode === "--check") {
    const printprocess = (args[0] === "--verbose");
    const quiet = (args[0] === "--quiet");
    const files = args.slice((printprocess || quiet) ? 1 : 0);
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const error_vopts = {
        ISize: 64,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: false,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: false,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    const errors = workflowGetErrors(usercode, error_vopts, "NSMain::main");
    if(errors === undefined) {
        process.stdout.write("Failed to load error lines\n");
        process.exit(1);
    }

    if(errors.length === 0) {
        process.stdout.write(chalk.green("No errors are possible in this program!\n"));
        process.exit(0);
    }

    process.stdout.write(chalk.bold(`Analyzing ${errors.length} possible error(s) in program...\n`));

    //
    //TODO: we probably want to make this a process parallel process
    //
    let icount = 0;
    let wcount = 0;
    let pcount = 0;
    let ecount = 0;
    let fcount = 0;
    let witnesslist: {msg: string, position: string, input: any[]}[] = [];
    for(let i = 0; i < errors.length; ++i) {
        if(!quiet) {
            process.stdout.write(`Checking error ${errors[i].msg} at ${errors[i].file}@${errors[i].line}#${errors[i].pos}...\n`);
        }

        const jres = workflowBSQCheck(usercode, DEFAULT_TIMEOUT, errors[i], "NSMain::main", printprocess);

        if(jres === undefined) {
            if(!quiet) {
                process.stdout.write(`Failed with internal errors :(\n`);
            }
            fcount++;
        }
        else if(jres.result === "unreachable") {
            if(!quiet) {
                process.stdout.write(`Proved unreachable in ${jres.time}s!\n`);
            }
            icount++;
        }
        else if(jres.result === "witness") {
            if(!quiet) {
                process.stdout.write(`Generated witness input in ${jres.time}s!\n`);
                //process.stdout.write(`${jres.input}\n`);
            }
            wcount++;
            witnesslist.push({msg: errors[i].msg, position: `line ${errors[i].line} in ${errors[i].file}`, input: jres.input});
        }
        else if(jres.result === "partial") {
            if(!quiet) {
                process.stdout.write(`Proved unreachable on limited space.\n`);
            }
            pcount++;
        }
        else {
            if(!quiet) {
                process.stdout.write(`Exhausted resource bounds without finding failures.\n`);
            }
            ecount++;
        }
    }

    if(fcount !== 0) {
        process.stdout.write(chalk.yellow(`Failed on ${fcount} error(s)!\n`));
    }

    if(icount !== 0) {
        process.stdout.write(chalk.green(`Proved ${icount} error(s) unreachable on all executions!\n`));
    }

    if(wcount !== 0) {
        process.stdout.write(chalk.red(`Found failing inputs for ${wcount} error(s)!\n`));
        for(let i = 0; i < witnesslist.length; ++i) {
            process.stdout.write(`${witnesslist[i].msg} -- ${witnesslist[i].position}\n`);    
            process.stdout.write(JSON.stringify(witnesslist[i].input, undefined, 2) + "\n");
        }
    }

    if(pcount !== 0) {
        process.stdout.write(chalk.blue(`Proved ${pcount} error(s) unreachable on a subset of excutions (and found no failing inputs)!\n`));
    }

    if(ecount !== 0) {
        process.stdout.write(chalk.blue(`Exhausted search on ${ecount} error(s) and found no failing inputs.\n`));
    }
}
else if(mode === "--evaluate") {
    const files = args;
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const vopts = {
        ISize: 8,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const jinput = JSON.parse(input) as any[];
            workflowEvaluateSingle(usercode, jinput, vopts, DEFAULT_TIMEOUT, "NSMain::main", (res: string) => {
                try {
                    const jres = JSON.parse(res);

                    if (jres["result"] === "unreachable") {
                        process.stdout.write(`No valid (non error) result exists for this input!\n`);
                    }
                    else if (jres["result"] === "output") {
                        process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                        process.stdout.write(JSON.stringify(jres["output"]) + "\n");
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
else if(mode === "--invert") {
    const files = args;
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const vopts = {
        ISize: 8,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    let rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout
    });

    rl.question(">> ", (input) => {
        try {
            const joutput = JSON.parse(input);
            workflowInvertSingle(usercode, joutput, vopts, DEFAULT_TIMEOUT, "NSMain::main", (res: string) => {
                try {
                    const jres = JSON.parse(res);

                    if (jres["result"] === "unreachable") {
                        process.stdout.write(`No valid (non error) input exists for this output!\n`);
                    }
                    else if (jres["result"] === "witness") {
                        process.stdout.write(`Generated candidate input in ${jres["time"]} millis!\n`);
                        process.stdout.write(JSON.stringify(jres["input"]) + "\n");
                    }
                    else if (jres["result"] === "timeout") {
                        process.stdout.write(`Solver timeout :(\n`);
                    }
                    else {
                        process.stdout.write(`Failed with -- ${jres}`);
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
    const files = args;
    const usercode = workflowLoadUserSrc(files);
    if(usercode === undefined) {
        process.stdout.write("Could not load code files\n");
        process.exit(1);
    }

    const error_vopts = {
        ISize: 64,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: false,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: false,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    const errors = workflowGetErrors(usercode, error_vopts, "NSMain::main");
    if(errors === undefined) {
        process.stderr.write("Failed to load error lines\n");
        process.exit(1);
    }

    process.stdout.write("Possible Errors:\n");
    process.stdout.write(JSON.stringify(errors, undefined, 2) + "\n");
}
