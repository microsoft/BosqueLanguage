//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";
import * as readline from "readline";

import chalk from "chalk";
const fsextra = require("fs-extra");

import { help, extractEntryPointKnownFile, isStdInArgs, extractFiles, extractArgs, loadUserSrc, tryLoadPackage, extractEntryPoint, extractConfig, extractOutput } from "./args_load";
import { ConfigBuild, ConfigRun, Package, parseURIPathGlob } from "./package_load";
import { PackageConfig, SymbolicActionMode } from "../compiler/mir_assembly";
import { workflowEmitICPPFile, workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";
import { generateStandardVOpts, workflowEmitToFile, workflowEvaluate } from "../tooling/checker/smt_workflows";

function processRunAction(args: string[]) {
    if(args.length === 0) {
        args.push("./package.json");
    }

    if(path.extname(args[0]) === ".bsqapi") {
        const entryfile = args[0];

        const entrypoint = extractEntryPointKnownFile(args, process.cwd(), entryfile);
        if(entrypoint === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("run");
            process.exit(1);
        }

        let fargs: any[] | undefined = undefined;
        if (!isStdInArgs(args)) {
            fargs = extractArgs(args);
            if (fargs === undefined) {
                process.stderr.write(chalk.red("Could not parse 'arguments' option\n"));

                help("run");
                process.exit(1);
            }
        }

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("run");
            process.exit(1);
        }

        const entryglob = parseURIPathGlob(path.resolve(process.cwd(), entryfile));
        if(entryglob === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("run");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(process.cwd(), [entryglob, ...files]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const usersrcinfo = srcfiles.map((sf) => {
            return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
         });
        const userpackage = new PackageConfig([], usersrcinfo);

        if(fargs === undefined) {
            // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname]
            
            let rl = readline.createInterface({
                input: process.stdin,
                output: process.stdout
            });

            rl.question(">> ", (input) => {
                try {
                    const jargs = JSON.parse(input);
        
                    process.stdout.write(`Evaluating...\n`);
        
                    workflowRunICPPFile(jargs, userpackage, args[0] === "debug", "release", false, args[0] === "debug", {}, entrypoint, (result: string | undefined) => {
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
        else {
            // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
            workflowRunICPPFile(fargs, userpackage, args[0] === "debug", "release", false, args[0] === "debug", {}, entrypoint, (result: string | undefined) => {
                if (result !== undefined) {
                    process.stdout.write(`${result}\n`);
                }
                else {
                    process.stdout.write(`failure\n`);
                }

                process.exit(0);
            });
        }
    }
    else {
        let workingdir = process.cwd();
        let pckg: Package | undefined = undefined;
        if(path.extname(args[0]) === ".json") {
            workingdir = path.dirname(path.resolve(args[0]));
            pckg = tryLoadPackage(path.resolve(args[0]));
        }
        else {
            const implicitpckg = path.resolve(workingdir, "package.json");
            if(fs.existsSync(implicitpckg)) {
                pckg = tryLoadPackage(implicitpckg);
            }
        }
        
        if(pckg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'package' option\n"));

            help("run");
            process.exit(1);
        }

        const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
        if(entrypoint === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("run");
            process.exit(1);
        }

        let fargs: any[] | undefined = undefined;
        if (!isStdInArgs(args)) {
            fargs = extractArgs(args);
            if (fargs === undefined) {
                process.stderr.write(chalk.red("Could not parse 'arguments' option\n"));

                help("run");
                process.exit(1);
            }
        }

        const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "run");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("run");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const usersrcinfo = srcfiles.map((sf) => {
           return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
        });
        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);
        
        if(fargs === undefined) {
            // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname]
            
            let rl = readline.createInterface({
                input: process.stdin,
                output: process.stdout
            });

            rl.question(">> ", (input) => {
                try {
                    const jargs = JSON.parse(input);
        
                    process.stdout.write(`Evaluating...\n`);
        
                    workflowRunICPPFile(jargs, userpackage, args[0] === "debug", cfg.buildlevel, false, args[0] === "debug", {}, entrypoint, (result: string | undefined) => {
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
        else {
            // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
            workflowRunICPPFile(fargs, userpackage, args[0] === "debug", cfg.buildlevel, false, args[0] === "debug", {}, entrypoint, (result: string | undefined) => {
                if (result !== undefined) {
                    process.stdout.write(`${result}\n`);
                }
                else {
                    process.stdout.write(`failure\n`);
                }

                process.exit(0);
            });
        }
    }
}

function processRunSymbolicAction(args: string[]) {
    const timeout = 10000;
    const eval_opts = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);

    if(args.length === 0) {
        args.push("./package.json");
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("symrun");
        process.exit(1);
    }

    const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
    if (entrypoint === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("symrun");
        process.exit(1);
    }

    let fargs: any[] | undefined = undefined;
    if (!isStdInArgs(args)) {
        fargs = extractArgs(args);
        if (fargs === undefined) {
            process.stderr.write(chalk.red("Could not parse 'arguments' option\n"));

            help("symrun");
            process.exit(1);
        }
    }

    const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "run");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("symrun");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    if(fargs === undefined) {
        // bosque runsym [package_path.json] [--entrypoint fname] [--config cname]
        
        let rl = readline.createInterface({
            input: process.stdin,
            output: process.stdout
        });

        rl.question(">> ", (input) => {
            try {
                const jinput = JSON.parse(input) as any[];
                workflowEvaluate(userpackage, "debug", false, timeout, eval_opts, entrypoint, jinput, (res: string) => {
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
        // bosque runsym [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
        workflowEvaluate(userpackage, "debug", false, timeout, eval_opts, entrypoint, fargs, (res: string) => {
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
}

function processBuildAction(args: string[]) {
    if(args.length === 1) {
        args.push("./package.json");
    }

    if(args[0] === "node") {
        let workingdir = process.cwd();
        let pckg: Package | undefined = undefined;
        if(path.extname(args[1]) === ".json") {
            workingdir = path.dirname(path.resolve(args[1]));
            pckg = tryLoadPackage(path.resolve(args[1]));
        }
        else {
            const implicitpckg = path.resolve(workingdir, "package.json");
            if(fs.existsSync(implicitpckg)) {
                pckg = tryLoadPackage(implicitpckg);
            }
        }
        
        if(pckg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'package' option\n"));

            help("build");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("build");
            process.exit(1);
        }

        const output = extractOutput(workingdir, args);
        if(output === undefined) {
            process.stderr.write(chalk.red("Could not parse 'output' option\n"));

            help("build");
            process.exit(1);
        }

        //bosque build node [package_path.json] [--config cname] [--output out]
        process.stderr.write(chalk.red("Transpile to NPM module not implemented yet.\n"));
        process.exit(1);
    }
    else if(args[0] === "sym") {
        const timeout = 10000;
        const noerr = {file: "[No Error Trgt]", line: -1, pos: -1};

        let smtonly = args.includes("--smtlib");
        let vopts = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);

        if(args[1] === "chk") {
            vopts = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);
        }
        else if(args[1] === "eval") {
            vopts = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);
        }
        else {
            process.stderr.write(chalk.red("Could not parse symbolic build mode\n"));

            help("build");
            process.exit(1);
        }

        let workingdir = process.cwd();
        let pckg: Package | undefined = undefined;
        if(path.extname(args[1]) === ".json") {
            workingdir = path.dirname(path.resolve(args[1]));
            pckg = tryLoadPackage(path.resolve(args[1]));
        }
        else {
            const implicitpckg = path.resolve(workingdir, "package.json");
            if(fs.existsSync(implicitpckg)) {
                pckg = tryLoadPackage(implicitpckg);
            }
        }
        
        if(pckg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'package' option\n"));

            help("build");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("build");
            process.exit(1);
        }

        const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
        if (entrypoint === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("build");
            process.exit(1);
        }

        const output = extractOutput(workingdir, args);
        if(output === undefined) {
            process.stderr.write(chalk.red("Could not parse 'output' option\n"));

            help("build");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
        if (srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const usersrcinfo = srcfiles.map((sf) => {
            return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
        });
        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

        try {
            fsextra.ensureDirSync(output.path);
        }
        catch(ex) {
            process.stderr.write(chalk.red("Could not create 'output' directory\n"));

            help("build");
            process.exit(1);
        }

        //bosque build smt [err|chk|eval] [package_path.json] [--config cname] [--output out]
        if(smtonly) {
            workflowEmitToFile(path.join(output.path, cfg.name + ".smt2"), userpackage, cfg.buildlevel, false, timeout, vopts, entrypoint, noerr, true);
        }
        else {
            workflowEmitToFile(path.join(output.path, cfg.name + ".json"), userpackage, cfg.buildlevel, false, timeout, vopts, entrypoint, noerr, false);
        }
    }
    else if(args[0] === "bytecode") {
        let workingdir = process.cwd();
        let pckg: Package | undefined = undefined;
        if(path.extname(args[1]) === ".json") {
            workingdir = path.dirname(path.resolve(args[1]));
            pckg = tryLoadPackage(path.resolve(args[1]));
        }
        else {
            const implicitpckg = path.resolve(workingdir, "package.json");
            if(fs.existsSync(implicitpckg)) {
                pckg = tryLoadPackage(implicitpckg);
            }
        }
        
        if(pckg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'package' option\n"));

            help("build");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("build");
            process.exit(1);
        }

        const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
        if (entrypoint === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("build");
            process.exit(1);
        }
        const rrep = {filename: entrypoint.filename, names: [entrypoint.name], fkeys: [entrypoint.fkey]};

        const output = extractOutput(workingdir, args);
        if(output === undefined) {
            process.stderr.write(chalk.red("Could not parse 'output' option\n"));

            help("build");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
        if (srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const usersrcinfo = srcfiles.map((sf) => {
            return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
        });
        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

        try {
            fsextra.ensureDirSync(output.path);
        }
        catch(ex) {
            process.stderr.write(chalk.red("Could not create 'output' directory\n"));

            help("build");
            process.exit(1);
        }

        //bosque build bytecode [package_path.json] [--config cname] [--output out]
        workflowEmitICPPFile(path.join(output.path, cfg.name + ".json"), userpackage, false, cfg.buildlevel, false, {}, rrep);
    }
    else {
        process.stderr.write(chalk.red(`Unknown build target '${args[0]}'\n`));

        help("build");
        process.exit(1);
    }
}

export {
    processRunAction, processRunSymbolicAction, processBuildAction
};
