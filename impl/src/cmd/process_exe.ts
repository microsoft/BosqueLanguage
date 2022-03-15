//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";
import * as readline from "readline";

import chalk from "chalk";

import { help, extractEntryPointKnownFile, isStdInArgs, extractFiles, extractArgs, loadUserSrc, tryLoadPackage, extractEntryPoint, extractConfig, extractOutput } from "./args_load";
import { ConfigBuild, ConfigRun, Package, parseURIPathGlob } from "./package_load";
import { PackageConfig } from "../compiler/mir_assembly";
import { workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";

function processRunAction(args: string[]) {
    if(path.extname(args[0]) === "bsqapp") {
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

        const userpackage = new PackageConfig([], srcfiles);

        if(fargs === undefined) {
            // bosque run [package_path.json] [--entrypoint fname] [--config cname]
            
            let rl = readline.createInterface({
                input: process.stdin,
                output: process.stdout
            });

            rl.question(">> ", (input) => {
                try {
                    const jargs = JSON.parse(input);
        
                    process.stdout.write(`Evaluating...\n`);
        
                    workflowRunICPPFile(jargs, userpackage, "release", false, {}, entrypoint, (result: string | undefined) => {
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
            // bosque run [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
            workflowRunICPPFile(fargs, userpackage, "release", false, {}, entrypoint, (result: string | undefined) => {
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
        if(path.extname(args[0]) === "json") {
            workingdir = path.dirname(path.normalize(args[0]));
            pckg = tryLoadPackage(args[0]);
        }
        else {
            const implicitpckg = path.join(workingdir, "package.json");
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

        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], srcfiles);

        if(fargs === undefined) {
            // bosque run [package_path.json] [--entrypoint fname] [--config cname]
            
            let rl = readline.createInterface({
                input: process.stdin,
                output: process.stdout
            });

            rl.question(">> ", (input) => {
                try {
                    const jargs = JSON.parse(input);
        
                    process.stdout.write(`Evaluating...\n`);
        
                    workflowRunICPPFile(jargs, userpackage, cfg.buildlevel, false, {}, entrypoint, (result: string | undefined) => {
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
            // bosque run [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
            workflowRunICPPFile(fargs, userpackage, cfg.buildlevel, false, {}, entrypoint, (result: string | undefined) => {
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

function processBuildAction(args: string[]) {
    if(args[0] === "node") {
        let workingdir = process.cwd();
        let pckg: Package | undefined = undefined;
        if(path.extname(args[0]) === "json") {
            workingdir = path.dirname(path.normalize(args[0]));
            pckg = tryLoadPackage(args[0]);
        }
        else {
            const implicitpckg = path.join(workingdir, "package.json");
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
    else {
        process.stderr.write(chalk.red(`Unknown build target '${args[0]}'\n`));

        help("build");
        process.exit(1);
    }
}

export {
    processRunAction, processBuildAction
};
