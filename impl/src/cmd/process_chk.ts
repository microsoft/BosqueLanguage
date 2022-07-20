//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";

import * as chalk from "chalk";

import { extractConfig, extractFiles, extractOutput, extractTestFlags, help, loadUserSrc, tryLoadPackage } from "./args_load";
import { ConfigAppTest, ConfigFuzz, ConfigTest, Package, parseURIPathGlob } from "./package_load";
import { runtests } from "../test/runner/suite_runner";

function processTestAction(args: string[]) {
    if(args.length === 0) {
        args.push("./package.json");
    }

    if(path.extname(args[0]) === ".bsqtest") {
        const entryfile = args[0];

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("test");
            process.exit(1);
        }

        const flavors = extractTestFlags(args, "test");
        if(flavors === undefined) {
            process.stderr.write(chalk.red("Could not parse test 'flavors' option\n"));

            help("test");
            process.exit(1);
        }

        const entryglob = parseURIPathGlob(path.resolve(process.cwd(), entryfile));
        if(entryglob === undefined) {
            process.stderr.write(chalk.red("Could not parse 'bsqtest' file\n"));

            help("run");
            process.exit(1);
        }

        let smallmodel = args.includes("--small-model-only");

        const srcfiles = loadUserSrc(process.cwd(), [entryglob, ...files]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const userpackage = [{macros: [] as string[], files: srcfiles}];

        //bosque test testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]

        runtests(userpackage, [], [path.resolve(process.cwd(), entryfile)], "test", smallmodel, true, {}, "extra", flavors, ["*"]);
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

            help("test");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigTest>(args, pckg, workingdir, "test");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("test");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(workingdir, [...pckg.src.testfiles, ...pckg.src.bsqsource]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        let smallmodel = args.includes("--small-model-only");

        const userpackage = [{macros: [...cfg.macros, ...cfg.globalmacros], files: srcfiles}];

        let dirs: string[] = ["*"];
        if(Array.isArray(cfg.params.dirs)) {
            dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
        }

        //bosque test [package_path.json] [--config cname]

        runtests(userpackage, [], pckg.src.testfiles.map((tf) => path.resolve(workingdir, tf.path)), cfg.buildlevel, smallmodel, true, {}, "extra", cfg.params.flavors, dirs);
    }
}

function processAppTestAction(args: string[]) {
    if(args.length === 0) {
        args.push("./package.json");
    }
    
    if(path.extname(args[0]) === ".bsqapi") {
        const entryfile = args[0];

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("apptest");
            process.exit(1);
        }

        const flavors = extractTestFlags(args, "apptest");
        if(flavors === undefined) {
            process.stderr.write(chalk.red("Could not parse test 'flavors' option\n"));

            help("apptest");
            process.exit(1);
        }

        const entryglob = parseURIPathGlob(path.resolve(process.cwd(), entryfile));
        if(entryglob === undefined) {
            process.stderr.write(chalk.red("Could not parse 'bsqapi' file\n"));

            help("run");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(process.cwd(), [entryglob, ...files]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        let smallmodel = args.includes("--small-model-only");

        const userpackage = [{macros: [] as string[], files: srcfiles}];

        //bosque apptest testfile.bsqapi ... --files ... [--flavors (sym | icpp | err | chk)*]

        runtests(userpackage, [], [path.resolve(process.cwd(), entryfile)], "test", true, smallmodel, {}, "extra", flavors, ["*"]);
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

            help("apptest");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigAppTest>(args, pckg, workingdir, "apptest");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("apptest");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        let smallmodel = args.includes("--small-model-only");

        const userpackage = [{macros: [...cfg.macros, ...cfg.globalmacros], files: srcfiles}];

        let dirs: string[] = ["*"];
        if(Array.isArray(cfg.params.dirs)) {
            dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
        }

        //bosque apptest [package_path.json] [--config cname]

        runtests(userpackage, [], pckg.src.entrypoints.map((ef) => path.resolve(workingdir, ef.path)), cfg.buildlevel, true, smallmodel, {}, "extra", cfg.params.flavors, dirs);
    }
}

function processFuzzAction(args: string[]) {
    if(path.extname(args[0]) === ".bsqapi") {
        const entryfile = args[0];

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("fuzz");
            process.exit(1);
        }

        const entryglob = parseURIPathGlob(path.resolve(process.cwd(), entryfile));
        if(entryglob === undefined) {
            process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

            help("run");
            process.exit(1);
        }

        //bosque fuzz testfile.bsqapi ... --files ...

        process.stderr.write(chalk.red("Fuzz running is not supported yet.\n"));
        process.exit(1);
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

            help("fuzz");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigFuzz>(args, pckg, workingdir, "fuzz");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("fuzz");
            process.exit(1);
        }

        //bosque fuzz [package_path.json] [--config cname]

        process.stderr.write(chalk.red("Fuzz running is not supported yet.\n"));
        process.exit(1);
    }
}

function processMorphirCheckAction(args: string[]) {
    let workingdir = process.cwd();
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
    }

    const output = extractOutput(workingdir, args);
    if (output === undefined) {
        process.stderr.write(chalk.red("Could not parse 'output' option\n"));

        help("morphir-chk");
        process.exit(1);
    }

    const srcfile = path.join(workingdir, "morphir-ir.json");
    const dstdir = path.join(path.parse(srcfile).dir, "bsqproj");
    const dstpckg = path.join(dstdir, "package.json");

    process.stdout.write(`Running Bosque checker...\n`);
    processAppTestAction([dstpckg]);
}

export {
    processTestAction, processAppTestAction, processFuzzAction, processMorphirCheckAction
};
