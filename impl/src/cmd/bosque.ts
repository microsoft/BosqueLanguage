//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Config, ConfigAppTest, ConfigBuild, ConfigFuzz, ConfigRun, ConfigTest, Package, parsePackage, parseURIPath, URIPath } from "./package_load";

import * as fs from "fs";
import * as path from "path";
import chalk from "chalk";

type CmdTag = "run" | "build" | "test" | "apptest" | "fuzz";

function generateRunConfigDefault(): ConfigRun {
    return {
        args: undefined,
        main: "Main::main"
    };
}

function generateBuildConfigDefault(workingdir: string): ConfigBuild {
    return {
        out: {
            scheme: "file",
            authority: undefined,
            port: undefined,
            path: path.join(workingdir, "bin"),
            extension: undefined
        }
    };
}

function generateTestConfigDefault(): ConfigTest {
    return {
        flavors: ["sym", "icpp", "chk"],
        dirs: "*"
    };
}

function generateAppTestConfigDefault(): ConfigAppTest {
    return {
        flavors: ["sym", "icpp", "err"],
        dirs: "*"
    };
}

function generateFuzzConfigDefault(): ConfigFuzz {
    return {
        dirs: "*"
    };
}

function help(cmd: CmdTag | undefined) {
    if(cmd === "run" || cmd === undefined) {
        process.stdout.write("Run Application:\n");
        process.stdout.write("bosque run [package_path.json] [--entrypoint fname] [--config cname]\n");
        process.stdout.write("bosque run [package_path.json] [--entrypoint fname] [--config cname] --args \"[...]\"\n");
        process.stdout.write("bosque run entryfile.bsqapp [--entrypoint fname] --files ...\n");
        process.stdout.write("bosque run entryfile.bsqapp [--entrypoint fname] --files ... --args \"[...]\"\n\n");
    }

    if(cmd === "build" || cmd === undefined) {
        process.stdout.write("Build Application:\n");
        process.stdout.write("bosque build node [package_path.json] [--config cname] [out]\n\n");
    }

    if(cmd === "test" || cmd === undefined) {
        process.stdout.write("Unit-Test Application:\n");
        process.stdout.write("bosque test [package_path.json] [--config cname]\n");
        process.stdout.write("bosque test testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]\n\n");
    }

    if(cmd === "apptest" || cmd === undefined) {
        process.stdout.write("EntryPoint Test Application:\n");
        process.stdout.write("bosque apptest [package_path.json] [--config cname]\n");
        process.stdout.write("bosque apptest testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]\n\n");
    }

    if(cmd === "fuzz" || cmd === undefined) {
        process.stdout.write("Fuzz Application:\n");
        process.stdout.write("bosque fuzz [package_path.json] [--config cname]\n");
        process.stdout.write("bosque fuzz testfile.bsqapp ... --files ...\n\n");
    }
}

function tryLoadPackage(pckgpath: string): Package | undefined {
    if(path.extname(pckgpath) !== "json") {
        return undefined;
    }

    if(path.basename(pckgpath) !== "package.json") {
        process.stderr.write(chalk.red(`Invalid package file name (expected 'package.json')-- ${pckgpath}\n`));
        process.exit(1);
    }

    let contents: string = "EMPTY";
    try {
        contents = fs.readFileSync(pckgpath).toString();
    }
    catch(exl) {
        process.stderr.write(chalk.red(`Could not load package file -- ${pckgpath}\n`));
        process.exit(1);
    }

    let jpckg: any = undefined;
    try {
        jpckg = JSON.parse(contents);
    }
    catch(exj) {
        process.stderr.write(chalk.red(`Package file does not have a vaild JSON config -- ${pckgpath}\n`));
        process.exit(1);
    }

    const pckg = parsePackage(jpckg);
    if(typeof(pckg) === "string") {
        process.stderr.write(chalk.red(`Package file format error -- ${pckg}\n`));
        process.exit(1);
    }

    return pckg;
}

function extractEntryPoint(args: string[]): string | undefined {
    const epidx = args.indexOf("--entrypoint");
    if(epidx === -1) {
        return "Main::main";
    }
    else {
        if(epidx === args.length - 1) {
            return undefined;
        }

        return args[epidx] + 1;
    }
}

function isStdInArgs(args: string[]): boolean {
    return args.indexOf("--args") === -1;
}

function extractArgs(args: string[]): any[] | undefined {
    const argsidx = args.indexOf("--args");
    if(argsidx === -1 || argsidx === args.length - 1) {
        return undefined;
    }

    let rargs: any = undefined;
    try {
        rargs = JSON.parse(args[argsidx] + 1);
        if(!Array.isArray(rargs)) {
            return undefined;
        }
    }
    catch {
        ;
    }

    return rargs;
}

function extractOutput(workingdir: string, args: string[]): URIPath | undefined {
    const argsidx = args.indexOf("--output");
    if(argsidx === -1 || argsidx === args.length - 1) {
        return {
            scheme: "file",
            authority: undefined,
            port: undefined,
            path: path.join(workingdir, "bin"),
            extension: undefined
        };
    }

    return parseURIPath(args[argsidx + 1]);
}

function extractFiles(workingdir: string, args: string[]): URIPath[] | undefined {
    const fidx = args.indexOf("--files");
    if(fidx === -1) {
        return undefined;
    }

    let ii = fidx + 1;
    let files: string[] = [];
    while(ii < args.length && !args[ii].startsWith("--")) {
        if(path.extname(args[ii]) !== "bsq") {
            return undefined;
        }

        files.push(args[ii]);
    } 

    let urifiles: URIPath[] = [];
    for(let i = 0; i < files.length; ++i) {
        const fullfd = path.join(workingdir, files[i]);
        if(!fs.existsSync(fullfd)) {
            return undefined;
        }

        const furi = parseURIPath(fullfd);
        if(furi === undefined) {
            return undefined;
        }

        urifiles.push(furi);
    }

    return urifiles;
}

function extractConfig<T>(args: string[], pckg: Package, workingdir: string, cmd: CmdTag): Config<T> | undefined {
    const cfgidx = args.indexOf("--confg");
    if(cfgidx !== -1) {
        if(cfgidx === args.length - 1) {
            return undefined;
        }

        const cfgname = args[cfgidx];
        if(cmd === "run") {
            return (pckg.configs.run.find((cfg) => cfg.name === cfgname) as any) as Config<T>;
        }
        else if(cmd === "build") {
            return (pckg.configs.build.find((cfg) => cfg.name === cfgname) as any) as Config<T>;
        }
        else if(cmd === "test") {
            return (pckg.configs.test.find((cfg) => cfg.name === cfgname) as any) as Config<T>;
        }
        else if(cmd === "apptest") {
            return (pckg.configs.apptest.find((cfg) => cfg.name === cfgname) as any) as Config<T>;
        }
        else {
            return (pckg.configs.run.find((cfg) => cfg.name === cfgname) as any) as Config<T>;
        }
    }
    else {
        if(cmd === "run") {
            const rcfg = generateRunConfigDefault() as any;
            return {
                name: "_run_",
                macros: [],
                globalmacros: [],
                buildlevel: "release",
                params: rcfg as T
            };
        }
        else if(cmd === "build") {
            const rcfg = generateBuildConfigDefault(workingdir) as any;
            return {
                name: "_build_",
                macros: [],
                globalmacros: [],
                buildlevel: "release",
                params: rcfg as T
            };
        }
        else if(cmd === "test") {
            const rcfg = generateTestConfigDefault() as any;
            return {
                name: "_test_",
                macros: [],
                globalmacros: [],
                buildlevel: "test",
                params: rcfg as T
            };
        }
        else if(cmd === "apptest") {
            const rcfg = generateAppTestConfigDefault() as any;
            return {
                name: "_apptest_",
                macros: [],
                globalmacros: [],
                buildlevel: "test",
                params: rcfg as T
            };
        }
        else {
            const rcfg = generateFuzzConfigDefault() as any;
            return {
                name: "_fuzz_",
                macros: [],
                globalmacros: [],
                buildlevel: "test",
                params: rcfg as T
            };
        }
    }
}

function extractTestFlags(args: string[], cmd: CmdTag): ("sym" | "icpp" | "err" | "chk")[] | undefined {
    const fidx = args.indexOf("--flavors");
    if(fidx === -1 || fidx === args.length - 1) {
        if(cmd === "test") {
            return ["sym", "icpp", "chk"];
        }
        else {
            return ["sym", "icpp", "err"];
        }
    }

    if(fidx === args.length - 1) {
        return undefined;
    }

    let ii = fidx + 1;
    let flavors: ("sym" | "icpp" | "err" | "chk")[] = [];
    while(ii < args.length && !args[ii].startsWith("--")) {
        const flavor = args[ii];
        if(flavor !== "sym" && flavor !== "icpp" && flavor !== "err" && flavor !== "chk") {
            return undefined;
        }

        flavors.push(flavor);
    } 

    return flavors;
}

function processRunAction(args: string[]) {
    if(path.extname(args[0]) === "bsqapp") {
        const entryfile = args[0];

        const entrypoint = extractEntryPoint(args);
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

        if(fargs === undefined) {
            // bosque run entryfile.bsqapp [--entrypoint fname] --files ...
            xxx;
        }
        else {
            // bosque run entryfile.bsqapp [--entrypoint fname] --files ... --args "[...]"
            xxx;
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

        const entrypoint = extractEntryPoint(args);
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

        if(fargs === undefined) {
            // bosque run [package_path.json] [--entrypoint fname] [--config cname]
            xxx;
        }
        else {
            // bosque run [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
            xxx;
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

        const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "build");
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

        xxxx;
        //bosque build node [package_path.json] [--config cname] [--output out]
    }
    else {
        process.stderr.write(chalk.red(`Unknown build target '${args[0]}'\n`));

        help("build");
        process.exit(1);
    }
}

function processTestAction(args: string[]) {
    if(path.extname(args[0]) === "bsqtest") {
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

        //bosque test testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]
        xxxx;
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

            help("test");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("test");
            process.exit(1);
        }

        //bosque test [package_path.json] [--config cname]
        xxxx;
    }
}

function processAppTestAction(args: string[]) {
    if(path.extname(args[0]) === "bsqtest") {
        const entryfile = args[0];

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("test");
            process.exit(1);
        }

        const flavors = extractTestFlags(args, "apptest");
        if(flavors === undefined) {
            process.stderr.write(chalk.red("Could not parse test 'flavors' option\n"));

            help("test");
            process.exit(1);
        }

        //bosque test testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]
        xxxx;
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

            help("test");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("test");
            process.exit(1);
        }

        //bosque test [package_path.json] [--config cname]
        xxxx;
    }
}

function processFuzzAction(args: string[]) {
    if(path.extname(args[0]) === "bsqapp") {
        const entryfile = args[0];

        const files = extractFiles(process.cwd(), args);
        if(files === undefined) {
            process.stderr.write(chalk.red("Could not parse 'files' option\n"));

            help("test");
            process.exit(1);
        }

        //bosque fuzz testfile.bsqapp ... --files ...
        xxxx;
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

            help("test");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "build");
        if(cfg === undefined) {
            process.stderr.write(chalk.red("Could not parse 'config' option\n"));

            help("test");
            process.exit(1);
        }

        //bosque fuzz [package_path.json] [--config cname]
        xxxx;
    }
}

