//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Config, ConfigAppTest, ConfigBuild, ConfigFuzz, ConfigRun, ConfigTest, Package, parsePackage, parseURIPath, URIPath, parseURIPathGlob, URIPathGlob } from "./package_load";

import * as fs from "fs";
import * as path from "path";
import * as readline from "readline";

import chalk from "chalk";

import { workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";
import { PackageConfig } from "../compiler/mir_assembly";
import { CodeFileInfo } from "../ast/parser";
import { runtests } from "../test/runner/suite_runner";

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

function checkEntrypointMatch(contents: string, ns: string, fname: string): boolean {
    const okns = contents.includes(`namespace ${ns};`);
    const okfname = contents.includes(`entrypoint function ${fname};`);

    return okns && okfname;
}

function extractEntryPointKnownFile(args: string[], workingdir: string, appfile: string): {filename: string, name: string, fkey: string} | undefined {
    const epidx = args.indexOf("--entrypoint");

    let epname = "Main::main";
    if(epidx !== -1) {
        if(epidx === args.length - 1) {
            return undefined;
        }

        epname = args[epidx] + 1;
    }

    const ccidx = epname.indexOf("::");
    if(ccidx === -1) {
        return undefined;
    }

    return {
        filename: path.resolve(workingdir, appfile),
        name: epname,
        fkey: "__i__" + epname
    }
}

function extractEntryPoint(args: string[], workingdir: string, appfiles: URIPathGlob[]): {filename: string, name: string, fkey: string} | undefined {
    const epidx = args.indexOf("--entrypoint");

    let epname = "Main::main";
    if(epidx !== -1) {
        if(epidx === args.length - 1) {
            return undefined;
        }

        epname = args[epidx] + 1;
    }

    const ccidx = epname.indexOf("::");
    if(ccidx === -1) {
        return undefined;
    }

    const ns = epname.slice(0, ccidx);
    const fname = epname.slice(ccidx + 2);

    try {
        for (let i = 0; i < appfiles.length; ++i) {
            if(appfiles[i].scheme === "file") {
                const fullpath = path.resolve(workingdir, appfiles[i].path);

                if(appfiles[i].selection === undefined) {
                    const contents = fs.readFileSync(fullpath).toString();
                    if(checkEntrypointMatch(contents, ns, fname)) {
                        return {
                            filename: fullpath,
                            name: epname,
                            fkey: "__i__" + epname
                        };
                    }
                }
                else if(appfiles[i].selection === "*") {
                    const subfiles = fs.readdirSync(fullpath);
                
                    for(let j = 0; j < subfiles.length; ++j) {
                        const fullsubpath = path.resolve(fullpath, subfiles[j]);
                        const fext = path.extname(fullsubpath);

                        if ((fext === appfiles[i].filter || appfiles[i].filter === undefined) && fext === "bsqapp") {
                            const contents = fs.readFileSync(fullsubpath).toString();
                            if (checkEntrypointMatch(contents, ns, fname)) {
                                return {
                                    filename: fullsubpath,
                                    name: epname,
                                    fkey: "__i__" + epname
                                };
                            }
                        }
                    }
                }
                else {
                    process.stderr.write(chalk.red("** glob pattern not implemented yet!!!\n"));
                    process.exit(1);
                }
            }
            else {
                return undefined;
            }
        }

        return undefined;
    }
    catch (ex) {
        return undefined;
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

function extractFiles(workingdir: string, args: string[]): URIPathGlob[] | undefined {
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

    let urifiles: URIPathGlob[] = [];
    for(let i = 0; i < files.length; ++i) {
        const fullfd = path.join(workingdir, files[i]);
        if(!fs.existsSync(fullfd)) {
            return undefined;
        }

        const furi = parseURIPathGlob(fullfd);
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

function loadUserSrc(workingdir: string, files: URIPathGlob[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            if(files[i].scheme === "file") {
                const fullpath = path.resolve(workingdir, files[i].path);
                if(files[i].selection === undefined) {
                    code.push({ srcpath: fullpath, filename: path.basename(fullpath), contents: fs.readFileSync(fullpath).toString() });
                }
                else if(files[i].selection === "*") {
                    const subfiles = fs.readdirSync(fullpath);
                
                    for(let j = 0; j < subfiles.length; ++j) {
                        const fullsubpath = path.resolve(fullpath, subfiles[j]);
                        const fext = path.extname(fullsubpath);

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === "bsq") {
                            code.push({ srcpath: fullsubpath, filename: path.basename(fullsubpath), contents: fs.readFileSync(fullsubpath).toString() });
                        }

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === "bsqapp") {
                            code.push({ srcpath: fullsubpath, filename: path.basename(fullsubpath), contents: fs.readFileSync(fullsubpath).toString() });
                        }

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === "bsqtest") {
                            code.push({ srcpath: fullsubpath, filename: path.basename(fullsubpath), contents: fs.readFileSync(fullsubpath).toString() });
                        }
                    }
                }
                else {
                    process.stderr.write(chalk.red("** glob pattern not implemented yet!!!\n"));
                    process.exit(1);
                }
            }
            else {
                return undefined;
            }
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

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

        const entryglob = parseURIPathGlob(path.resolve(process.cwd(), entryfile));
        if(entryglob === undefined) {
            process.stderr.write(chalk.red("Could not parse 'bsqtest' file\n"));

            help("run");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(process.cwd(), [entryglob, ...files]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const userpackage = new PackageConfig([], srcfiles);

        //bosque test testfile.bsqtest ... --files ... [--flavors (sym | icpp | err | chk)*]

        runtests([userpackage], [], [path.resolve(process.cwd(), entryfile)], "test", true, {}, "extra", flavors, ["*"]);
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

        const cfg = extractConfig<ConfigTest>(args, pckg, workingdir, "build");
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

        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], srcfiles);

        let dirs: string[] = ["*"];
        if(Array.isArray(cfg.params.dirs)) {
            dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
        }

        //bosque test [package_path.json] [--config cname]

        runtests([userpackage], [], pckg.src.testfiles.map((tf) => path.resolve(workingdir, tf.path)), cfg.buildlevel, true, {}, "extra", cfg.params.flavors, dirs);
    }
}

function processAppTestAction(args: string[]) {
    if(path.extname(args[0]) === "bsqapp") {
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
            process.stderr.write(chalk.red("Could not parse 'bsqapp' file\n"));

            help("run");
            process.exit(1);
        }

        const srcfiles = loadUserSrc(process.cwd(), [entryglob, ...files]);
        if(srcfiles === undefined) {
            process.stderr.write(chalk.red("Failed when loading source files\n"));
            process.exit(1);
        }

        const userpackage = new PackageConfig([], srcfiles);

        //bosque apptest testfile.bsqapp ... --files ... [--flavors (sym | icpp | err | chk)*]

        runtests([userpackage], [], [path.resolve(process.cwd(), entryfile)], "test", true, {}, "extra", flavors, ["*"]);
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

            help("apptest");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigAppTest>(args, pckg, workingdir, "build");
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

        const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], srcfiles);

        let dirs: string[] = ["*"];
        if(Array.isArray(cfg.params.dirs)) {
            dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
        }

        //bosque apptest [package_path.json] [--config cname]

        runtests([userpackage], [], pckg.src.entrypoints.map((ef) => path.resolve(workingdir, ef.path)), cfg.buildlevel, true, {}, "extra", cfg.params.flavors, dirs);
    }
}

function processFuzzAction(args: string[]) {
    if(path.extname(args[0]) === "bsqapp") {
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

        //bosque fuzz testfile.bsqapp ... --files ...

        process.stderr.write(chalk.red("Fuzz running is not supported yet.\n"));
        process.exit(1);
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

            help("fuzz");
            process.exit(1);
        }

        const cfg = extractConfig<ConfigFuzz>(args, pckg, workingdir, "build");
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

const fullargs = process.argv;

//slice of node bosque.js or bosque prefix of command
if(fullargs.length < 2) {
    help(undefined);
    process.exit(1);
}

let cmdop: string = "unset";
let cmdargs: string[] = [];
if(fullargs[1].endsWith("bosque.js")) {
    cmdop = fullargs[2];
    cmdargs = fullargs.slice(3);
}
else {
    cmdop = fullargs[1];
    cmdargs = fullargs.slice(2);
}

if(cmdop === "run") {
    processRunAction(cmdargs);
}
else if(cmdop === "build") {
    processBuildAction(cmdargs);
}
else if(cmdop === "test") {
    processTestAction(cmdargs);
}
else if(cmdop === "apptest") {
    processAppTestAction(cmdargs);
}
else if(cmdop === "fuzz") {
    processFuzzAction(cmdargs);
}
else {
    help(undefined);
    process.exit(1);
}
