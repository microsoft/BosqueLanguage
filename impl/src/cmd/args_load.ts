//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";

import chalk from "chalk";

import { Config, ConfigAppTest, ConfigBuild, ConfigFuzz, ConfigRun, ConfigTest, Package, parsePackage, parseURIPath, parseURIPathGlob, URIPath, URIPathGlob } from "./package_load";

type CmdTag = "run" | "symrun" | "build" | "test" | "apptest" | "fuzz";

function help(cmd: CmdTag | undefined) {
    if(cmd === "run" || cmd === undefined) {
        process.stdout.write("Run Application:\n");
        process.stdout.write("bosque run [package_path.json] [--entrypoint fname] [--config cname]\n");
        process.stdout.write("bosque run [package_path.json] [--entrypoint fname] [--config cname] --args \"[...]\"\n");
        process.stdout.write("bosque run entryfile.bsqapi [--entrypoint fname] --files ...\n");
        process.stdout.write("bosque run entryfile.bsqapi [--entrypoint fname] --files ... --args \"[...]\"\n\n");
    }

    if(cmd === "symrun" || cmd === undefined) {
        process.stdout.write("Symbolic Run Application:\n");
        process.stdout.write("bosque symrun [package_path.json] [--entrypoint fname] [--config cname]\n");
        process.stdout.write("bosque symrun [package_path.json] [--entrypoint fname] [--config cname] --args \"[...]\"\n\n");
    }

    if(cmd === "build" || cmd === undefined) {
        process.stdout.write("Build Application:\n");
        process.stdout.write("bosque build node [package_path.json] [--config cname] [out]\n");
        process.stdout.write("bosque build bytecode [package_path.json] [--entrypoint fname] [--config cname] [out]\n");
        process.stdout.write("bosque build sym chk|eval --smtlib [package_path.json] [--entrypoint fname] [--config cname] [out]\n\n");
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
        process.stdout.write("bosque fuzz testfile.bsqapi ... --files ...\n\n");
    }
}

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

function tryLoadPackage(pckgpath: string): Package | undefined {
    if(path.extname(pckgpath) !== ".json") {
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
    const okfname = contents.includes(`entrypoint function ${fname}(`);

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
        name: epname.slice(ccidx + 2),
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

        epname = args[epidx + 1];
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
                            name: epname.slice(ccidx + 2),
                            fkey: "__i__" + epname
                        };
                    }
                }
                else if(appfiles[i].selection === "*") {
                    const subfiles = fs.readdirSync(fullpath);
                
                    for(let j = 0; j < subfiles.length; ++j) {
                        const fullsubpath = path.resolve(fullpath, subfiles[j]);
                        const fext = path.extname(fullsubpath);

                        if ((fext === appfiles[i].filter || appfiles[i].filter === undefined) && fext === ".bsqapi") {
                            const contents = fs.readFileSync(fullsubpath).toString();
                            if (checkEntrypointMatch(contents, ns, fname)) {
                                return {
                                    filename: fullsubpath,
                                    name: epname.slice(ccidx + 2),
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
        rargs = JSON.parse(args[argsidx + 1]);
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
        if(path.extname(args[ii]) !== ".bsq") {
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

function loadUserSrc(workingdir: string, files: URIPathGlob[]): string[] | undefined {
    try {
        let code: string[] = [];

        for (let i = 0; i < files.length; ++i) {
            if(files[i].scheme === "file") {
                const fullpath = path.resolve(workingdir, files[i].path);
                if(files[i].selection === undefined) {
                    code.push(fullpath);
                }
                else if(files[i].selection === "*") {
                    const subfiles = fs.readdirSync(fullpath);
                
                    for(let j = 0; j < subfiles.length; ++j) {
                        const fullsubpath = path.resolve(fullpath, subfiles[j]);
                        const fext = path.extname(fullsubpath);

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === ".bsq") {
                            code.push(fullsubpath);
                        }

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === ".bsqapi") {
                            code.push(fullsubpath);
                        }

                        if((fext === files[i].filter || files[i].filter === undefined) && fext === ".bsqtest") {
                            code.push(fullsubpath);
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

export {
    CmdTag,
    help,
    tryLoadPackage, extractEntryPointKnownFile, extractEntryPoint, isStdInArgs, extractArgs, extractOutput, extractFiles, extractConfig, extractTestFlags, loadUserSrc
};
