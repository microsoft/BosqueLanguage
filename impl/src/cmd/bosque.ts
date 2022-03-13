//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Config, ConfigAppTest, ConfigBuild, ConfigFuzz, ConfigRun, ConfigTest, Package, parsePackage, parseURIPath, SourceInfo, URIPath } from "./package_load";

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

function generateAppTestConfigDefault(): ConfigTest {
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
        /*
        * bosque run [package_path.json] [--entrypoint fname] [--config cname]
        * bosque run entryfile.bsqapp [--entrypoint fname] --files ...
        * bosque run [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
        * bosque run entryfile.bsqapp [--entrypoint fname] --files ... --args "[...]"
        */
        xxxx;
    }

    if(cmd === "build" || cmd === undefined) {
        /*
        * bosque build node package_path.json [--config cname] [out]
        */
        xxxx;
    }

    if(cmd === "test" || cmd === undefined) {
        /*
        * bosque test [package_path.json] [--config cname] [--flavors ("sym" | "icpp" | "err" | "chk")] [--dirs ...]
        * bosque test testfile.bsqtest --files ... [--flavors ("sym" | "icpp" | "err" | "chk")]
        */
        xxxx;
    }

    if(cmd === "apptest" || cmd === undefined) {
        /*
        * bosque apptest [package_path.json] [--config cname] [--flavors ("sym" | "icpp" | "err" | "chk")] [--dirs ...]
        * bosque apptest testfile.bsqtest --files ... [--flavors ("sym" | "icpp" | "err" | "chk")]
        */
        xxxx;
    }

    if(cmd === "fuzz" || cmd === undefined) {
        /*
        * bosque fuzz package_path.json [--config cname]
        * bosque fuzz package_path.json --files ...
        */
        xxxx;
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
    if(epidx === -1 || epidx === args.length) {
        return undefined;
    }

    return args[epidx] + 1;
}

function extractArgs(args: string[]): any[] | undefined {
    const argsidx = args.indexOf("--args");
    if(argsidx === -1 || argsidx === args.length) {
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

function extractConfig<T>(args: string[], cmd: CmdTag): Config<T> {

}

function extractSrc<T>(args: string[], cfg: Config<T>): SourceInfo {
    
}

function extractTestFlags(args: string[]): { category: Category[], dirs: string[] } {

}

function processRunAction(args: string) {
    if(path.extname(args[0]) === "json") {
        const pckg = tryLoadPackage(args[0]);
        if(pckg === undefined) {
            help("run");
            process.exit(1);
        }

        // bosque run [package_path.json] [--entrypoint fname] [--config cname]

        // bosque run [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
    }
    else if(path.extname(args[0]) === "bsqapp") {
        // bosque run entryfile.bsqapp [--entrypoint fname] --files ...

        // bosque run entryfile.bsqapp [--entrypoint fname] --files ... --args "[...]"
    }
    else {
        help("run");
        process.exit(1);
    }
}