//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Config, ConfigAppTest, ConfigBuild, ConfigFuzz, ConfigRun, ConfigTest, Package, parsePackage, SourceInfo } from "./package_load";

import * as fs from "fs";
import chalk from "chalk";

type CmdTag = "run" | "build" | "test" | "apptest" | "fuzz";

const RUN_CONFIG_DEFAULT: ConfigRun = {
    args: undefined,
    main: "Main::main"
};

const BUILD_CONFIG_DEFAULT: ConfigBuild = {

};

const TEST_CONFIG_DEFAULT: ConfigTest = {

};

const APPTEST_CONFIG_DEFAULT: ConfigAppTest = {

};

const FUZZ_CONFIG_DEFAULT: ConfigFuzz = {
    dirs: "*"
};

function help(cmd: CmdTag | undefined) {
    if(cmd === "run" || cmd === undefined) {
        /*
        * bosque run [package_path.json] [--entrypoint fname] [--config cname]
        * bosque run entryfile.bsqapp [--entrypoint fname] --files ...
        * bosque run [package_path.json] [--config cname] [--entrypoint fname] --args "[...]"
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

function loadPackage(pckgpath: string): Package | undefined {
    if(!pckgpath.endsWith(".json")) {
        return undefined; //use the default package
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

function extractConfig<T>(args: string[], cmd: CmdTag): Config<T> {

}

function extractSrc<T>(args: string[], cfg: Config<T>): SourceInfo {
    
}

function extractTestFlags(args: string[]): { category: Category[], dirs: string[] } {

}