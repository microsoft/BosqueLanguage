//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Config, SourceInfo } from "./package_load";

function help(cmd: "run" | "build" | "test" | "apptest" | "fuzz" | undefined) {
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
        */
        xxxx;
    }
}

function extractConfig(args: string[]): Config {

}

function extractSrc(args: string[], cfg: Config): SourceInfo {
    
}

function extractTestFlags(args: string[]): { category: Category[], dirs: string[] } {

}