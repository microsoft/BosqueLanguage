//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { Category, runtests } from "../runner/suite_runner";

const testroot = Path.normalize(Path.join(__dirname, "tests"));

const testfiles = FS.readdirSync(testroot)
    .filter((ff) => ff.endsWith(".bsqtest"))
    .map((ff) => Path.join(testroot, ff));

//TODO: maybe we want to also read recursive in directories as well to make grouping some tests easier later (like collections)

const pckg = {macros: [] as string[], files: testfiles};

let opts: Category[] = [];
let dirs: string[] = [];
let aargs = process.argv.slice(2);

let i = 0;
while(i < aargs.length) {
    if(aargs[i] === "--path") {
        ++i;
        break;
    }

    const rr = aargs[i];
    if(rr === "sym" || rr === "icpp" || rr === "err" || rr === "chk" || rr === "symexec") {
        opts.push(rr);
    }

    ++i;
}

while(i < aargs.length) {
    dirs.push(aargs[i]);
    ++i;
}

if(opts.length === 0) {
    opts = ["sym", "icpp", "err", "chk", "symexec"];
}

if(dirs.length === 0) {
    dirs = ["*"];
}

runtests([pckg], [], testfiles, "debug", true, {}, "extra", ["sym", "icpp", "err", "chk", "symexec"], dirs);

