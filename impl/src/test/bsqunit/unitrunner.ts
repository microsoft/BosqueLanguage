//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { Category, runtests } from "../runner/suite_runner";
import { SMT_SMALL_MODEL_ONLY_DEFAULT } from "../runner/test_decls";

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

const testroot = Path.join(__dirname, "tests");
const testcorelibroot = Path.join(testroot, "corelib");
const testlistroot = Path.join(testcorelibroot, "list");
const testmaproot = Path.join(testcorelibroot, "map");

const testfiles: string[] = [];
[testroot, testcorelibroot, testlistroot, testmaproot].forEach((tdir) => {
    const tfiles = FS.readdirSync(tdir)
        .filter((ff) => ff.endsWith(".bsqtest"))
        .map((ff) => Path.join(tdir, ff));

    testfiles.push(...tfiles);
});

const pckg = {macros: [] as string[], files: testfiles};

runtests([pckg], [], testfiles, "debug", SMT_SMALL_MODEL_ONLY_DEFAULT, true, {}, "extra", ["sym", "icpp", "err", "chk", "symexec"], dirs);

