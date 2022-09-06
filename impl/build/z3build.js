//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const path = require("path");
const proc = require('child_process');

if(process.argv.length !== 3) {
    process.stderr.write("");
    process.exit(1);
}

let z3dir = process.argv[2];
let builddir = path.join(z3dir, "build");

let runconfig = "";
if(process.platform === "darwin") {
    runconfig = "FPMATH_ENABLED=False python scripts/mk_make.py --arm64=true --staticlib";
}
else if(process.platform === "linux") {
    runconfig = "python scripts/mk_make.py --staticlib";
}
else {
    runconfig = "python scripts/mk_make.py -x";
}

try {
    process.stdout.write("Configuring...\n");
    proc.execSync(runconfig, {cwd: z3dir});
    
    process.stdout.write("Building...\n");
    if(process.platform === "darwin" || process.platform === "linux") {
        proc.execSync("make", {cwd: builddir});
    }
    else {
        proc.execSync("nmake", {cwd: builddir});
    }

    process.stdout.write("Done!\n");
}
catch (ex) {
    console.log(ex.toString());
    process.exit(1);
}
