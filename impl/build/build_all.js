//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const { exec } = require("child_process");
const path = require("path");

const builddir = __dirname;
const tscdir = path.dirname(__dirname);

let donecopy = false;
let donets = false;
let donesmt = false;
let doneicpp = false;

let haderror = false;

function doneop(iserror, msg) {
    haderror = haderror || iserror;

    process.stdout.write(msg + "\n");
    if(donecopy && donets && donesmt && doneicpp) {
        if(!haderror) {
            process.stdout.write("done!\n");
            process.exit(0);
        }
        else {
            process.stdout.write("error!\n");
            process.exit(1);
        }
    }
}

exec("tsc -p tsconfig.json", {cwd: tscdir}, (err, stdout, stderr) => {
    donets = true;
    doneop(err !== null, err !== null ? err : "done tsc..."); 
});

exec("node ./resource_copy.js", {cwd: builddir}, (err, stdout, stderr) => {
    donecopy = true;
    doneop(err !== null, err !== null ? stderr : "done copy..."); 
});

exec("node ./evaluator_build.js", {cwd: builddir}, (err, stdout, stderr) => {
    donesmt = true;
    doneop(err !== null, err !== null ? stdout : "done smt..."); 

    exec("node ./interpreter_build.js", {cwd: builddir}, (err, stdout, stderr) => {
        doneicpp = true;
        doneop(err !== null, err !== null ? stdout : "done icpp..."); 
    });
});
