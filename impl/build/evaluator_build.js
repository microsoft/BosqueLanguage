//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/checker/evaluator"));
const apisrc = path.normalize(path.join(__dirname, "../", "src/tooling/api_parse"));
const cppfiles = [rootsrc, apisrc].map((pp) => pp + "/*.cpp");

const includebase = path.normalize(path.join(__dirname, "include"));
const includeheaders = [path.join(includebase, "headers/json"), path.join(includebase, "headers/z3")];
const outbase = path.normalize(path.join(__dirname, "output"));

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let z3lib = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    ccflags = "-O0 -g -Wall -std=c++20 -arch x86_64";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/macos/z3/bin/libz3.a")
    outfile = "-o " + outbase + "/chk";
}
else if(process.platform === "linux") {
    compiler = "clang++";
    ccflags = "-O0 -g -Wall -std=c++20 -pthread";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/linux/z3/bin/libz3.a")
    outfile = "-o " + outbase + "/chk";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /Zi /std:c++20";  
    includes = includeheaders.map((ih) => `/I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/win/z3/bin/libz3.lib")
    outfile = "/Fo:\"" + outbase + "/\"" + " " + "/Fd:\"" + outbase + "/\"" + " " + "/Fe:\"" + outbase + "\\chk.exe\"";
}

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")} ${z3lib}`;

fsx.ensureDirSync(outbase);
fsx.removeSync(outfile);

console.log(command);

try {
    const outstr = proc.execSync(command).toString();
    console.log(`${outstr}`);

    if(process.platform === "win32") {
        fsx.copyFileSync(path.join(includebase, "win/z3/bin/libz3.dll"), path.join(outbase, "libz3.dll"));
    }
}
catch (ex) {
    console.log(ex.toString());
    process.exit(1);
}
