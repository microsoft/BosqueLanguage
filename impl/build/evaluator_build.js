//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const rootsrc = path.join(__dirname, "../", "src/tooling/checker/evaluator");
const apisrc = path.join(__dirname, "../", "src/tooling/api_parse");
const cppfiles = [rootsrc, apisrc].map((pp) => pp + "/*.cpp");

const includebase = path.join(__dirname, "include");
const includeheaders = [path.join(includebase, "headers/json"), path.join(includebase, "headers/z3")];
const outexec = path.join(__dirname, "output");
const outobj = path.join(__dirname, "output", "obj");

const mode = process.argv[2] || "debug";

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let z3lib = "";
if(process.platform === "darwin") {
    compiler = "g++";
    ccflags = (mode === "debug" ? "-g" : "-O2") + " -Wall -Wextra -Wuninitialized -Wno-unused-parameter -Werror -std=c++2a -arch arm64";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/macos/z3/bin/libz3.a")
    outfile = "-o " + outexec + "/chk";
}
else if(process.platform === "linux") {
    compiler = "g++";
    ccflags = (mode === "debug" ? "-Og -g" : "-O2") + " -Wall -Wextra -Wuninitialized -Wno-unused-parameter -Werror -std=c++2a -lpthread";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/linux/z3/bin/libz3.a")
    outfile = "-o " + outexec + "/chk";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /MP " + (mode === "debug" ? "/Zi /Od" : "/O2") + " /std:c++20";  
    includes = includeheaders.map((ih) => `/I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/win/z3/bin/libz3.lib")
    outfile = "/Fo:\"" + outobj + "/\"" + " " + "/Fd:\"" + outexec + "/\"" + " " + "/Fe:\"" + outexec + "\\chk.exe\"";
}

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")} ${z3lib}`;

fsx.ensureDirSync(outexec);
fsx.ensureDirSync(outobj);
fsx.removeSync(outfile);

console.log(command);

try {
    const outstr = proc.execSync(command).toString();
    console.log(`${outstr}`);

    if(process.platform === "win32") {
        fsx.copyFileSync(path.join(includebase, "win/z3/bin/libz3.dll"), path.join(outexec, "libz3.dll"));
    }
}
catch (ex) {
    console.log(ex.toString());
    process.exit(1);
}
