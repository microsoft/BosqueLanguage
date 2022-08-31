//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const rootsrc = path.join(__dirname, "../", "src/tooling/icpp/interpreter");
const apisrc = path.join(__dirname, "../", "src/tooling/api_parse");
const cppfiles = [apisrc, rootsrc, path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");

const includebase = path.join(__dirname, "include");
const includeheaders = [path.join(includebase, "headers/json")];
const outexec = path.join(__dirname, "output");
const outobj = path.join(__dirname, "output", "obj");

const mode = process.argv[2] || "debug";

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
if(process.platform === "darwin") {
    compiler = "g++";
    ccflags = (mode === "debug" ? "-g3" : "-O2") + " -DBSQ_DEBUG_BUILD -Wall -std=c++20";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    outfile = "-o " + outexec+ "/icpp";
}
else if(process.platform === "linux") {
    compiler = "g++";
    ccflags = (mode === "debug" ? "-g3" : "-O2") + " -DBSQ_DEBUG_BUILD -Wall -std=c++20";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    outfile = "-o " + outexec + "/icpp";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /MP " + (mode === "debug" ? "/Zi /Od" : "/O2") + " /D \"BSQ_DEBUG_BUILD\" /std:c++20";  
    includes = includeheaders.map((ih) => `/I ${ih}`).join(" ");
    outfile = "/Fo:\"" + outobj + "/\"" + " " + "/Fd:\"" + outexec + "/\"" + " " + "/Fe:\"" + outexec + "\\icpp.exe\"";
}

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")}`;

fsx.ensureDirSync(outexec);
fsx.ensureDirSync(outobj);
fsx.removeSync(outfile);

console.log(command);


try {
    const outstr = proc.execSync(command).toString();
    console.log(`${outstr}`);
}
catch (ex) {
    console.log(ex.toString());
    process.exit(1);
}
