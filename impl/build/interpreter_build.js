//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/icpp/interpreter"));
const cppfiles = [rootsrc, path.join(rootsrc, "assembly"), path.join(rootsrc, "core"), path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");


const includebase = path.normalize(path.join(__dirname, "include"));
const includeheaders = [path.join(includebase, "headers/json")];
const outbase = path.normalize(path.join(__dirname, "output"));

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let milib = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    ccflags = "-O0 -g -DBSQ_DEBUG_BUILD -Wall -std=c++20 -arch x86_64";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    milib = path.join(includebase, "/macos/mimalloc/bin/mimalloc-static.a");
    outfile = "-o " + outbase + "/icpp";
}
else if(process.platform === "linux") {
    compiler = "clang++";
    ccflags = "-O0 -g -DBSQ_DEBUG_BUILD -Wall -std=c++20";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    milib = path.join(includebase, "/linux/mimalloc/bin/libmimalloc.a");
    outfile = "-o " + outbase + "/icpp";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /Zi /D \"BSQ_DEBUG_BUILD\" /std:c++17";  
    includes = includeheaders.map((ih) => `/I ${ih}`).join(" ");
    milib = path.join(includebase, "/win/mimalloc/bin/libmimalloc.a");
    outfile = "/Fo:\"" + outbase + "/\"" + " " + "/Fd:\"" + outbase + "/\"" + " " + "/Fe:\"" + outbase + "\\icpp.exe\"";
}

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")} ${milib}`;

fsx.ensureDirSync(outbase);
fsx.removeSync(outfile);

console.log(command);

const outstr = proc.execSync(command).toString();
console.log(`${outstr}`);
