//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const chalk = require('chalk');

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/icpp/interpreter"));
const apisrc = path.normalize(path.join(__dirname, "../", "src/tooling/api_parse"));
const cppfiles = [apisrc, rootsrc, path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");

const includebase = path.normalize(path.join(__dirname, "include"));
const includeheaders = [path.join(includebase, "headers/json"), path.join(includebase, "headers/mimalloc")];
const outbase = path.normalize(path.join(__dirname, "output"));

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let milib = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    ccflags = "-O0 -g -DBSQ_DEBUG_BUILD -Wall -std=c++20 -arch arm64";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    milib = path.join(includebase, "/macos/mimalloc/bin/libmimalloc.a");
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
    ccflags = "/EHsc /Zi /MD /D \"BSQ_DEBUG_BUILD\" /std:c++20";  
    includes = includeheaders.map((ih) => `/I ${ih}`).join(" ");
    milib = path.join(includebase, "/win/mimalloc/bin/mimalloc-static.lib");
    outfile = "/Fo:\"" + outbase + "/\"" + " " + "/Fd:\"" + outbase + "/\"" + " " + "/Fe:\"" + outbase + "\\icpp.exe\"";
}

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")} ${milib} advapi32.lib`;

fsx.ensureDirSync(outbase);
fsx.removeSync(outfile);

console.log(command);


try {
    const outstr = proc.execSync(command).toString();
    console.log(`${outstr}`);
}
catch (ex) {
    console.log(chalk.red(ex.toString()));
    process.exit(1);
}
