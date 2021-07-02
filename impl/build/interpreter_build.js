//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fsx = require("fs-extra");
const path = require("path");
const proc = require('child_process');

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/icpp/interpreter"));
const cppfiles = [rootsrc, path.join(rootsrc, "assembly"), path.join(rootsrc, "core"), path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");

const outbase = path.normalize(path.join(__dirname, "output"));

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let taillinks = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    ccflags = "-O1 -g -DBSQ_DEBUG_BUILD -Wall -Wno-reorder-ctor -std=c++17 -arch x86_64";
    includes = " -I /usr/local/boost_1_76_0";
    outfile = "-o " + outbase + "/icpp";
}
else if(process.platform === "linux") {
    compiler = "clang++";
    ccflags = "-O1 -g -DBSQ_DEBUG_BUILD -Wall -Wno-reorder-ctor -std=c++17";
    includes = " -I /usr/local/boost_1_76_0";
    outfile = "-o " + outbase + "/icpp";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /Zi /D \"BSQ_DEBUG_BUILD\" /std:c++17";  
    includes = " /I \"C:\\Program Files\\boost_1_76_0\"";
    taillinks = " /link /LIBPATH:\"C:\\Program Files\\boost_1_76_0\\stage\\lib\"";
    outfile = "/Fo:\"" + outbase + "/\"" + " " + "/Fd:\"" + outbase + "/\"" + " " + "/Fe:\"" + outbase + "\\icpp.exe\"";
}

const command = `${compiler} ${ccflags}${includes} ${outfile} ${cppfiles.join(" ")}${taillinks}`;

fsx.ensureDirSync(outbase);
fsx.emptyDirSync(outbase);

console.log(command);

const outstr = proc.execSync(command).toString();
console.log(`${outstr}`);
