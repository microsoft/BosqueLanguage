//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fs = require("fs");
const path = require("path");

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/interpreter"));
const cppfiles = [rootsrc, path.join(rootsrc, "assembly"), path.join(rootsrc, "core"), path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");

//-Wextra

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let taillinks = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    ccflags = "-g -DBSQ_DEBUG_BUILD -Wall -std=c++17";
    outfile = "-o " + __dirname + "/tools/macos/icpp";
}
else if(process.platform === "linux") {
    compiler = "clang++";
    ccflags = "-g -DBSQ_DEBUG_BUILD -Wall -std=c++17";
    outfile = "-o " + __dirname + "/tools/linux/icpp";
}
else {
    compiler = "cl.exe";
    ccflags = "/EHsc /Zi /D \"BSQ_DEBUG_BUILD\" /std:c++17";  
    includes = " /I \"C:\\Program Files\\boost_1_76_0\"";
    taillinks = " /link \"libboost_json-vc142-mt-gd-x64-1_76.lib\" /LIBPATH:\"C:\\Program Files\\boost_1_76_0\\stage\\lib\"";
    outfile = "/Fe:\"" + __dirname + "\\tools\\win\\icpp.exe\"";
}

const command = `${compiler} ${ccflags}${includes} ${outfile} ${cppfiles.join(" ")}${taillinks}`;

console.log("Running compile:");
console.log(command);
