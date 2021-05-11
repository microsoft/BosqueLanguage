//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fs = require("fs");
const path = require("path");

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/interpreter"));
const cppfiles = [rootsrc, path.join(rootsrc, "assembly"), path.join(rootsrc, "core"), path.join(rootsrc, "runtime")].map((pp) => pp + "/*.cpp");

const ccflags = "-g -BSQ_DEBUG_BUILD -Wall -std=c++17";  

//-Wextra

let compiler = "";
let includes = " ";
let outfile = "";
if(process.platform === "darwin") {
    compiler = "clang++";
    outfile = __dirname + "/tools/macos/icpp";
}
else if(process.platform === "linux") {
    compiler = "clang++";
    outfile = __dirname + "/tools/linux/icpp";
}
else {
    compiler = "clang.exe";
    includes = " --include-directory=\"C:\\Program Files\\boost_1_76_0\" --library-directory=\"C:\\Program Files\\boost_1_76_0\\stage\\lib\" ";
    outfile = __dirname + "\\tools\\win\\icpp.exe";
}

const command = `${compiler} ${ccflags}${includes}-o ${outfile} ${cppfiles.join(" ")}`;

console.log("Running compile:");
console.log(command);
