//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const fs = require(fs);
const path = require("path");
const fsx = require("fs-extra");

const rootsrc = path.normalize(path.join(__dirname, "../", "src/tooling/interpreter/"));
const alldirs = [rootsrc, path.join(rootsrc, "assembly"), path.join(rootsrc, "core"), path.join(rootsrc, "runtime")];

var cppfiles = [].join(...alldirs.forEach((dd) => fs.readdirSync(dd).filter(fn => fn.endsWith('.cpp'))));

//const rootbin = path.normalize(path.join(__dirname, "../", "bin"));
