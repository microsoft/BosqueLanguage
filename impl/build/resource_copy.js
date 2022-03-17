//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const path = require("path");
const fsx = require("fs-extra");

const rootsrc = path.join(__dirname, "../", "src");
const rootbin = path.join(__dirname, "../", "bin");

function copyResourceDir(dir) {
    const srcpath = path.join(rootsrc, dir);
    const dstpath = path.join(rootbin, dir);

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fsx.ensureDirSync(dstpath);
    fsx.emptyDirSync(dstpath);
    fsx.copySync(srcpath, dstpath);
}

process.stdout.write(`Copying resources...\n`);

copyResourceDir("core");
copyResourceDir("tooling/checker/runtime");
copyResourceDir("test/bsqunit/tests");

process.stdout.write(`done!\n`);