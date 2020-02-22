//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const sh = require("child_process");
const path = require("path");
const fsx = require("fs-extra");

const rootsrc = path.normalize(path.join(__dirname, "../", "src"));
const rootbin = path.normalize(path.join(__dirname, "../", "bin"));

function copyResourceDir(dir) {
    const srcpath = path.normalize(path.join(rootsrc, dir));
    const dstpath = path.normalize(path.join(rootbin, dir));

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fsx.ensureDirSync(dstpath);
    fsx.emptyDirSync(dstpath);
    fsx.copySync(srcpath, dstpath);
}

process.stdout.write(`Copying resources...\n`);

copyResourceDir("core");
copyResourceDir("tooling/aot/runtime");
copyResourceDir("tooling/aot/runtime/bsqcustom");
copyResourceDir("tooling/bmc/runtime");
copyResourceDir("test/tests");

if(process.platform === "linux") {
    const z3path = path.join(rootbin, "/tooling/bmc/runtime/bin/linux/z3")
    sh.execSync(`chmod a+x ${z3path}`);
}

if(process.platform === "darwin") {
    const z3path = path.join(rootbin, "/tooling/bmc/runtime/bin/macos/z3")
    sh.execSync(`chmod a+x ${z3path}`);
}

process.stdout.write(`done!\n`);