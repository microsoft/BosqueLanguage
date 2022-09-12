#!/usr/bin/env node

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { help } from "./args_load";
import { processBuildAction } from "./process_build";
import { processAppTestAction, processTestAction } from "./process_chk";
import { processRunAction, processFuzzAction, processRunSymbolicAction } from "./process_exe";

const fullargs = process.argv;

//slice of node bosque.js or bosque prefix of command
if (fullargs.length < 2) {
    help(undefined);
    process.exit(1);
}

let cmdop: string = "unset";
let cmdargs: string[] = [];
if (fullargs[1].endsWith("bosque.js")) {
    cmdop = fullargs[2];
    cmdargs = fullargs.slice(3);
}
else {
    cmdop = fullargs[1];
    cmdargs = fullargs.slice(2);
}

if (cmdop === "run" || cmdop === "debug") {
    processRunAction(cmdargs);
}
else if (cmdop === "symrun") {
    processRunSymbolicAction(cmdargs);
}
else if (cmdop === "build") {
    processBuildAction(cmdargs);
}
else if (cmdop === "test") {
    processTestAction(cmdargs);
}
else if (cmdop === "apptest") {
    processAppTestAction(cmdargs);
}
else if (cmdop === "fuzz") {
    processFuzzAction(cmdargs);
}
else {
    help(undefined);
    process.exit(1);
}
