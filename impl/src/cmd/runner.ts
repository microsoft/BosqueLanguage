//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import chalk from "chalk";

function evalStdIn() {
    process.stderr.write(chalk.red("Execution with read from StdIn not implemented yet.\n"));
}

function evalArgs() {
    process.stderr.write(chalk.red("Execution with cmd provided arguments not implemented yet.\n"));
}

function transpileToNPM() {
    process.stderr.write(chalk.red("Transpile to NPM module not implemented yet.\n"));
}

export {
    evalStdIn, evalArgs, transpileToNPM
};