//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import chalk from "chalk";

function runTests() {
    process.stderr.write(chalk.red("Test running is not supported yet.\n"));
}

function fuzzTests() {
    process.stderr.write(chalk.red("Fuzz running is not supported yet.\n"));
}

export {
    runTests, fuzzTests
};
