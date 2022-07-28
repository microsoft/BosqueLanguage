//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
/*
import * as FS from "fs";
import * as Path from "path";

import { execSync } from "child_process";

import * as chalk from "chalk";

const bosque_dir: string = Path.join(__dirname, "../../../");

enum TestMode {
    Test,
    AppTest
}

type ApplicationTest = {
    dir: string,
    mode: TestMode,
    pass: number,
    fail: number
};

const s_application_list = [
    {dir: "readme_calc", mode: TestMode.Test, pass: 0, fail: 0},
    {dir: "tic_tac_toe", mode: TestMode.Test, pass: 0, fail: 0}
];

function runTest(t: ApplicationTest): boolean {
    let output = "[NO OUTPUT]";
    try {
        const cmd = `node ${bosque_dir}/bin/cmd/bosque.js ${t.mode === TestMode.Test ? "test" : "apptest"} ${bosque_dir}src/test/apps/${t.dir}/package.json`;
        output = execSync(cmd).toString();
    }
    catch(ex) {
        process.stdout.write(chalk.magenta(`Failed to run ${t.mode === TestMode.Test ? "test" : "apptest"} on ${t.dir}.\n`));
        return false;
    }

    const reportlineall = (/^Ran (?<test_total>[0-9]+) tests in /m).exec(output);

    const reportlineall_exe = (/^Ran (?<test_total>[0-9]+) executable tests /m).exec(output);
    const reportlinepass_exe = (/^Ran (?<test_total>[0-9]+) executable tests /m).exec(output);
    const reportlinefail_exe = (/^Ran (?<test_total>[0-9]+) executable tests /m).exec(output);
}

for(let i = 0; i < s_application_list.length; ++i) {

}
*/