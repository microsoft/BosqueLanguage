//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";

import { execSync } from "child_process";

import * as chalk from "chalk";

const bosque_dir: string = Path.join(__dirname, "../../../");
const exename: string = Path.join(bosque_dir, "/bin/cmd/bosque.js");

enum TestMode {
    Test,
    AppTest
}

type ApplicationTest = {
    dir: string,
    mode: TestMode,
    exepass: number,
    exefail: number,
    sympass: number,
    symfail: number
};

const s_application_list = [
    {dir: "readme_calc", mode: TestMode.Test, exepass: 3, exefail: 0, sympass: 1, symfail: 1},
    {dir: "readme_calc", mode: TestMode.AppTest, exepass: 0, exefail: 0, sympass: 3, symfail: 0},

    {dir: "tic_tac_toe", mode: TestMode.Test, exepass: 4, exefail: 0, sympass: 2, symfail: 1},
    //{dir: "tic_tac_toe", mode: TestMode.AppTest, exepass: 1, exefail: 0, sympass: 36, symfail: 1},

    {dir: "order", mode: TestMode.Test, exepass: 3, exefail: 0, sympass: 1, symfail: 1},
    {dir: "order", mode: TestMode.AppTest, exepass: 1, exefail: 0, sympass: 1, symfail: 0}
];

function runTest(t: ApplicationTest): boolean {
    let output = "[NO OUTPUT]";
    const start = new Date();
    try {
        const dirname = Path.join(bosque_dir, `src/test/apps/${t.dir}/package.json`);
        const cmd = `node ${exename} ${t.mode === TestMode.Test ? "test" : "apptest"} ${dirname}`;
        output = execSync(cmd).toString();
    }
    catch(ex) {
        if((ex as any)["status"] === 1) {
            output = (ex as any)["stdout"].toString();
        }
        else {
            process.stdout.write(chalk.magenta(`Failed to run ${t.mode === TestMode.Test ? "test" : "apptest"} on ${t.dir}.\n`));
            return false;
        }
    }
    const end = new Date();

    const reportlineall = (/^Ran ([0-9]+) tests in /m).exec(output);
    if(reportlineall === null) {
        process.stdout.write(chalk.magenta(`No test results reported for ${t.dir}.\n`));
        return false;
    }

    const reportlineall_exe = (/^Ran ([0-9]+) executable tests/m).exec(output);
    const reportlinepassall_exe = (/^All executable tests pass/m).exec(output);
    const reportlinepasssome_exe = (/^([0-9]+) executable tests pass/m).exec(output);
    const reportlinefail_exe = (/^Suite had ([0-9]+) executable test failures/m).exec(output);
    
    let exeok = true;
    if(reportlineall_exe !== null) {
        const exepass = reportlinepasssome_exe !== null ? parseInt(reportlinepasssome_exe[1]) : (reportlinepassall_exe !== null ? parseInt(reportlineall_exe[1]) : 0);
        const exefail = reportlinefail_exe !== null ? parseInt(reportlinefail_exe[1]) : 0;

        if(exepass !== t.exepass || exefail !== t.exefail) {
            process.stdout.write(chalk.red(`Mismatch in executable test results for ${t.dir} -- expected ${t.exepass} pass and ${t.exefail} fail *but* got ${exepass} pass and ${exefail} fail.\n`));
            exeok = false;
        }
    }

    const reportlineall_sym = (/^Ran ([0-9]+) symbolic tests/m).exec(output);
    const reportlinepassall_sym = (/^All symbolic tests pass/m).exec(output);
    const reportlinepasssome_sym = (/^([0-9]+) symbolic tests pass/m).exec(output);
    const reportlinefail_sym = (/^Suite had ([0-9]+) symbolic test failures/m).exec(output);
    
    let symok = true;
    let symout = false;
    if(reportlineall_sym !== null) {
        const sympass = reportlinepasssome_sym !== null ? parseInt(reportlinepasssome_sym[1]) : (reportlinepassall_sym !== null ? parseInt(reportlineall_sym[1]) : 0);
        const symfail = reportlinefail_sym !== null ? parseInt(reportlinefail_sym[1]) : 0;

        if(sympass !== t.sympass || symfail !== t.symfail) {
            if(symfail + sympass > t.symfail + t.sympass || symfail > t.symfail || sympass > t.sympass) {
                process.stdout.write(chalk.red(`Mismatch in symbolic test results for ${t.dir} -- expected ${t.sympass} pass and ${t.symfail} fail *but* got ${sympass} pass and ${symfail} fail.\n`));
                symok = false;
            }
            else {
                process.stdout.write(chalk.blue(`Timeout (or count mismatch) detected in ${t.dir} for ${(t.symfail + t.sympass) - (symfail + sympass)} tests.\n`));
                symout = true;
            }
        }
    }

    if(exeok && symok && !symout) {
        process.stdout.write(`${chalk.green("Passed")} checks for ${t.dir} ${t.mode === TestMode.Test ? "test" : "apptest"} (${(end.getTime() - start.getTime()) / 1000} seconds)\n`);
    } 
    process.stdout.write("\n");

    return exeok && symok;
}

let passcount = 0;
for(let i = 0; i < s_application_list.length; ++i) {
    process.stdout.write(`Running ${s_application_list[i].dir} ${s_application_list[i].mode === TestMode.Test ? "test" : "apptest"} ...\n`);

    const tpass = runTest(s_application_list[i]);

    if(tpass) {
        passcount++;
    }
}

if(passcount === s_application_list.length) {
    process.stdout.write(chalk.green(`\nAll application tests passed!\n`));
    process.exit(0);
}
else {
    process.stdout.write(chalk.red(`\n${s_application_list.length - passcount} application tests failed!\n`));
    process.exit(1);
}
