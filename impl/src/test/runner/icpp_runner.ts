//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { exec } from "child_process";

import { ICPPTest, TestResultKind } from "./test_decls";

const PARALLEL_COUNT = 4;

function runICPPTest(exepath: string, verbose: boolean, test: ICPPTest, icppjson: {code: object, args: any[], main: string}, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    try {
        const cmd = `${exepath} --stream`;

        if(verbose) {
            cbpre(test);
        }

        const proc = exec(cmd, (err, stdout) => {
            const end = new Date();
            let status: "error" | "success" | "failure" = "error";
            let msg: string = "";
            let value: any = undefined;

            try {
                const robj = JSON.parse(stdout.toString().trim());
                status = robj["status"] as "error" | "success" | "failure";
                msg = robj["msg"] || "No Msg";
                value = robj["value"];
            }
            catch (ex) {
                status = "error";
                msg = `Could not parse -- ${stdout}`;
            }

            if(err !== null && stdout.length === 0) {
                cb("error", test, start, end, err.toString());
            }
            else {
                if(test.resultKind === TestResultKind.errors) {
                    if(status === "success") {
                        cb("pass", test, start, end);
                    }
                    else if (status === "failure") {
                        cb("fail", test, start, end, msg);
                    }
                    else {
                        cb("error", test, start, end, msg);
                    }
                }
                else {
                    if(status === "success") {
                        if(value === true) {
                            cb("pass", test, start, end);
                        }
                        else {
                            cb("fail", test, start, end, JSON.stringify(value));
                        }
                    }
                    else if (status === "failure") {
                        cb("error", test, start, end, msg);
                    }
                    else {
                        cb("error", test, start, end, msg);
                    }
                }
            }
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(icppjson, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end()
    }
    catch(ex: any) {
        const end = new Date();
        cb("error", test, start, end, ex.toString());
    }
}

function enqueueICPPTest(exepath: string, verbose: boolean, test: ICPPTest, icppasm: any, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void) {
    if(!test.fuzz) {
        runICPPTest(exepath, verbose, test, icppasm, cbpre, cb);
    }
    else {
        cb("fail", test, new Date(), new Date(), "Fuzzing isn't wired up yet");
    }
}

function generateTestResultCallback(exepath: string, verbose: boolean, winfo: {worklist: {test: ICPPTest, icppasm: any}[], cpos: number, done: number}, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void, cbdone: () => void): (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void {
    return (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => {
        cb(result, test, start, end, info);

        winfo.done++;
        if(winfo.cpos < winfo.worklist.length) {
            enqueueICPPTest(exepath, verbose, winfo.worklist[winfo.cpos].test, winfo.worklist[winfo.cpos].icppasm, cbpre, generateTestResultCallback(exepath, verbose, winfo, cbpre, cb, cbdone));
            winfo.cpos++;
        }
        else {
            if(winfo.done === winfo.worklist.length) {
                cbdone();
            }
        }
    };
}

function enqueueICPPTests(exepath: string, tests: {test: ICPPTest, icppasm: any}[], verbose: boolean, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void, cbdone: () => void) {
    let shared_work_info = {worklist: tests, cpos: PARALLEL_COUNT, done: 0};

    for(let i = 0; i < PARALLEL_COUNT; ++i) {
        enqueueICPPTest(exepath, verbose, tests[i].test, tests[i].icppasm, cbpre, generateTestResultCallback(exepath, verbose, shared_work_info, cbpre, cb, cbdone));
    }
}

export {
    enqueueICPPTests
};
