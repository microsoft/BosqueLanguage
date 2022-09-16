//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { exec } from "child_process";

import { ICPPTest, PARALLEL_COUNT_ICPP, TestResultKind } from "./test_decls";

function runICPPTest(exepath: string, verbose: boolean, test: ICPPTest, icppjson: {code: object, args: any[], main: string}, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void) {
    const start = new Date();
    try {
        const cmd = `${exepath} --stream`;

        if(verbose) {
            cbpre(test);
        }

        const proc = exec(cmd, {env: {...process.env, ICPP_OUTPUT_MODE: "json"}}, (err, stdout, stderr) => {
            const end = new Date();
            let status: "error" | "success" | "failure" = "error";
            let msg: string = "";
            let value: any = undefined;
            let icpptime: number = -1;
            
            try {
                const robj = JSON.parse(stdout.toString().trim());
                status = robj["status"] as "error" | "success" | "failure";
                msg = robj["msg"] || "No Msg";
                value = robj["value"];
                icpptime = robj["time"] || 0;
            }
            catch (ex) {
                status = "error";
                msg = `Could not parse -- ${stdout}`;
            }

            if(err !== null && stdout.length === 0) {
                cb("error", test, start, end, icpptime, stderr.toString());
            }
            else {
                if(test.resultKind === TestResultKind.errors) {
                    if(status === "success") {
                        cb("pass", test, start, end, icpptime);
                    }
                    else if (status === "failure") {
                        cb("fail", test, start, end, icpptime, msg);
                    }
                    else {
                        cb("error", test, start, end, icpptime, msg);
                    }
                }
                else {
                    if(status === "success") {
                        if(value === true) {
                            cb("pass", test, start, end, icpptime);
                        }
                        else {
                            cb("fail", test, start, end, icpptime, JSON.stringify(value));
                        }
                    }
                    else if (status === "failure") {
                        cb("error", test, start, end, icpptime, msg);
                    }
                    else {
                        cb("error", test, start, end, icpptime, msg);
                    }
                }
            }
        });

        if(proc.stdin === null || proc.stdin === undefined) {
            cb("error", test, start, new Date(), -1, "Killed process!!!");
            proc.kill();
        }
        else {
            proc.stdin.on("error", (err: Error) => { cb("error", test, start, new Date(), -1, `Write to stdin error ${err}`); });

            proc.stdin.setDefaultEncoding('utf-8');
            proc.stdin.write(JSON.stringify(icppjson, undefined, 2));
            proc.stdin.write("\n");
            proc.stdin.end();
        }
    }
    catch(ex: any) {
        const end = new Date();
        cb("error", test, start, end, ex.toString());
    }
}

function enqueueICPPTest(exepath: string, verbose: boolean, test: ICPPTest, apiinfo: any, icppasm: any, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void) {
    if(!test.fuzz) {
        const icppjson = {
            code: {
                api: apiinfo, 
                bytecode: icppasm 
            }, 
            args: [], 
            main: test.invkey
        };

        runICPPTest(exepath, verbose, test, icppjson, cbpre, cb);
    }
    else {
        cb("fail", test, new Date(), new Date(), -1, "Fuzzing isn't wired up yet");
    }
}

function generateTestResultCallback(exepath: string, verbose: boolean, winfo: {worklist: {test: ICPPTest, apiinfo: any, icppasm: any}[], cpos: number, done: number}, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void, cbdone: () => void): (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void {
    return (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => {
        cb(result, test, start, end, icpptime, info);

        winfo.done++;
        if(winfo.cpos < winfo.worklist.length) {
            enqueueICPPTest(exepath, verbose, winfo.worklist[winfo.cpos].test, winfo.worklist[winfo.cpos].apiinfo, winfo.worklist[winfo.cpos].icppasm, cbpre, generateTestResultCallback(exepath, verbose, winfo, cbpre, cb, cbdone));
            winfo.cpos++;
        }
        else {
            if(winfo.done === winfo.worklist.length) {
                cbdone();
            }
        }
    };
}

function enqueueICPPTests(exepath: string, tests: {test: ICPPTest, apiinfo: any, icppasm: any}[], verbose: boolean, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void, cbdone: () => void) {
    let shared_work_info = {worklist: tests, cpos: PARALLEL_COUNT_ICPP, done: 0};

    for(let i = 0; i < Math.min(tests.length, PARALLEL_COUNT_ICPP); ++i) {
        enqueueICPPTest(exepath, verbose, tests[i].test, tests[i].apiinfo, tests[i].icppasm, cbpre, generateTestResultCallback(exepath, verbose, shared_work_info, cbpre, cb, cbdone));
    }
}

export {
    enqueueICPPTests
};
