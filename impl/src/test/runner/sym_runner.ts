//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { exec } from "child_process";

import { SymTest, SymTestInternalChkShouldFail, PARALLEL_COUNT_SMT, TestResultKind } from "./test_decls";

function runSymTest(exepath: string, verbose: boolean, test: SymTest, cpayload: object, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void) {
    const start = new Date();
    try {
        const cmd = `${exepath} --${test.trgterror !== undefined ? "errorchk" : "passchk"}`;

        if(verbose) {
            cbpre(test);
        }

        const proc = exec(cmd, (err, stdout) => {
            const end = new Date();
            let status: "error" | "unknown" | "pass" | "unreachable" | "witness";
            let info: string = "";
            let witness: any = undefined;
            let smttime: number = -1;

            try {
                const robj = JSON.parse(stdout.toString().trim());
                status = robj["status"] as "error" | "unknown" | "pass" | "unreachable" | "witness";
                info = robj["info"] || "No Msg";
                witness = robj["witness"];
                smttime = robj["time"] || 0;
            }
            catch (ex) {
                status = "error";
                info = `Could not parse -- ${stdout}`;
            }

            if(err !== null && stdout.length === 0) {
                cb("error", test, start, end, smttime, err.toString());
            }
            else {
                if(test.resultKind === TestResultKind.errors) {
                    if(status === "unreachable") {
                        cb("pass", test, start, end, smttime);
                    }
                    else if (status === "witness") {
                        cb("fail", test, start, end, smttime, JSON.stringify(witness));
                    }
                    else {
                        if(status === "unknown") {
                            cb("passlimit", test, start, end, smttime, info);
                        }
                        else {
                            cb("error", test, start, end, smttime, info);
                        }
                    }
                }
                else {
                    if(status === "pass") {
                        cb("pass", test, start, end, smttime);
                    }
                    else if (status === "witness") {
                        cb("fail", test, start, end, smttime, JSON.stringify(witness));
                    }
                    else {
                        if(status === "unknown") {
                            cb("passlimit", test, start, end, smttime, info);
                        }
                        else {
                            cb("error", test, start, end, smttime, info);
                        }
                    }
                }
            }
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(cpayload, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end()
    }
    catch(ex: any) {
        const end = new Date();
        cb("error", test, start, end, ex.toString());
    }
}

function runSymTestShouldFail(exepath: string, verbose: boolean, test: SymTestInternalChkShouldFail, cpayload: object, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void) {
    const start = new Date();
    try {
        const cmd = `${exepath} --passchk`;

        if(verbose) {
            cbpre(test);
        }

        const proc = exec(cmd, (err, stdout) => {
            const end = new Date();
            let status: "error" | "unknown" | "pass" | "witness";
            let info: string = "";
            let witness: any = undefined;
            let smttime: number = -1;

            try {
                const robj = JSON.parse(stdout.toString().trim());
                status = robj["status"] as "error" | "unknown" | "pass" | "witness";
                info = robj["info"] || "No Msg";
                witness = robj["witness"];
                smttime = robj["time"] || 0;
            }
            catch (ex) {
                status = "error";
                info = `Could not parse -- ${stdout}`;
            }

            if(err !== null && stdout.length === 0) {
                cb("error", test, start, end, smttime, err.toString());
            }
            else {
                if (status === "pass") {
                    cb("fail", test, start, end, smttime, "Expected to find failing witness");
                }
                else if (status === "witness") {
                    cb("pass", test, start, end, smttime, JSON.stringify(witness));
                }
                else {
                    cb("error", test, start, end, smttime, (status === "unknown" ? "[UNKNOWN]" : "") + info);
                }
            }
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(cpayload, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end()
    }
    catch(ex: any) {
        const end = new Date();
        cb("error", test, start, end, ex.toString());
    }
}

function enqueueSymTest(exepath: string, verbose: boolean, test: SymTest, icppasm: any, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void) {
    runSymTest(exepath, verbose, test, icppasm, cbpre, cb);
}

function enqueueSymTestInternalChkShouldFail(exepath: string, verbose: boolean, test: SymTestInternalChkShouldFail, icppasm: any, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void) {
    runSymTestShouldFail(exepath, verbose, test, icppasm, cbpre, cb);
}

function generateTestResultCallback(exepath: string, verbose: boolean, winfo: {worklist: {test: SymTest | SymTestInternalChkShouldFail, cpayload: any}[], cpos: number, done: number}, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void, cbdone: () => void): (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void {
    return (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => {
        cb(result, test, start, end, smttime, info);

        winfo.done++;
        if(winfo.cpos < winfo.worklist.length) {
            const ttest = winfo.worklist[winfo.cpos].test;
            if(ttest instanceof SymTest) {
                enqueueSymTest(exepath, verbose, ttest, winfo.worklist[winfo.cpos].cpayload, cbpre, generateTestResultCallback(exepath, verbose, winfo, cbpre, cb, cbdone));
            }
            else {
                enqueueSymTestInternalChkShouldFail(exepath, verbose, ttest, winfo.worklist[winfo.cpos].cpayload, cbpre, generateTestResultCallback(exepath, verbose, winfo, cbpre, cb, cbdone));
            }
            winfo.cpos++;
        }
        else {
            if(winfo.done === winfo.worklist.length) {
                cbdone();
            }
        }
    };
}

function enqueueSymTests(exepath: string, tests: {test: SymTest | SymTestInternalChkShouldFail, cpayload: any}[], verbose: boolean, cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void, cbdone: () => void) {
    let shared_work_info = {worklist: tests, cpos: PARALLEL_COUNT_SMT, done: 0};

    for(let i = 0; i < Math.min(tests.length, PARALLEL_COUNT_SMT); ++i) {
        const ttest = tests[i].test;
        if(ttest instanceof SymTest) {
            enqueueSymTest(exepath, verbose, ttest, tests[i].cpayload, cbpre, generateTestResultCallback(exepath, verbose, shared_work_info, cbpre, cb, cbdone));
        }
        else {
            enqueueSymTestInternalChkShouldFail(exepath, verbose, ttest,tests[i].cpayload, cbpre, generateTestResultCallback(exepath, verbose, shared_work_info, cbpre, cb, cbdone));
        }
    }
}

export {
    enqueueSymTests
};
