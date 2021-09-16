//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
/*
import { DEFAULT_TOPTS, workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";

function enqueueICPPTest(testsrc: string, jargs: any[], expected: string | undefined, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", filepath: "test.bsq", contents: testsrc}];

    workflowRunICPPFile(jargs, codeinfo, DEFAULT_TOPTS, "NSMain::main", (result: string | undefined) => {
        const end = new Date();
        try {
            if(result === undefined) {
                if(expected === undefined) {
                    cb("pass", start, end);
                }
                else {
                    cb("fail", start, end, result);
                }
            }
            else {
                if(expected === result) {
                    cb("pass", start, end, result);
                }
                else {
                    cb("fail", start, end, `Expected: ${expected} -- Result: ${result}`);
                }
            }
        }
        catch (ex) {
            cb("error", start, end, `${ex}`);
        }
    });
}
*/

function enqueueICPPTest(testsrc: string, jargs: any[], expected: string | undefined, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const end = new Date();
    cb("fail", start, end, "Disabled");
}


export {
    enqueueICPPTest
};
