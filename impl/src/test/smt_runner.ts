//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { DEFAULT_TIMEOUT, DEFAULT_VOPTS, workflowBSQInfeasibleSingle, workflowBSQWitnessSingle, workflowEvaluateSingle, workflowGetErrors } from "../tooling/verifier/smt_workflows";

function enqueueSMTTestRefute(testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", contents: testsrc}];

    const allerrors = workflowGetErrors(codeinfo, DEFAULT_VOPTS, "NSMain::main");
    const errlocation = allerrors !== undefined ? allerrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline) : undefined;
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        workflowBSQInfeasibleSingle(false, codeinfo, DEFAULT_VOPTS, DEFAULT_TIMEOUT, errlocation, "NSMain::main", (result: string) => {
            const end = new Date();
            try {
                const jres = JSON.parse(result);
                const rkind = jres["result"] as "error" | "infeasible" | "possible" | "timeout";

                if(rkind === "error") {
                    cb("error", start, end, result);    
                }
                else if(rkind === "timeout") {
                    cb("unknown/timeout", start, end, result);  
                }
                else if(rkind === "possible") {
                    cb("fail", start, end, result);
                }
                else {
                    cb("pass", start, end);
                }
            }
            catch (ex) {
                cb("error", start, end, `${ex}`);
            }
        });
    }
}

function enqueueSMTTestWitness(testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", contents: testsrc}];

    const allerrors = workflowGetErrors(codeinfo, DEFAULT_VOPTS, "NSMain::main");
    const errlocation = allerrors !== undefined ? allerrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline) : undefined;
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        workflowBSQWitnessSingle(false, codeinfo, DEFAULT_VOPTS, DEFAULT_TIMEOUT, errlocation, "NSMain::main", (result: string) => {
            const end = new Date();
            try {
                const jres = JSON.parse(result);
                const rkind = jres["result"] as "error" | "infeasible" | "witness" | "timeout";

                if(rkind === "error") {
                    cb("error", start, end, result);    
                }
                else if(rkind === "timeout") {
                    cb("unknown/timeout", start, end, result);  
                }
                else if(rkind === "infeasible") {
                    cb("fail", start, end, result);
                }
                else {
                    cb("pass", start, end, result);
                }
            }
            catch (ex) {
                cb("error", start, end, `${ex}`);
            }
        });
    }
}

function enqueueSMTTestEvaluate(testsrc: string, jin: any[], expected: any, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", contents: testsrc}];

    workflowEvaluateSingle(false, codeinfo, jin, DEFAULT_VOPTS, DEFAULT_TIMEOUT, "NSMain::main", (result: string) => {
        const end = new Date();

        try {
            const jres = JSON.parse(result);
            const rkind = jres["result"] as "error" | "infeasible" | "output" | "timeout";

            if(rkind === "error") {
                cb("error", start, end, result);    
            }
            else if(rkind === "timeout") {
                cb("unknown/timeout", start, end, result);  
            }
            else if(rkind === "infeasible") {
                if(expected === undefined) {
                    cb("pass", start, end);
                }
                else {
                    cb("fail", start, end, result);
                }
            }
            else {
                const routput = JSON.stringify(jres["output"]);
                const eoutput = JSON.stringify(expected);

                if(routput === eoutput) {
                    cb("pass", start, end, result);
                }
                else {
                    cb("fail", start, end, `Expected: ${eoutput} -- Result: ${routput}`);
                }
            }
        }
        catch (ex) {
            cb("error", start, end, `${ex}`);
        }
    });
}

export {
    enqueueSMTTestRefute, enqueueSMTTestWitness, enqueueSMTTestEvaluate
};
