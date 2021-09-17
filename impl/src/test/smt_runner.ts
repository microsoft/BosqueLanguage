//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { VerifierOptions } from "../tooling/verifier/smt_exp";
import { DEFAULT_TIMEOUT, workflowBSQInfeasibleSingle, workflowBSQWitnessSingle, workflowEvaluateSingle, workflowGetErrors } from "../tooling/verifier/smt_workflows";

const vopts_err = {
    ISize: 64,
    StringOpt: "ASCII",
    EnableCollection_SmallHavoc: false,
    EnableCollection_LargeHavoc: true,
    EnableCollection_SmallOps: false,
    EnableCollection_LargeOps: true
} as VerifierOptions;

const vopts_refute = {
    ISize: 8,
    StringOpt: "ASCII",
    EnableCollection_SmallHavoc: false,
    EnableCollection_LargeHavoc: true,
    EnableCollection_SmallOps: false,
    EnableCollection_LargeOps: true
} as VerifierOptions;

const vopts_witnesssmall = {
    ISize: 5,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: false,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: false
} as VerifierOptions;

const vopts_witnesslarge = {
    ISize: 8,
    StringOpt: "ASCII",
    EnableCollection_SmallHavoc: true,
    EnableCollection_LargeHavoc: true,
    EnableCollection_SmallOps: true,
    EnableCollection_LargeOps: true
} as VerifierOptions;

const vopts_evaluate = {
    ISize: 8,
    StringOpt: "ASCII",
    EnableCollection_SmallHavoc: true,
    EnableCollection_LargeHavoc: true,
    EnableCollection_SmallOps: true,
    EnableCollection_LargeOps: true
} as VerifierOptions;

function enqueueSMTTestRefute(testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", filepath: "test.bsq", contents: testsrc}];

    const allerrors = workflowGetErrors(codeinfo, vopts_err, "NSMain::main");
    const errlocation = allerrors !== undefined ? allerrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline) : undefined;
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        workflowBSQInfeasibleSingle(codeinfo, vopts_refute, DEFAULT_TIMEOUT, errlocation, "NSMain::main", (result: string) => {
            const end = new Date();
            try {
                const jres = JSON.parse(result);
                const rkind = jres["result"] as "error" | "unreachable" | "possible" | "timeout";

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

function enqueueSMTTestWitness(testsrc: string, trgtline: number, dosmall: boolean, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", filepath: "test.bsq", contents: testsrc}];

    const allerrors = workflowGetErrors(codeinfo, vopts_err, "NSMain::main");
    const errlocation = allerrors !== undefined ? allerrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline) : undefined;
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        workflowBSQWitnessSingle(codeinfo, dosmall ? vopts_witnesssmall : vopts_witnesslarge, DEFAULT_TIMEOUT, errlocation, "NSMain::main", (result: string) => {
            const end = new Date();
            try {
                const jres = JSON.parse(result);
                const rkind = jres["result"] as "error" | "unreachable" | "witness" | "timeout";

                if(rkind === "error") {
                    cb("error", start, end, result);    
                }
                else if(rkind === "timeout") {
                    cb("unknown/timeout", start, end, result);  
                }
                else if(rkind === "unreachable") {
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
    const codeinfo = [{fpath: "test.bsq", filepath: "test.bsq", contents: testsrc}];

    workflowEvaluateSingle(codeinfo, jin, vopts_evaluate, DEFAULT_TIMEOUT, "NSMain::main", (result: string) => {
        const end = new Date();

        try {
            const jres = JSON.parse(result);
            const rkind = jres["result"] as "error" | "unreachable" | "output" | "timeout";

            if(rkind === "error") {
                cb("error", start, end, result);    
            }
            else if(rkind === "timeout") {
                cb("unknown/timeout", start, end, result);  
            }
            else if(rkind === "unreachable") {
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
