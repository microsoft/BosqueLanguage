//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { DEFAULT_VOPTS, workflowGetErrors } from "../tooling/verifier/smt_workflows";


function runCompilerTest(testsrc: string): { result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string } {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", contents: testsrc}];
    try {
        const allerrors = workflowGetErrors(codeinfo, DEFAULT_VOPTS, "NSMain::main");

        return {
            result: allerrors === undefined ? "pass" : "fail",
            start: start,
            end: new Date()
        }
    }
    catch (ex) {
        return {
            result: "error",
            start: start,
            end: new Date,
            info: `${ex}`
        }
    }
}

export {
    runCompilerTest
};