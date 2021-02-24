//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";


function generateMASM(corefiles: {relativePath: string, contents: string}[], testsrc: string): [MIRAssembly | undefined, string[]] {
    const code: { relativePath: string, contents: string }[] = [...corefiles, { relativePath: "test.bsq", contents: testsrc }];
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", {namespace: "NSMain", names: ["main"]}, true, code);

    return [masm, errors];
}


function runCompilerTest(corefiles: {relativePath: string, contents: string}[], testsrc: string): { result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string } {
    const start = new Date();
    try {
        const [masm] = generateMASM(corefiles, testsrc);

        return {
            result: masm === undefined ? "pass" : "fail",
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