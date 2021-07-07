//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { DEFAULT_TIMEOUT, DEFAULT_VOPTS, workflowBSQSingle, workflowGetErrors } from "../tooling/verifier/smt_workflows";


const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const smtlib_path = Path.join(bosque_dir, "bin/core/verify");
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");

function generateMASM(corefiles: {relativePath: string, contents: string}[], testsrc: string, macrodefs: string[]): [MIRAssembly | undefined, string[]] {
    const code: { relativePath: string, contents: string }[] = [...corefiles, { relativePath: "test.bsq", contents: testsrc }];
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", macrodefs, {namespace: "NSMain", names: ["main"]}, true, code);

    return [masm, errors];
}

function enqueueSMTTestRefute(testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();

    const allerrors = workflowGetErrors([testsrc], DEFAULT_VOPTS, "NSMain::main");
    const errlocation = allerrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline);
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        workflowBSQSingle(false, [testsrc], DEFAULT_VOPTS, DEFAULT_TIMEOUT, errlocation, "NSMain::main", (result: string) => {

        });
    }



    
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        const smtasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, errlocation, "NSMain::main");
        const smfc = buildSMT2file(smtasm, smtruntime, timeout, mode);

        runSMT2File(smfc, mode, start, cb);
    }
}

function enqueueSMTTestWitness(mode: "Refute" | "Reach", macrodefs: string[], corefiles: {relativePath: string, contents: string}[], smtruntime: string, testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const massembly = generateMASM(corefiles, testsrc, macrodefs);
    if(massembly[0] === undefined) {
        cb("error", start, new Date(), "Failed to generate assembly -- " + JSON.stringify(massembly[1]));
        return;
    }

    const sasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, { file: "[]", line: -1, pos: -1 }, "NSMain::main");
    const errlocation = sasm.allErrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline);
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        const smtasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, errlocation, "NSMain::main");
        const smfc = buildSMT2file(smtasm, smtruntime, timeout, mode);

        runSMT2File(smfc, mode, start, cb);
    }
}

function enqueueSMTTestEvaluate(mode: "Refute" | "Reach", macrodefs: string[], corefiles: {relativePath: string, contents: string}[], smtruntime: string, testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const massembly = generateMASM(corefiles, testsrc, macrodefs);
    if(massembly[0] === undefined) {
        cb("error", start, new Date(), "Failed to generate assembly -- " + JSON.stringify(massembly[1]));
        return;
    }

    const sasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, { file: "[]", line: -1, pos: -1 }, "NSMain::main");
    const errlocation = sasm.allErrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline);
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        const smtasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, errlocation, "NSMain::main");
        const smfc = buildSMT2file(smtasm, smtruntime, timeout, mode);

        runSMT2File(smfc, mode, start, cb);
    }
}

export {
    smtlib_path,
    smtruntime_path,
    enqueueSMTTest
};
