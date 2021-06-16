//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";
import { exec, ExecException } from "child_process";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { ICPPAssembly, TranspilerOptions } from "../tooling/icpp/transpiler/icpp_assembly";
import { MIRInvokeKey } from "../compiler/mir_ops";
import { ICPPEmitter } from "../tooling/icpp/transpiler/icppdecls_emitter";

let icpppath: string | undefined = undefined;
if (process.platform === "win32") {
    icpppath = "build/output/icpp.exe";
}
else if (process.platform === "linux") {
    icpppath = "build/output/icpp";
}
else {
    icpppath = "build/output/icpp";
}

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const icpplib_path = Path.join(bosque_dir, "bin/core/execute");

function generateMASM(corefiles: {relativePath: string, contents: string}[], testsrc: string, macrodefs: string[]): [MIRAssembly | undefined, string[]] {
    const code: { relativePath: string, contents: string }[] = [...corefiles, { relativePath: "test.bsq", contents: testsrc }];
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", macrodefs, {namespace: "NSMain", names: ["main"]}, true, code);

    return [masm, errors];
}

function runICPPFile(prover: "z3" | "cvc4", cfile: string, mode: "Refute" | "Reach", start: Date, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {

    const smtpath = Path.normalize(Path.join(bosque_dir, (prover === "z3" ? z3pathsmt : cvc4pathsmt) as string));
    const smtflags = (prover === "z3") ? "-smt2 -in" : "--lang=smt2 --cegqi-all --tlimit=1000";

    const res = exec(`${smtpath} ${smtflags}`, (err: ExecException | null, stdout: string, stderr: string) => {
        if (err) {
            cb("error", start, new Date(), stdout);
        }
        else {
            const res = stdout.trim();

            if (mode === "Refute") {
                if (res === "unsat") {
                    cb("pass", start, new Date());
                }
                else if (res === "sat") {
                    cb("fail", start, new Date());
                }
                else {
                    cb("unknown/timeout", start, new Date(), stdout);
                }
            }
            else {
                if (res === "sat") {
                    cb("pass", start, new Date());
                }
                else if (res === "unsat") {
                    cb("fail", start, new Date());
                }
                else {
                    cb("unknown/timeout", start, new Date(), stdout);
                }
            }
        }
    });

    res.stdin.setDefaultEncoding('utf-8');
    res.stdin.write(cfile);
    res.stdin.end();
}

const topts = {
} as TranspilerOptions;

function generateICPPAssembly(masm: MIRAssembly, topts: TranspilerOptions, entrypoint: MIRInvokeKey): ICPPAssembly | undefined {
    let res: ICPPAssembly | undefined = undefined;
    try {
        res = ICPPEmitter.generateICPPAssembly(masm, topts, entrypoint);
    } catch(e) {
       //leave as undefined
    }
    return res;
}

function enqueueICPPTest(macrodefs: string[], corefiles: {relativePath: string, contents: string}[], testsrc: string, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const massembly = generateMASM(corefiles, testsrc, macrodefs);
    if(massembly[0] === undefined) {
        cb("error", start, new Date(), "Failed to generate assembly -- " + JSON.stringify(massembly[1]));
        return;
    }
    else {
        const icppasm = generateICPPAssembly(massembly[0], topts, "NSMain::main");
        if (icppasm === undefined) {
            cb("error", start, new Date(), "Invalid trgt line");
        }
        else {
            const icppjson = JSON.stringify(icppasm.jsonEmit(), undefined, "  ");

            runSMT2File(prover, smfc, mode, start, cb);
        }
    }
}

export {
    icpplib_path,
    enqueueICPPTest
};
