//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { exec } from "child_process";

import { ICPPTest } from "./test_decls";
import { MIRAssembly } from "../../compiler/mir_assembly";

function generateICPPAssembly(masm: MIRAssembly, istestbuild: boolean, topts: TranspilerOptions, entrypoints: MIRInvokeKey[]): any {
    let res: any = undefined;
    try {
        res = ICPPEmitter.generateICPPAssembly(masm, istestbuild, topts, entrypoints);
    } catch(e) {
        process.stdout.write(chalk.red(`ICPP bytecode generate error -- ${e}\n`));
        process.exit(1);
    }
    return res;
}

function runICPPTest(exepath: string, test: ICPPTest, icppjson: {code: object, args: any[], main: string}, cb: (result: "pass" | "fail" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    try {
        const cmd = `${exepath} --stream`;

        const proc = exec(cmd, (err, stdout, stderr) => {
            const end = new Date();
            cb(stdout.toString().trim());
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(icppjson, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end()
    }
    catch(ex) {
        const end = new Date();
        cb("error", start, end, JSON.stringify(ex));
    }
}

function enqueueICPPTest(exepath: string, test: ICPPTest, masm: MIRAssembly, icppasm: any, cb: (result: "pass" | "fail" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();

    if(!test.fuzz) {
        workflowRunICPPFile([], )
    }
    else {
        xxx;
    }

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

function enqueueICPPTest(testsrc: string, jargs: any[], expected: string | undefined, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const end = new Date();
    cb("fail", start, end, "Disabled");
}


export {
    enqueueICPPTest
};
