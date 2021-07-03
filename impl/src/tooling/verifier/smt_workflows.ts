//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import chalk from "chalk";

import { MIRAssembly, PackageConfig } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { Payload, SMTEmitter } from "../../tooling/verifier/smtdecls_emitter";
import { VerifierOptions } from "../../tooling/verifier/smt_exp";
import { MIRInvokeKey } from "../../compiler/mir_ops";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../"));
const smtlib_path = Path.join(bosque_dir, "bin/core/verify");
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
const exepath = Path.normalize(Path.join(bosque_dir, "/build/out/chkworkflow" + (process.platform === "win32" ? ".exe" : "")));

const smtruntime = FS.readFileSync(smtruntime_path).toString();

const DEFAULT_TIMEOUT = 5000;

const DEFAULT_VOPTS = {
    ISize: 5,
    BigXMode: "Int",
    OverflowEnabled: false,
    FPOpt: "Real",
    StringOpt: "ASCII",
    SimpleQuantifierMode: false,
    SpecializeSmallModelGen: false
} as VerifierOptions;

function generateMASM(files: string[], entrypoint: string, dosmallopts: boolean): { masm: MIRAssembly | undefined, errors: string[] } {
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const corefiles = FS.readdirSync(smtlib_path);

        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(smtlib_path, corefiles[i]);
            code.push({ relativePath: cfpath, contents: FS.readFileSync(cfpath).toString() });
        }
 
        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            const file = { relativePath: realpath, contents: FS.readFileSync(realpath).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        return { masm: undefined, errors: ["Failed to load code"] };
    }

    let namespace = "NSMain";
    let entryfunc = "main";
    const cpos = entrypoint.indexOf("::");
    if(cpos === -1) {
        entryfunc = entrypoint;
    }
    else {
        namespace = entrypoint.slice(0, cpos);
        entryfunc = entrypoint.slice(cpos + 2);
    }

    const macros = dosmallopts ? ["SMALL_MODEL_PATH"] : [];
    return MIREmitter.generateMASM(new PackageConfig(), "debug", macros, {namespace: namespace, names: [entryfunc]}, true, code);
}

function generateSMTPayload(masm: MIRAssembly, mode: "check" | "evaluate" | "invert", timeout: number, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): Payload | undefined {
    try {
        return SMTEmitter.generateSMTPayload(masm, mode, timeout, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        process.stderr.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function emitSMT2File(cfile: string, into: string) {
    try {
        FS.writeFileSync(into, cfile);
    }
    catch (fex) {
        process.stderr.write(chalk.red(`Failed to write file -- ${fex}\n`));
    }
}

function runVEvaluator(cpayload: object, workflow: "check" | "eval" | "invert", bson: boolean): string {
    try {
        return execSync(`${exepath} ${bson ? " --bson" : ""} --${workflow}`, { input: JSON.stringify(cpayload) }).toString().trim();
    }
    catch(ex) {
        return JSON.stringify({result: "error", info: `${ex}`});
    }
}

function workflowGetErrors(files: string[], vopts: VerifierOptions, entrypoint: MIRInvokeKey): { file: string, line: number, pos: number, msg: string }[] | undefined {
    try {
        const { masm, errors } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2));
            return undefined;
        }
        else {    
            return SMTEmitter.generateSMTAssemblyAllErrors(masm, vopts, entrypoint);
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function workflowEmitToFile(into: string, files: string[], mode: "check" | "evaluate" | "invert", timeout: number, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey) {
    try {
        const { masm, errors } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2));
            process.exit(1);
        }
        else {    
            const res = generateSMTPayload(masm, mode, timeout, vopts, errorTrgtPos, entrypoint);
            if(res !== undefined) {
                emitSMT2File(res.smt2decl, into);
            }
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function workflowBSQSingle(bson: boolean, files: string[], vopts: VerifierOptions, timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): string {
    try {
        const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            return JSON.stringify({result: "error", info: "compile errors"});
        }
        else {    
            const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
            if(res === undefined) {
                return JSON.stringify({result: "error", info: "payload generation error"});
            }

            return runVEvaluator(res, "check", bson);
        }
    } catch(e) {
        return JSON.stringify({result: "error", info: `${e}`});
    }
}

function wfCheckSmall(bson: boolean, files: string[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogres: boolean): {result: string, time: number} | {result: string, time: number, input: any} | undefined {
    //
    //TODO: should compute min viable BV size here
    //
    const BV_SIZES = [3, 5, 8, 16];
    let vopts = DEFAULT_VOPTS;

    for(let i = 0; i < BV_SIZES.length; ++i) {
        vopts.ISize = BV_SIZES[i];
        if(printprogres) {
            process.stderr.write(`Checking small (${BV_SIZES[i]}) bit width...\n`);
            return undefined;
        }

        try {
            const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
            if(masm === undefined) {
                if(printprogres) {
                    process.stderr.write(`Compile errors\n`);
                    return undefined;
                }
            }
            else {    
                const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
                if(res === undefined) {
                    if(printprogres) {
                        process.stderr.write(`Payload generation errors`);
                        return undefined;
                    }
                }
    
                const cres = runVEvaluator(res, "check", bson);
            }
        } catch(e) {
            if(printprogres) {
                process.stderr.write(`Failure: ${e}\n`);
                return undefined;
            }
        }   
    }

    return undefined;
}

function workflowBSQCheck(bson: boolean, files: string[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogres: boolean): string {
    


}

function workflowEvaluateSingle(bson: boolean, files: string[], jin: any[], vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey): string {
    try {
        const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            return JSON.stringify({result: "error", info: "compile errors"});
        }
        else {    
            const res = generateSMTPayload(masm, "evaluate", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                return JSON.stringify({result: "error", info: "payload generation error"});
            }

            return runVEvaluator({...res, jin: jin}, "eval", bson);
        }
    } catch(e) {
        return JSON.stringify({result: "error", info: `${e}`});
    }
}

function workflowInvertSingle(bson: boolean, files: string[], jout: any, vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey): string {
    try {
        const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            return JSON.stringify({result: "error", info: "compile errors"});
        }
        else {    
            const res = generateSMTPayload(masm, "invert", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                return JSON.stringify({result: "error", info: "payload generation error"});
            }

            return runVEvaluator({...res, jout: jout}, "invert", bson);
        }
    } catch(e) {
        return JSON.stringify({result: "error", info: `${e}`});
    }
}

export {
    workflowGetErrors, workflowEmitToFile, workflowBSQSingle, workflowBSQCheck, workflowEvaluateSingle, workflowInvertSingle,
    DEFAULT_TIMEOUT, DEFAULT_VOPTS
};
