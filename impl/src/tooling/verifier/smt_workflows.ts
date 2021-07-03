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

type CheckerResult = "infeasible" | "witness" | "timeout";

//ocrresponds to 1a, 1b, 2a, 2b in paper
type ChkWorkflowOutcome = "infeasible" | "witness" | "partial" | "exhaustive";

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

function wfCheckSmall(bson: boolean, files: string[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    //
    //TODO: should compute min viable BV size here
    //
    const BV_SIZES = [3, 5, 8, 16];
    let vopts = {...DEFAULT_VOPTS};

    const start = Date.now();

    for(let i = 0; i < BV_SIZES.length; ++i) {
        vopts.ISize = BV_SIZES[i];
        if(printprogress) {
            process.stderr.write(`    Checking small (${BV_SIZES[i]}) bit width...\n`);
        }

        try {
            const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
            if(masm === undefined) {
                if(printprogress) {
                    process.stderr.write(`    compile errors\n`);
                }
                return undefined;
            }
            else {    
                const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
                if(res === undefined) {
                    if(printprogress) {
                        process.stderr.write(`    payload generation errors\n`);
                    }
                    return undefined;
                }
    
                const cres = runVEvaluator(res, "check", bson);
                const jres = JSON.parse(cres);
                const rr = jres["result"];
                if(rr === "infeasible") {
                    if(printprogress) {
                        process.stderr.write(`    infeasible -- continuing checks...\n`);
                    }
                }
                else if(rr === "witness") {
                    const end = Date.now();
                    const witness = jres["input"];

                    //
                    //Witness may be infeasible for some reason (Float <-> Real approx), depends on NAT_MAX not being 2^64, etc.
                    //May want to try executing it here to validate -- if it fails then we can return undefined?
                    //

                    if (printprogress) {
                        process.stderr.write(`    witness\n`);
                    }

                    return {result: "witness", time: (end - start) / 1000, input: witness};
                }
                else if (rr === "timeout") {
                    if(printprogress) {
                        process.stderr.write(`    timeout -- moving on\n`);
                    }
                    
                    const end = Date.now();
                    return {result: "timeout", time: (end - start) / 1000};
                }
                else {
                    if(printprogress) {
                        process.stderr.write(`    error -- moving on\n`);
                    }
                    return undefined;
                }
            }
        } catch(e) {
            if(printprogress) {
                process.stderr.write(`    failure: ${e}\n`);
            }
            return undefined;
        }   
    }

    const end = Date.now();
    return {result: "infeasible", time: (end - start) / 1000};
}

function wfCheckLarge(bson: boolean, files: string[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    let vopts = {...DEFAULT_VOPTS};
    vopts.ISize = 64;

    const start = Date.now();

    if(printprogress) {
        process.stderr.write(`    Checking large (64) bit width...\n`);
    }

    try {
        const { masm } = generateMASM(files, entrypoint, vopts.SpecializeSmallModelGen);
        if (masm === undefined) {
            if (printprogress) {
                process.stderr.write(`    compile errors\n`);
            }
            return undefined;
        }
        else {
            const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
            if (res === undefined) {
                if (printprogress) {
                    process.stderr.write(`    payload generation errors\n`);
                }
                return undefined;
            }

            const cres = runVEvaluator(res, "check", bson);
            const jres = JSON.parse(cres);
            const rr = jres["result"];
            if (rr === "infeasible") {
                if (printprogress) {
                    process.stderr.write(`    infeasible\n`);
                }

                const end = Date.now();
                return {result: "infeasible", time: (end - start) / 1000};
            }
            else if (rr === "witness") {
                const end = Date.now();
                const witness = jres["input"];

                //
                //Witness may be infeasible for some reason (Float <-> Real approx), depends on NAT_MAX not being 2^64, etc.
                //May want to try executing it here to validate -- if it fails then we can return undefined?
                //

                if (printprogress) {
                    process.stderr.write(`    witness\n`);
                }

                return { result: "witness", time: (end - start) / 1000, input: witness };
            }
            else if (rr === "timeout") {
                if (printprogress) {
                    process.stderr.write(`    timeout -- moving on\n`);
                }
                return undefined;
            }
            else {
                if (printprogress) {
                    process.stderr.write(`    error -- moving on\n`);
                }
                return undefined;
            }
        }
    } catch (e) {
        if (printprogress) {
            process.stderr.write(`    failure: ${e}\n`);
        }
        return undefined;
    }
}

function workflowBSQCheck(bson: boolean, files: string[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: ChkWorkflowOutcome, time: number, input?: any} | undefined {
    if(printprogress) {
        process.stderr.write(`  Checking error at ${errorTrgtPos.file}@${errorTrgtPos.line}...\n`);
    }

    const start = Date.now();

    const smr = wfCheckSmall(bson, files, timeout, errorTrgtPos, entrypoint, printprogress);
    if(smr === undefined) {
        if(printprogress) {
            process.stderr.write(`  blocked on small model checking -- moving on :(\n`);
        }
        return undefined;
    }

    if(smr.result === "witness") {
        if(printprogress) {
            process.stderr.write(`  witness input generation successful (1b)!\n`);
        }
        const end = Date.now();
        return {result: "witness", time: (end - start) / 1000, input: smr.input};
    }

    const lmr = wfCheckLarge(bson, files, timeout, errorTrgtPos, entrypoint, printprogress);
    if(lmr === undefined) {
        if(printprogress) {
            process.stderr.write(`  blocked on large model checking -- no result :(\n`);
        }
        return undefined;
    }

    const end = Date.now();
    const elapsed = (end - start) / 1000;

    if(lmr.result === "infeasible") {
        if(printprogress) {
            process.stderr.write(`  infeasible on all inputs (1a)!\n`);
        }
        return {result: "infeasible", time: elapsed};
    }
    else {
        if(smr.result === "infeasible") {
            if(printprogress) {
                process.stderr.write(`  infeasible on restricted inputs (2a)!\n`);
            }
            return {result: "partial", time: elapsed};
        }
        else {
            if(printprogress) {
                process.stderr.write(`  exhastive exploration (2b)!\n`);
            }
            return {result: "exhaustive", time: elapsed};
        }
    }
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
    ChkWorkflowOutcome,
    DEFAULT_TIMEOUT, DEFAULT_VOPTS
};
