//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { exec, execSync } from "child_process";

import chalk from "chalk";

import { MIRAssembly, PackageConfig } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../compiler/mir_ops";

import { Payload, SMTEmitter } from "./smtdecls_emitter";
import { VerifierOptions } from "./smt_exp";
import { CodeFileInfo } from "../../ast/parser";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../"));
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
const exepath = Path.normalize(Path.join(bosque_dir, "/build/output/chkworkflow" + (process.platform === "win32" ? ".exe" : "")));

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

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            code.push({ fpath: realpath, contents: FS.readFileSync(realpath).toString() });
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = Path.join(bosque_dir, "bin/core/verify");
        const corefiles = FS.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
            code.push({ fpath: cfpath, contents: FS.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

function generateMASM(usercode: CodeFileInfo[], entrypoint: string, dosmallopts: boolean): { masm: MIRAssembly | undefined, errors: string[] } {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const code = [...corecode, ...usercode];

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

function runVEvaluator(cpayload: object, workflow: "check" | "eval" | "invert", bson: boolean): string {
    try {
        const cmd = `${exepath}${bson ? " --bsqon" : ""} --${workflow}`;
        return execSync(cmd, { input: JSON.stringify(cpayload, undefined, 2) }).toString().trim();
    }
    catch(ex) {
        return JSON.stringify({result: "error", info: `${ex}`});
    }
}

function runVEvaluatorAsync(cpayload: object, workflow: "check" | "eval" | "invert", bson: boolean, cb: (result: string) => void) {
    try {
        const cmd = `${exepath}${bson ? " --bsqon" : ""} --${workflow}`;
        const proc = exec(cmd, (err, stdout, stderr) => {
            cb(stdout.toString().trim());
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(cpayload, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end();
    }
    catch(ex) {
        cb(JSON.stringify({result: "error", info: `${ex}`}));
    }
}

function workflowGetErrors(usercode: CodeFileInfo[], vopts: VerifierOptions, entrypoint: MIRInvokeKey): { file: string, line: number, pos: number, msg: string }[] | undefined {
    try {
        const { masm, errors } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
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

function workflowEmitToFile(into: string, usercode: CodeFileInfo[], mode: "check" | "evaluate" | "invert", timeout: number, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, smtonly: boolean) {
    try {
        const { masm, errors } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2));
            process.exit(1);
        }
        else {    
            const res = generateSMTPayload(masm, mode, timeout, vopts, errorTrgtPos, entrypoint);
            if(res !== undefined) {
                FS.writeFileSync(into, smtonly ? res.smt2decl : JSON.stringify(res, undefined, 2));
            }
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function workflowBSQSingle(bson: boolean, usercode: CodeFileInfo[], vopts: VerifierOptions, timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {    
            const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync(res, "check", bson, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function wfCheckSmall(bson: boolean, usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    //
    //TODO: should compute min viable BV size here
    //
    const BV_SIZES = [5, 8, 16];
    let vopts = {...DEFAULT_VOPTS};

    const start = Date.now();

    for(let i = 0; i < BV_SIZES.length; ++i) {
        vopts.ISize = BV_SIZES[i];
        if(printprogress) {
            process.stderr.write(`    Checking small (${BV_SIZES[i]}) bit width...\n`);
        }

        try {
            const { masm } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
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

function wfCheckLarge(bson: boolean, usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    let vopts = {...DEFAULT_VOPTS};
    vopts.ISize = 64;

    const start = Date.now();

    if(printprogress) {
        process.stderr.write(`    Checking large (64) bit width...\n`);
    }

    try {
        const { masm } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
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

function workflowBSQCheck(bson: boolean, usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: ChkWorkflowOutcome, time: number, input?: any} | undefined {
    if(printprogress) {
        process.stderr.write(`  Checking error at ${errorTrgtPos.file}@${errorTrgtPos.line}...\n`);
    }

    const start = Date.now();

    const smr = wfCheckSmall(bson, usercode, timeout, errorTrgtPos, entrypoint, printprogress);
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

    const lmr = wfCheckLarge(bson, usercode, timeout, errorTrgtPos, entrypoint, printprogress);
    if(lmr === undefined) {
        if(printprogress) {
            process.stderr.write(`  blocked on large model checking -- no result :(\n`);
        }
        return undefined;
    }

    const end = Date.now();
    const elapsed = (end - start) / 1000;

    if(lmr.result === "witness") {
        if(printprogress) {
            process.stderr.write(`  witness input generation successful (1b)!\n`);
        }
        const end = Date.now();
        return {result: "witness", time: (end - start) / 1000, input: lmr.input};
    }
    else if(lmr.result === "infeasible") {
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

function workflowEvaluateSingle(bson: boolean, usercode: CodeFileInfo[], jin: any[], vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {    
            const res = generateSMTPayload(masm, "evaluate", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync({...res, jin: jin}, "eval", bson, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowInvertSingle(bson: boolean, usercode: CodeFileInfo[], jout: any, vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, vopts.SpecializeSmallModelGen);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {    
            const res = generateSMTPayload(masm, "invert", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync({...res, jout: jout}, "invert", bson, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

export {
    workflowLoadUserSrc,
    workflowGetErrors, workflowEmitToFile, workflowBSQSingle, workflowBSQCheck, workflowEvaluateSingle, workflowInvertSingle,
    ChkWorkflowOutcome,
    DEFAULT_TIMEOUT, DEFAULT_VOPTS
};
