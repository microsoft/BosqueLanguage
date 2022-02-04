//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { exec, execSync } from "child_process";

import chalk from "chalk";

import { MIRAssembly, MIRObjectEntityTypeDecl, PackageConfig, SymbolicActionMode } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../compiler/mir_ops";

import { SMTEmitter } from "./smtdecls_emitter";
import { VerifierOptions } from "./smt_exp";
import { CodeFileInfo } from "../../ast/parser";
import { BuildApplicationMode } from "../../ast/assembly";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../"));
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
const exepath = Path.normalize(Path.join(bosque_dir, "/build/output/chkworkflow" + (process.platform === "win32" ? ".exe" : "")));

const smtruntime = FS.readFileSync(smtruntime_path).toString();

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            code.push({ srcpath: realpath, filename: files[i], contents: FS.readFileSync(realpath).toString() });
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

        const coredir = Path.join(bosque_dir, "bin/core");
        const corefiles = FS.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: FS.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

function generateMASM(usercode: PackageConfig, entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["CHECK_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.ModelChecker, [coreconfig, usercode], "debug", entrypoint);
}

function generateSMTPayload(masm: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): any {
    try {
        return SMTEmitter.generateSMTPayload(masm, false, smtruntime, vopts, errorTrgtPos, "__i__" + entrypoint);
    } catch(e) {
        process.stderr.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function runVEvaluator(cpayload: object, mode: SymbolicActionMode): string {
    try {
        const cmd = `${exepath} --${workflow}`;
        return execSync(cmd, { input: JSON.stringify(cpayload, undefined, 2) }).toString().trim();
    }
    catch(ex) {
        return JSON.stringify({result: "error", info: `${ex}`});
    }
}

function runVEvaluatorAsync(cpayload: object, workflow: "unreachable" | "witness" | "eval" | "invert", cb: (result: string) => void) {
    try {
        const cmd = `${exepath} --${workflow}`;
        const proc = exec(cmd, (err, stdout, stderr) => {
            if(err) {
                cb(JSON.stringify({result: "error", info: `${err}`}));
            }
            else {
                cb(stdout.toString().trim());
            }
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
        const { masm, errors } = generateMASM(usercode, entrypoint, AssemblyFlavor.UFOverApproximate, vopts.EnableCollection_SmallOps);
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2) + "\n");
            return undefined;
        }
        else {
            const simplenumgen = BVEmitter.create(BigInt(vopts.ISize));
            const hashgen = BVEmitter.create(BigInt(512));
            return SMTEmitter.generateSMTAssemblyAllErrors(masm, vopts, { int: simplenumgen, hash: hashgen}, "__i__" + entrypoint);
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function workflowEmitToFile(into: string, usercode: CodeFileInfo[], asmflavor: AssemblyFlavor, mode: "unreachable" | "witness" | "evaluate" | "invert", timeout: number, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, smtonly: boolean) {
    try {
        const { masm, errors } = generateMASM(usercode, entrypoint, asmflavor, vopts.EnableCollection_SmallOps);
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2) + "\n");
            process.exit(1);
        }
        else {
            const numgen = computeNumGen(masm, vopts.ISize);
            const hashgen = BVEmitter.create(BigInt(16));
            if(numgen === undefined) {
                process.stderr.write(chalk.red(`Constants larger than specified bitvector size (${vopts.ISize})!\n`));
                process.exit(1);
            }

            const res = generateSMTPayload(masm, mode, timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
            if(res !== undefined) {
                FS.writeFileSync(into, smtonly ? res.smt2decl : JSON.stringify(res, undefined, 2));
            }
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function workflowBSQInfeasibleSingle(usercode: CodeFileInfo[], vopts: VerifierOptions, timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.UFOverApproximate, vopts.EnableCollection_SmallOps);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const numgen = computeNumGen(masm, vopts.ISize);
            const hashgen = BVEmitter.create(BigInt(16));
            if(numgen === undefined) {
                cb(JSON.stringify({result: "error", info: `constants larger than specified bitvector size (${vopts.ISize})`}));
                return;
            }
            
            const res = generateSMTPayload(masm, "unreachable", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync(res, "unreachable", cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowBSQWitnessSingle(usercode: CodeFileInfo[], vopts: VerifierOptions, timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.RecuriveImpl, vopts.EnableCollection_SmallOps);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const numgen = computeNumGen(masm, vopts.ISize);
            const hashgen = BVEmitter.create(BigInt(16));
            if(numgen === undefined) {
                cb(JSON.stringify({result: "error", info: `constants larger than specified bitvector size (${vopts.ISize})`}));
                return;
            }

            const res = generateSMTPayload(masm, "witness", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync(res, "witness", cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function wfInfeasibleSmall(usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean, smallopsonly: boolean): {result: CheckerResult, time: number} | undefined {
    const SMALL_MODEL = smallopsonly 
    ? [
        { EnableCollection_SmallHavoc: true, EnableCollection_LargeHavoc: false, EnableCollection_SmallOps: true, EnableCollection_LargeOps: false, StringOpt: "ASCII" } 
    ]
    : [
        { EnableCollection_SmallHavoc: true, EnableCollection_LargeHavoc: false, EnableCollection_SmallOps: true, EnableCollection_LargeOps: true, StringOpt: "ASCII" },
        { EnableCollection_SmallHavoc: false, EnableCollection_LargeHavoc: true, EnableCollection_SmallOps: true, EnableCollection_LargeOps: true, StringOpt: "ASCII" },
    ];

    const BV_SIZES = [
        4,
        8, 
        16
    ];

    const start = Date.now();

    for(let i = 0; i < BV_SIZES.length; ++i) {
        if(printprogress) {
            process.stderr.write(`    Checking small (${BV_SIZES[i]}) bit width unreachability...\n`);
        }

        try {
            const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.UFOverApproximate, true /*EnableCollection_SmallOps always true*/);
            if(masm === undefined) {
                if(printprogress) {
                    process.stderr.write(`    compile errors\n`);
                }
                return undefined;
            }
            else {
                const numgen = computeNumGen(masm, BV_SIZES[i]);
                const hashgen = BVEmitter.create(BigInt(16));
                if(numgen === undefined) {
                    if(printprogress) {
                        process.stderr.write(`    constants larger than specified bitvector size -- continuing checks...\n`);
                    }
                }
                else {
                    for (let j = 0; j < SMALL_MODEL.length; ++j) {
                        const vopts = { ISize: BV_SIZES[i], ...SMALL_MODEL[j] } as VerifierOptions;
                        if(printprogress) {
                            process.stderr.write(`      Checking *${vopts.EnableCollection_LargeHavoc ? "mixed" : "small"}* inputs with *${vopts.EnableCollection_LargeOps ? "mixed" : "small"}* operations...\n`);
                        }

                        const res = generateSMTPayload(masm, "unreachable", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
                        if (res === undefined) {
                            if (printprogress) {
                                process.stderr.write(`      payload generation errors\n`);
                            }
                            return undefined;
                        }

                        const cres = runVEvaluator(res, "unreachable");
                        const jres = JSON.parse(cres);
                        const rr = jres["result"];
                        if (rr === "unreachable") {
                            if (printprogress) {
                                process.stderr.write(`      unreachable -- continuing checks...\n`);
                            }
                        }
                        else if (rr === "possible") {
                            if (printprogress) {
                                process.stderr.write(`      possible -- moving on\n`);
                            }

                            const end = Date.now();
                            return { result: "possible", time: (end - start) / 1000 };
                        }
                        else if (rr === "timeout") {
                            if (printprogress) {
                                process.stderr.write(`      timeout -- moving on\n`);
                            }

                            const end = Date.now();
                            return { result: "timeout", time: (end - start) / 1000 };
                        }
                        else {
                            if (printprogress) {
                                process.stderr.write(`      error -- moving on\n`);
                            }
                            return undefined;
                        }
                    }
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
    return {result: "unreachable", time: (end - start) / 1000};
}

function wfWitnessSmall(usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean, smallopsonly: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    const SMALL_MODEL = smallopsonly 
    ? [
        { EnableCollection_SmallHavoc: true, EnableCollection_LargeHavoc: false, EnableCollection_SmallOps: true, EnableCollection_LargeOps: false, StringOpt: "ASCII" }
    ]
    : [
        { EnableCollection_SmallHavoc: true, EnableCollection_LargeHavoc: false, EnableCollection_SmallOps: true, EnableCollection_LargeOps: true, StringOpt: "ASCII" },
        { EnableCollection_SmallHavoc: false, EnableCollection_LargeHavoc: true, EnableCollection_SmallOps: true, EnableCollection_LargeOps: true, StringOpt: "ASCII" },
    ];

    const BV_SIZES = [
        3,
        5, 
        8, 
        12, 
        16
    ];

    const start = Date.now();

    for(let i = 0; i < BV_SIZES.length; ++i) {
        if(printprogress) {
            process.stderr.write(`    Looking for small (${BV_SIZES[i]}) bit width witnesses...\n`);
        }

        try {
            const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.UFOverApproximate, true /*EnableCollection_SmallOps always true*/);
            if(masm === undefined) {
                if(printprogress) {
                    process.stderr.write(`    compile errors\n`);
                }
                return undefined;
            }
            else {
                const numgen = computeNumGen(masm, BV_SIZES[i]);
                const hashgen = BVEmitter.create(BigInt(16));
                if(numgen === undefined) {
                    if(printprogress) {
                        process.stderr.write(`    constants larger than specified bitvector size -- continuing checks...\n`);
                    }
                }
                else {
                    for (let j = 0; j < SMALL_MODEL.length; ++j) {
                        const vopts = { ISize: BV_SIZES[i], ...SMALL_MODEL[j] } as VerifierOptions;
                        if(printprogress) {
                            process.stderr.write(`      Checking *${vopts.EnableCollection_LargeHavoc ? "mixed" : "small"}* inputs with *${vopts.EnableCollection_LargeOps ? "mixed" : "small"}* operations...\n`);
                        }

                        const res = generateSMTPayload(masm, "witness", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
                        if (res === undefined) {
                            if (printprogress) {
                                process.stderr.write(`      payload generation errors\n`);
                            }
                            return undefined;
                        }

                        const cres = runVEvaluator(res, "witness");
                        const jres = JSON.parse(cres);
                        const rr = jres["result"];
                        if (rr === "unreachable") {
                            if (printprogress) {
                                process.stderr.write(`      unreachable -- continuing checks...\n`);
                            }
                        }
                        else if (rr === "witness") {
                            const end = Date.now();
                            const witness = jres["input"];

                            //
                            //Witness may be unreachable for some reason (Float <-> Real approx), depends on NAT_MAX not being 2^64, etc.
                            //May want to try executing it here to validate -- if it fails then we can return undefined?
                            //

                            if (printprogress) {
                                process.stderr.write(`      witness\n`);
                            }

                            return { result: "witness", time: (end - start) / 1000, input: witness };
                        }
                        else if (rr === "timeout") {
                            if (printprogress) {
                                process.stderr.write(`      timeout -- moving on\n`);
                            }

                            const end = Date.now();
                            return { result: "timeout", time: (end - start) / 1000 };
                        }
                        else {
                            if (printprogress) {
                                process.stderr.write(`      error -- moving on\n`);
                            }
                            return undefined;
                        }
                    }
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
    return {result: "unreachable", time: (end - start) / 1000};
}

function wfInfeasibleLarge(usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number} | undefined {
    const start = Date.now();

    const vopts = {
        ISize: 64,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: false,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    if(printprogress) {
        process.stderr.write(`    Checking full (${64}) bit width uneachability...\n`);
    }

    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.UFOverApproximate, vopts.EnableCollection_SmallOps);
        if (masm === undefined) {
            if (printprogress) {
                process.stderr.write(`    compile errors\n`);
            }
            return undefined;
        }
        else {
            const numgen = BVEmitter.create(BigInt(64));
            const hashgen = BVEmitter.create(BigInt(512));

            const res = generateSMTPayload(masm, "unreachable", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
            if (res === undefined) {
                if (printprogress) {
                    process.stderr.write(`    payload generation errors\n`);
                }
                return undefined;
            }

            const cres = runVEvaluator(res, "unreachable");
            const jres = JSON.parse(cres);
            const rr = jres["result"];
            if (rr === "unreachable") {
                if (printprogress) {
                    process.stderr.write(`    unreachable\n`);
                }

                const end = Date.now();
                return { result: "unreachable", time: (end - start) / 1000 };
            }
            else if (rr === "possible") {
                if (printprogress) {
                    process.stderr.write(`    possible\n`);
                }

                const end = Date.now();
                return { result: "possible", time: (end - start) / 1000 };
            }
            else if (rr === "timeout") {
                if (printprogress) {
                    process.stderr.write(`    timeout\n`);
                }

                const end = Date.now();
                return { result: "timeout", time: (end - start) / 1000 };
            }
            else {
                if (printprogress) {
                    process.stderr.write(`    error\n`);
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

function wfWitnessLarge(usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: CheckerResult, time: number, input?: any} | undefined {
    const start = Date.now();

    const vopts = {
        ISize: 64,
        StringOpt: "ASCII",
        EnableCollection_SmallHavoc: true,
        EnableCollection_LargeHavoc: true,
        EnableCollection_SmallOps: true,
        EnableCollection_LargeOps: true
    } as VerifierOptions;

    if(printprogress) {
        process.stderr.write(`    Looking for full (${64}) bit width witness...\n`);
    }

    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.RecuriveImpl, vopts.EnableCollection_SmallOps);
        if (masm === undefined) {
            if (printprogress) {
                process.stderr.write(`    compile errors\n`);
            }
            return undefined;
        }
        else {
            const numgen = BVEmitter.create(BigInt(64));
            const hashgen = BVEmitter.create(BigInt(512));

            const res = generateSMTPayload(masm, "witness", timeout, {int: numgen, hash: hashgen}, vopts, errorTrgtPos, entrypoint);
            if (res === undefined) {
                if (printprogress) {
                    process.stderr.write(`    payload generation errors\n`);
                }
                return undefined;
            }

            const cres = runVEvaluator(res, "witness");
            const jres = JSON.parse(cres);
            const rr = jres["result"];
            if (rr === "unreachable") {
                if (printprogress) {
                    process.stderr.write(`    unreachable\n`);
                }

                const end = Date.now();
                return { result: "unreachable", time: (end - start) / 1000 };
            }
            else if (rr === "witness") {
                const end = Date.now();
                const witness = jres["input"];

                //
                //Witness may be unreachable for some reason (Float <-> Real approx), depends on NAT_MAX not being 2^64, etc.
                //May want to try executing it here to validate -- if it fails then we can return undefined?
                //

                if (printprogress) {
                    process.stderr.write(`    witness\n`);
                }

                return { result: "witness", time: (end - start) / 1000, input: witness };
            }
            else if (rr === "timeout") {
                if (printprogress) {
                    process.stderr.write(`    timeout\n`);
                }

                const end = Date.now();
                return { result: "timeout", time: (end - start) / 1000 };
            }
            else {
                if (printprogress) {
                    process.stderr.write(`    error\n`);
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

function workflowBSQCheck(usercode: CodeFileInfo[], timeout: number, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, printprogress: boolean): {result: ChkWorkflowOutcome, time: number, input?: any} | undefined {
    if(printprogress) {
        process.stderr.write(`  Checking error at ${errorTrgtPos.file}@${errorTrgtPos.line}...\n`);
    }

    const start = Date.now();

    const smis = wfInfeasibleSmall(usercode, timeout, errorTrgtPos, entrypoint, printprogress, true);
    const smil = wfInfeasibleSmall(usercode, timeout, errorTrgtPos, entrypoint, printprogress, false);
    if(smis === undefined || smil === undefined) {
        if(printprogress) {
            process.stderr.write(`  blocked on small model unreachability -- moving on :(\n`);
        }
        return undefined;
    }

    let nosmallerror = false;
    let nolimitederror = false;
    if (smis.result !== "unreachable" || smil.result !== "unreachable") {
        const smws = wfWitnessSmall(usercode, timeout, errorTrgtPos, entrypoint, printprogress, true);
        nosmallerror = smws !== undefined && smws.result === "unreachable";

        if (smws !== undefined && smws.result === "witness") {
            if (printprogress) {
                process.stderr.write(`  witness input generation successful (1b)!\n`);
            }
            const end = Date.now();
            return { result: "witness", time: (end - start) / 1000, input: smws.input };
        }

        const smwl = wfWitnessSmall(usercode, timeout, errorTrgtPos, entrypoint, printprogress, false);
        nolimitederror = smwl !== undefined && smwl.result === "unreachable";

        if (smwl !== undefined && smwl.result === "witness") {
            if (printprogress) {
                process.stderr.write(`  witness input generation successful (1b)!\n`);
            }
            const end = Date.now();
            return { result: "witness", time: (end - start) / 1000, input: smwl.input };
        }
    }

    const lmr = wfInfeasibleLarge(usercode, timeout, errorTrgtPos, entrypoint, printprogress);
    if(lmr !== undefined && lmr.result === "unreachable") {
        if(printprogress) {
            process.stderr.write(`  unreachable on all inputs (1a)!\n`);
        }
        const end = Date.now();
        return {result: "unreachable", time: (end - start) / 1000};
    }
    
    let lmw = wfWitnessLarge(usercode, timeout, errorTrgtPos, entrypoint, printprogress);
    if(lmw !== undefined && lmw.result === "witness") {
        if(printprogress) {
            process.stderr.write(`  witness input generation successful (1b)!\n`);
        }
        const end = Date.now();
        return {result: "witness", time: (end - start) / 1000, input: lmw.input};
    }

    const end = Date.now();
    const elapsed = (end - start) / 1000;

    if (smis.result === "unreachable" || smil.result === "unreachable") {
        if (printprogress) {
            process.stderr.write(`  unreachable on ${smis.result === "unreachable" ? "small" : "restricted"} inputs (2a)!\n`);
        }
        return { result: "partial", time: elapsed };
    }
    else if(nosmallerror || nolimitederror) {
        if (printprogress) {
            process.stderr.write(`  unreachable on ${!nolimitederror ? "small" : "restricted"} inputs (2a)!\n`);
        }
        return { result: "nosmall", time: elapsed };
    }
    else {
        if (printprogress) {
            process.stderr.write(`  exhastive exploration (2b)!\n`);
        }
        return { result: "exhaustive", time: elapsed };
    }
}

function workflowEvaluateSingle(usercode: CodeFileInfo[], jin: any[], vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.RecuriveImpl, true);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const numgen = computeNumGen(masm, vopts.ISize);
            const hashgen = BVEmitter.create(BigInt(16));
            if(numgen === undefined) {
                cb(JSON.stringify({result: "error", info: `constants larger than specified bitvector size (${vopts.ISize})`}));
                return;
            }

            const res = generateSMTPayload(masm, "evaluate", timeout, {int: numgen, hash: hashgen}, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync({...res, jin: jin}, "eval", cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowInvertSingle(usercode: CodeFileInfo[], jout: any, vopts: VerifierOptions, timeout: number, entrypoint: MIRInvokeKey, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, entrypoint, AssemblyFlavor.RecuriveImpl, true);
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const numgen = computeNumGen(masm, vopts.ISize);
            const hashgen = BVEmitter.create(BigInt(16));
            if(numgen === undefined) {
                cb(JSON.stringify({result: "error", info: `constants larger than specified bitvector size (${vopts.ISize})`}));
                return;
            }

            const res = generateSMTPayload(masm, "invert", timeout, {int: numgen, hash: hashgen}, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
            if(res === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            runVEvaluatorAsync({...res, jout: jout}, "invert", cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

export {
    workflowLoadUserSrc,
    workflowGetErrors, workflowEmitToFile, workflowBSQInfeasibleSingle, workflowBSQWitnessSingle, workflowBSQCheck, workflowEvaluateSingle, workflowInvertSingle,
    ChkWorkflowOutcome,
    AssemblyFlavor, DEFAULT_TIMEOUT
};
