//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { exec, execSync } from "child_process";

import * as chalk from "chalk";

import { MIRAssembly, PackageConfig, SymbolicActionMode } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";

import { SMTEmitter } from "./smtdecls_emitter";
import { VerifierOptions } from "./smt_exp";
import { CodeFileInfo } from "../../ast/parser";
import { BuildApplicationMode, BuildLevel } from "../../ast/assembly";

const bosque_dir: string = Path.join(__dirname, "../../../");
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/checker/runtime/smtruntime.smt2");
const exepath = Path.join(bosque_dir, "/build/output/chk" + (process.platform === "win32" ? ".exe" : ""));

const smtruntime = FS.readFileSync(smtruntime_path).toString();

function generateStandardVOpts(mode: SymbolicActionMode): VerifierOptions {
    return {
        INT_MIN: -32768,
        INT_MAX: 32767,
        NAT_MAX: 65535,
        SLEN_MAX: 48,
        BLEN_MAX: 32,

        CONTAINER_MAX: 4,

        ActionMode: mode
    };
}

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            code.push({ srcpath: realpath, filename: Path.basename(files[i]), contents: FS.readFileSync(realpath).toString() });
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

function generateMASM(usercode: PackageConfig, buildlevel: BuildLevel, istestbuild: boolean, smallmodelonly: boolean, entrypointkey: MIRInvokeKey, entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];

    let smtmacros = ["CHECK_LIBS"];
    if(smallmodelonly) {
        smtmacros.push("CHK_SMALL_ONLY");
    }

    const coreconfig = new PackageConfig(smtmacros, corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.ModelChecker, [coreconfig, usercode], buildlevel, istestbuild, [entrypointkey], entrypoint);
}

function generateSMTPayload(masm: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): string | undefined {
    try {
        return SMTEmitter.generateSMTPayload(masm, istestbuild, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        process.stderr.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function generateSMTPayloadForISCFuzzing(masm: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): [string | undefined, string[]] {
    try {
        return SMTEmitter.generateSMTPayloadForISCFuzzing(masm, istestbuild, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        process.stderr.write(chalk.red(`SMT generate error -- ${e}\n`));
        return [undefined, []];
    }
}

function generateCheckerPayload(masm: MIRAssembly, istestbuild: boolean, smtasm: string, timeout: number, entrypoint: MIRInvokeKey): any {
    return {smt2decl: smtasm, timeout: timeout, apimodule: masm.emitAPIInfo([entrypoint], istestbuild), "mainfunc": entrypoint};
}

function runVEvaluatorAsync(cpayload: object, mode: SymbolicActionMode, cb: (result: string) => void) {
    let workflow = "missing";
    if(mode === SymbolicActionMode.ErrTestSymbolic) {
        workflow = "errorchk";
    }
    else if(mode === SymbolicActionMode.ChkTestSymbolic) {
        workflow = "passchk";
    }
    else if(mode === SymbolicActionMode.InputFuzzSymbolic) {
        workflow = "fuzz";
    }
    else {
        workflow = "eval";
    }

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

        if(proc.stdin === null) {
            proc.kill();
            cb(JSON.stringify({result: "error", info: "Killed process!!!"}));
        }
        else {
            proc.stdin.on("error", (err: Error) => { cb(JSON.stringify({result: "error", info: `Write to stdin error -- ${err}`})); });

            proc.stdin.setDefaultEncoding('utf-8');
            proc.stdin.write(JSON.stringify(cpayload, undefined, 2));
            proc.stdin.write("\n");
            proc.stdin.end();
        }
    }
    catch(ex) {
        cb(JSON.stringify({result: "error", info: `${ex}`}));
    }
}

function runVEvaluatorRandFuzz(cpayload: object, seed: number): any | undefined{
    try {
        const cmd = `${exepath} --fuzz`;
        const env = {...process.env, SMT_TEST_GEN_RAND_SEED: seed.toString()};
        const fval = execSync(cmd, {input: JSON.stringify(cpayload, undefined, 2), encoding: "utf-8", env: env}).toString();
            
        return JSON.parse(fval);
    }
    catch(ex) {
        //const ff = (cpayload as any).smt2decl;
        //FS.writeFileSync("c:\\Users\\marron\\Desktop\\scratch.smt2", ff);
        process.stdout.write(chalk.red(`SMT generate error -- ${ex}\n`));
        return undefined;
    }
}

function workflowGetErrors(usercode: PackageConfig, buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}): { file: string, line: number, pos: number, msg: string }[] | undefined {
    try {
        const { masm, errors } = generateMASM(usercode, buildlevel, istestbuild, smallmodelonly, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2) + "\n");
            return undefined;
        }
        else {
            return SMTEmitter.generateSMTAssemblyAllErrors(masm, istestbuild, vopts, entrypoint.name);
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        return undefined;
    }
}

function workflowEmitToFile(into: string, usercode: PackageConfig, buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, timeout: number, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, errorTrgtPos: { file: string, line: number, pos: number }, smtonly: boolean) {
    try {
        const { masm, errors } = generateMASM(usercode, buildlevel, istestbuild, smallmodelonly, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            process.stderr.write(chalk.red(`Compiler Errors!\n`));
            process.stderr.write(JSON.stringify(errors, undefined, 2) + "\n");
            process.exit(1);
        }
        else {
            const smtcode = generateSMTPayload(masm, istestbuild, vopts, errorTrgtPos, entrypoint.fkey);
            if(smtcode !== undefined) {
                if(smtonly) {
                    FS.writeFileSync(into, smtcode);
                }
                else {
                    const payload = generateCheckerPayload(masm, istestbuild, smtcode, timeout, entrypoint.fkey);
                    FS.writeFileSync(into, JSON.stringify(payload, undefined, 2));
                }
            }
        }
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function workflowErrorCheckSingle(usercode: PackageConfig, buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, timeout: number, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, errorTrgtPos: { file: string, line: number, pos: number }, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, buildlevel, istestbuild, smallmodelonly, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const smtcode = generateSMTPayload(masm, istestbuild, vopts, errorTrgtPos, entrypoint.fkey);
            if(smtcode === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            const payload = generateCheckerPayload(masm, istestbuild, smtcode, timeout, entrypoint.fkey);
            runVEvaluatorAsync(payload, SymbolicActionMode.ErrTestSymbolic, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowPassCheck(usercode: PackageConfig, buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, timeout: number, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, buildlevel, istestbuild, smallmodelonly, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const smtcode = generateSMTPayload(masm, istestbuild, vopts, { file: "[NO TARGET]", line: -1, pos: -1 }, entrypoint.fkey);
            if(smtcode === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            const payload = generateCheckerPayload(masm, istestbuild, smtcode, timeout, entrypoint.fkey);
            runVEvaluatorAsync(payload, SymbolicActionMode.ChkTestSymbolic, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowEvaluate(usercode: PackageConfig, buildlevel: BuildLevel, istestbuild: boolean, timeout: number, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, jin: any[], cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, buildlevel, istestbuild, false, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const smtcode = generateSMTPayload(masm, istestbuild, vopts, { file: "[NO TARGET]", line: -1, pos: -1 }, entrypoint.fkey)
            if(smtcode === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            const payload = generateCheckerPayload(masm, istestbuild, smtcode, timeout, entrypoint.fkey);
            runVEvaluatorAsync({...payload, jin: jin}, SymbolicActionMode.EvaluateSymbolic, cb);
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

function workflowInputFuzz(usercode: PackageConfig, buildlevel: BuildLevel, istestbuild: boolean, timeout: number, vopts: VerifierOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, cbinfo: (sstr: string) => void, cb: (result: string) => void) {
    try {
        const { masm } = generateMASM(usercode, buildlevel, istestbuild, false, entrypoint.fkey, {filename: entrypoint.filename, names: [entrypoint.name]});
        if(masm === undefined) {
            cb(JSON.stringify({result: "error", info: "compile errors"}));
        }
        else {
            const [smtcode, iscopts] = generateSMTPayloadForISCFuzzing(masm, istestbuild, vopts, { file: "[NO TARGET]", line: -1, pos: -1 }, entrypoint.fkey)
            if(smtcode === undefined) {
                cb(JSON.stringify({result: "error", info: "payload generation error"}));
                return;
            }

            cbinfo(`Generating ${iscopts.length} input fuzzing options...`);

            let testopts: any[] = [];
            for(let i = 0; i < iscopts.length; ++i) {
                const payload = generateCheckerPayload(masm, istestbuild, smtcode + iscopts[i], timeout, entrypoint.fkey);

                const jres = runVEvaluatorRandFuzz(payload, i);
                if(jres == undefined) {
                    cbinfo(`Payload ${i} generation error`);
                }

                if(jres.status === "input") {
                    cbinfo(`Test generated for payload ${i} in ${jres.time}ms`);
                }
                else if(jres.status === "unknown") {
                    cbinfo(`Payload ${i} has unknown satisfiability -- ${jres.info}`);
                }
                else {
                    //cbinfo(`No valid input for Payload ${i} -- ${jres.info}`);
                }

                testopts.push(jres);
            }

            cb(JSON.stringify({result: "input", info: testopts}));
        }
    } catch(e) {
        cb(JSON.stringify({result: "error", info: `${e}`}));
    }
}

export {
    generateStandardVOpts,
    workflowLoadUserSrc, workflowGetErrors, workflowEmitToFile, 
    workflowErrorCheckSingle, workflowPassCheck, workflowEvaluate, workflowInputFuzz
};
