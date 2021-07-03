//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import * as Commander from "commander";
import chalk from "chalk";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { SMTAssembly } from "../tooling/verifier/smt_assembly";
import { Payload, SMTEmitter } from "../tooling/verifier/smtdecls_emitter";
import { VerifierOptions } from "../tooling/verifier/smt_exp";
import { MIRInvokeKey } from "../compiler/mir_ops";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const smtlib_path = Path.join(bosque_dir, "bin/core/verify");
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
const exepath = Path.normalize(Path.join(bosque_dir, "/build/out/chkworkflow" + (process.platform === "win32" ? ".exe" : "")));

const timeout = 5000;
const smtruntime = FS.readFileSync(smtruntime_path).toString();

const vopts = {
    ISize: 5,
    BigXMode: "Int",
    OverflowEnabled: false,
    FPOpt: "Real",
    StringOpt: "ASCII",
    SimpleQuantifierMode: false,
    SpecializeSmallModelGen: false
} as VerifierOptions;

function generateMASM(files: string[], entrypoint: string, dosmallopts: boolean): MIRAssembly {
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
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
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
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", macros, {namespace: namespace, names: [entryfunc]}, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function generateSMTPayload(masm: MIRAssembly, mode: "check" | "evaluate" | "invert", timeout: number, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): Payload {
    try {
        return SMTEmitter.generateSMTPayload(masm, mode, timeout, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function emitSMT2File(cfile: string, into: string) {
    try {
        process.stdout.write(`Writing SMT output to "${into}..."\n`)
        FS.writeFileSync(Commander.output, cfile);
    }
    catch (fex) {
        process.stderr.write(chalk.red(`Failed to write file -- ${fex}\n`));
    }
}

function runVEvaluator(cpayload: Payload, workflow: "check" | "eval" | "invert", bson: boolean): string {
    try {
        return execSync(`${exepath} ${bson ? " --bson" : ""} --${workflow}`, { input: JSON.stringify(cpayload) }).toString().trim();
    }
    catch(ex) {
        return JSON.stringify({result: "error", info: `${ex}`});
    }
}

function workflowGetErrors(masm: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey) {
    try {
        const allErrors = SMTEmitter.generateSMTAssemblyAllErrors(masm, vopts, entrypoint);
        process.stdout.write("Possible error lines:\n")
        process.stdout.write(JSON.stringify(allErrors, undefined, 2) + "\n")
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
}

function workflowEmitToFile(into: string, masm: MIRAssembly, mode: "check" | "evaluate" | "invert", vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey) {
    const res = generateSMTPayload(masm, mode, timeout, vopts, errorTrgtPos, entrypoint);
    emitSMT2File(res.smt2decl, into)
}

function workflowBSQSingle(bson: boolean, masm: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey) {
    const res = generateSMTPayload(masm, "check", timeout, vopts, errorTrgtPos, entrypoint);
    const veval = runVEvaluator(res, "check", bson);
    
    process.stdout.write(veval);
}

function workflowBSQCheck() {
    
}

function workflowEvaluateSingle(bson: boolean, masm: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey) {
    const res = generateSMTPayload(masm, "check", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
    const veval = runVEvaluator(res, "check", bson);
    
    process.stdout.write(veval);
}

function workflowInvertSingle(bson: boolean, masm: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey) {
    const res = generateSMTPayload(masm, "check", timeout, vopts, { file: "[NO FILE]", line: -1, pos: -1 }, entrypoint);
    const veval = runVEvaluator(res, "check", bson);
    
    process.stdout.write(veval);
}

Commander
    .option("-l --location [location]", "Location (file.bsq@line#pos) with error of interest")
    .option("-e --entrypoint [entrypoint]", "Entrypoint to symbolically test", "NSMain::main")
    .option("-m --mode [mode]", "Mode to run (errorlocs | refute | generate)", "refute")
    .option("-s --small", "Enable small model optimizations in generate mode")
    .option("-o --output [file]", "Output the model to a given file")
    .option("-p --prover [prover]", "Prover to use (z3 | cvc4)", "z3");

Commander.parse(process.argv);



if (Commander.args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file and target line as arguments\n"));
    process.exit(1);
}

if(Commander.mode !== "errorlocs" && Commander.mode !== "refute" && Commander.mode !== "generate") {
    process.stdout.write(chalk.red("Error -- Valid modes are \"errorlocs\", \"refute\", and \"generate\"\n"));
    process.exit(1);
}

process.stdout.write(`Processing Bosque sources in:\n${Commander.args.join("\n")}\n...Using entrypoint ${Commander.entrypoint}...\n`);
const massembly = generateMASM(Commander.args, Commander.entrypoint, Commander.small !== undefined);

if(Commander.mode === "errorlocs" || Commander.location === undefined) {
    const sasm = generateSMTAssemblyForValidate(massembly, vopts, Commander.entrypoint, {file: "[]", line: -1, pos: -1});
    if(sasm !== undefined) {
        process.stdout.write("Possible error lines:\n")
        process.stdout.write(JSON.stringify(sasm.allErrors, undefined, 2) + "\n")

        if (Commander.output) {
            const smfc = buildSMT2file(sasm, timeout, "Refute");
            emitSMT2File(smfc, Commander.output);
        }
    }
    process.exit(0);
}

let errlocation = { file: "[]", line: -1, pos: -1 };
if (Commander.location !== undefined) {
    const errfile = Commander.location.slice(0, Commander.location.indexOf("@"));
    const errline = Number.parseInt(Commander.location.slice(Commander.location.indexOf("@") + 1, Commander.location.indexOf("#")));
    const errpos = Number.parseInt(Commander.location.slice(Commander.location.indexOf("#") + 1));
    errlocation = { file: errfile, line: errline, pos: errpos };
}

setImmediate(() => {
    try {
        const smtasm = generateSMTAssemblyForValidate(massembly, vopts, Commander.entrypoint, errlocation);
        if (smtasm === undefined) {
            process.stdout.write(chalk.red("Error -- Failed to generate SMTLIB code\n"));
            process.exit(1);
        }

        if(smtasm.allErrors.findIndex((ee) => ee.file === errlocation.file && ee.pos === errlocation.pos) === -1) {
            process.stdout.write(chalk.red("Error -- No error associated with given position\n"));
            process.exit(1);
        }

        const smfc = buildSMT2file(smtasm as SMTAssembly, timeout, Commander.mode === "refute" ? "Refute" : "Generate");
        if (Commander.output) {
            emitSMT2File(smfc, Commander.output);
        }

        runSMT2File(smfc, Commander.mode === "refute" ? "Refute" : "Generate");
    }
    catch (ex) {
        process.stderr.write(chalk.red(`Error -- ${ex}\n`));
    }
});
