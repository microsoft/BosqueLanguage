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
import { SMTEmitter } from "../tooling/verifier/smtdecls_emitter";
import { VerifierOptions } from "../tooling/verifier/smt_exp";
import { MIRInvokeKey } from "../compiler/mir_ops";

let platpathsmt: string | undefined = undefined;
if (process.platform === "win32") {
    platpathsmt = "build/tools/win/z3.exe";
}
else if (process.platform === "linux") {
    platpathsmt = "build/tools/linux/z3";
}
else {
    platpathsmt = "build/tools/macos/z3";
}

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const z3path = Path.normalize(Path.join(bosque_dir, platpathsmt));

function generateMASM(files: string[], entrypoint: string): MIRAssembly {
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "bin/core/verify");
        const corefiles = FS.readdirSync(coredir);

        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
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

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", {namespace: namespace, names: [entryfunc]}, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function generateSMTAssemblyForValidate(masm: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey, errorTrgtPos: { file: string, line: number, pos: number }, maxgas: number): SMTAssembly | undefined {
    let res: SMTAssembly | undefined = undefined;
    try {
        res = SMTEmitter.generateSMTAssemblyForValidate(masm, vopts, errorTrgtPos, entrypoint, maxgas);
    } catch(e) {
        process.stdout.write(chalk.red(`SMT generate error -- ${e}\n`));
        process.exit(1);
    }
    return res;
}

function buildSMT2file(smtasm: SMTAssembly, timeout: number, mode: "Refute" | "Generate"): string {
    const sfileinfo = smtasm.generateSMT2AssemblyInfo(mode);

    function joinWithIndent(data: string[], indent: string): string {
        if (data.length === 0) {
            return ";;NO DATA;;"
        }
        else {
            return data.map((d, i) => (i === 0 ? "" : indent) + d).join("\n");
        }
    }

    let contents = "";
    try {
        const smt_runtime = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
        const lsrc = FS.readFileSync(smt_runtime).toString();
        contents = lsrc
            .replace(";;TIMEOUT;;", `${timeout}`)
            .replace(";;TYPE_TAG_DECLS;;", joinWithIndent(sfileinfo.TYPE_TAG_DECLS, "      "))
            .replace(";;ABSTRACT_TYPE_TAG_DECLS;;", joinWithIndent(sfileinfo.ABSTRACT_TYPE_TAG_DECLS, "      "))
            .replace(";;INDEX_TAG_DECLS;;", joinWithIndent(sfileinfo.INDEX_TAG_DECLS, "      "))
            .replace(";;PROPERTY_TAG_DECLS;;", joinWithIndent(sfileinfo.PROPERTY_TAG_DECLS, "      "))
            .replace(";;SUBTYPE_DECLS;;", joinWithIndent(sfileinfo.SUBTYPE_DECLS, ""))
            .replace(";;TUPLE_HAS_INDEX_DECLS;;", joinWithIndent(sfileinfo.TUPLE_HAS_INDEX_DECLS, ""))
            .replace(";;RECORD_HAS_PROPERTY_DECLS;;", joinWithIndent(sfileinfo.RECORD_HAS_PROPERTY_DECLS, ""))
            .replace(";;KEY_TYPE_TAG_RANK;;", joinWithIndent(sfileinfo.KEY_TYPE_TAG_RANK, ""))
            .replace(";;BINTEGRAL_TYPE_ALIAS;;", joinWithIndent(sfileinfo.BINTEGRAL_TYPE_ALIAS, ""))
            .replace(";;BFLOATPOINT_TYPE_ALIAS;;", joinWithIndent(sfileinfo.BFLOATPOINT_TYPE_ALIAS, ""))
            .replace(";;STRING_TYPE_ALIAS;;", sfileinfo.STRING_TYPE_ALIAS + "\n")
            .replace(";;BINTEGRAL_CONSTANTS;;", joinWithIndent(sfileinfo.BINTEGRAL_CONSTANTS, ""))
            .replace(";;BFLOATPOINT_CONSTANTS;;", joinWithIndent(sfileinfo.BFLOATPOINT_CONSTANTS, ""))
            .replace(";;KEY_TUPLE_DECLS;;", joinWithIndent(sfileinfo.KEY_TUPLE_INFO.decls, "      "))
            .replace(";;KEY_RECORD_DECLS;;", joinWithIndent(sfileinfo.KEY_RECORD_INFO.decls, "      "))
            .replace(";;KEY_TYPE_DECLS;;", joinWithIndent(sfileinfo.KEY_TYPE_INFO.decls, "      "))
            .replace(";;KEY_TUPLE_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.KEY_TUPLE_INFO.constructors, "    "))
            .replace(";;KEY_RECORD_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.KEY_RECORD_INFO.constructors, "    "))
            .replace(";;KEY_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.KEY_TYPE_INFO.constructors, "    "))
            .replace(";;KEY_TUPLE_TYPE_BOXING;;", joinWithIndent(sfileinfo.KEY_TUPLE_INFO.boxing, "      "))
            .replace(";;KEY_RECORD_TYPE_BOXING;;", joinWithIndent(sfileinfo.KEY_RECORD_INFO.boxing, "      "))
            .replace(";;KEY_TYPE_BOXING;;", joinWithIndent(sfileinfo.KEY_TYPE_INFO.boxing, "      "))
            .replace(";;TUPLE_DECLS;;", joinWithIndent(sfileinfo.TUPLE_INFO.decls, "    "))
            .replace(";;RECORD_DECLS;;", joinWithIndent(sfileinfo.RECORD_INFO.decls, "    "))
            .replace(";;TYPE_COLLECTION_INTERNAL_INFO_DECLS;;", joinWithIndent(sfileinfo.TYPE_COLLECTION_INTERNAL_INFO.decls, "    "))
            .replace(";;TYPE_DECLS;;", joinWithIndent(sfileinfo.TYPE_INFO.decls, "    "))
            .replace(";;TUPLE_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.TUPLE_INFO.constructors, "    "))
            .replace(";;RECORD_TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.RECORD_INFO.constructors, "    "))
            .replace(";;TYPE_COLLECTION_INTERNAL_INFO_CONSTRUCTORS;;", joinWithIndent(sfileinfo.TYPE_COLLECTION_INTERNAL_INFO.constructors, "    "))
            .replace(";;TYPE_CONSTRUCTORS;;", joinWithIndent(sfileinfo.TYPE_INFO.constructors, "    "))
            .replace(";;TUPLE_TYPE_BOXING;;", joinWithIndent(sfileinfo.TUPLE_INFO.boxing, "      "))
            .replace(";;RECORD_TYPE_BOXING;;", joinWithIndent(sfileinfo.RECORD_INFO.boxing, "      "))
            .replace(";;TYPE_BOXING;;", joinWithIndent(sfileinfo.TYPE_INFO.boxing, "      "))
            .replace(";;EPHEMERAL_DECLS;;", joinWithIndent(sfileinfo.EPHEMERAL_DECLS.decls, "      "))
            .replace(";;EPHEMERAL_CONSTRUCTORS;;", joinWithIndent(sfileinfo.EPHEMERAL_DECLS.constructors, "      "))
            .replace(";;RESULT_DECLS;;", joinWithIndent(sfileinfo.RESULT_INFO.decls, "      "))
            .replace(";;MASK_DECLS;;", joinWithIndent(sfileinfo.MASK_INFO.decls, "      "))
            .replace(";;RESULTS;;", joinWithIndent(sfileinfo.RESULT_INFO.constructors, "    "))
            .replace(";;MASKS;;", joinWithIndent(sfileinfo.MASK_INFO.constructors, "    "))
            .replace(";;GLOBAL_DECLS;;", joinWithIndent(sfileinfo.GLOBAL_DECLS, ""))
            .replace(";;UF_DECLS;;", joinWithIndent(sfileinfo.UF_DECLS, "\n"))
            .replace(";;FUNCTION_DECLS;;", joinWithIndent(sfileinfo.FUNCTION_DECLS, "\n"))
            .replace(";;GLOBAL_DEFINITIONS;;", joinWithIndent(sfileinfo.GLOBAL_DEFINITIONS, ""))
            .replace(";;ACTION;;", joinWithIndent(sfileinfo.ACTION, ""));
    }
    catch (ex) {
        process.stderr.write(chalk.red(`Error -- ${ex}\n`));
        process.exit(1);
    }

    return contents;
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

function runSMT2File(cfile: string, mode: "Refute" | "Generate") {
    process.stdout.write(`Running z3 on SMT encoding...\n`);
    const res = execSync(`${z3path} -smt2 -in`, { input: cfile }).toString().trim();
    process.stdout.write(`done!\n\n`);

    if (mode === "Refute") {
        if (res === "unsat") {
            process.stdout.write(chalk.green("Verified error is not possible!\n"));
        }
        else if (res === "sat") {
            process.stdout.write(chalk.red("Error can occour -- run in generate mode to attempt failing input generation!\n"));
        }
        else {
            process.stdout.write("Solver timeout :(\n");
        }
    }
    else {
        process.stdout.write(`Emitting raw SMTLIB model...\n`);
        process.stdout.write(res + "\n\n");
    }
}

Commander
    .option("-l --location [location]", "Location (file.bsq@line#pos) with error of interest")
    .option("-e --entrypoint [entrypoint]", "Entrypoint to symbolically test", "NSMain::main")
    .option("-m --mode [mode]", "Mode to run (errorlocs | refute | generate)", "refute")
    .option("-o --output [file]", "Output the model to a given file");

Commander.parse(process.argv);

const maxgas = 0;
const timeout = 10000;
const vopts = {
    ISize: 4,
    BigXMode: "BV",
    OverflowEnabled: false,
    FPOpt: "Real",
    StringOpt: "ASCII",
    SimpleQuantifierMode: false,
    SpecializeSmallModelGen: false
} as VerifierOptions;

if (Commander.args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file and target line as arguments\n"));
    process.exit(1);
}

if(Commander.mode !== "errorlocs" && Commander.mode !== "refute" && Commander.mode !== "generate") {
    process.stdout.write(chalk.red("Error -- Valid modes are \"errorlocs\", \"refute\", and \"generate\"\n"));
    process.exit(1);
}

process.stdout.write(`Processing Bosque sources in:\n${Commander.args.join("\n")}\n...Using entrypoint ${Commander.entrypoint}...\n`);
const massembly = generateMASM(Commander.args, Commander.entrypoint);

if(Commander.mode === "errorlocs" || Commander.location === undefined) {
    const sasm = generateSMTAssemblyForValidate(massembly, vopts, Commander.entrypoint, {file: "[]", line: -1, pos: -1}, maxgas);
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
        const smtasm = generateSMTAssemblyForValidate(massembly, vopts, Commander.entrypoint, errlocation, maxgas);
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
