//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import * as Commander from "commander";

import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { SMTEmitter } from "../../tooling/bmc/smtdecls_emitter";
import chalk from "chalk";

const binroot = Path.normalize(Path.join(__dirname, "../../"));

let platpathsmt: string | undefined = undefined;
if (process.platform === "win32") {
    platpathsmt = "bin/win/z3.exe";
}
else if (process.platform === "linux") {
    platpathsmt = "bin/linux/z3";
}
else {
    platpathsmt = "bin/macos/z3";
}

const z3path = Path.normalize(Path.join(__dirname, "../../tooling/bmc/runtime", platpathsmt));

function generateMASM(files: string[], corelibpath: string): MIRAssembly {
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(corelibpath, "/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(corelibpath, "/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        code = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }];
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

Commander
    .option("-e --entrypoint [entrypoint]", "Entrypoint to symbolically test", "NSMain::main")
    .option("-m --model", "Try to get model for failing inputs", false)
    .option("-o --output [file]", "Output the model to a given file");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file as an argument\n"));
    process.exit(1);
}

console.log(`Symbolic testing of Bosque sources in files:\n${Commander.args.join("\n")}\n...\n`);
const massembly = generateMASM(Commander.args, Path.normalize(Path.join(__dirname, "../../", "core/direct/")));

setImmediate(() => {
    console.log(`Transpiling Bosque assembly to bytecode with entrypoint of ${Commander.entrypoint}...`);
    const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");

    try {
        if(massembly.invokeDecls.get(Commander.entrypoint) === undefined) {
            process.stderr.write(chalk.red("Could not find specified entrypoint!!!\n"));
            process.exit(1);
        }

        const entrypoint = massembly.invokeDecls.get(Commander.entrypoint) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => p.type !== "NSCore::Bool" && p.type !== "NSCore::Int" && p.type !== "NSCore::String")) {
            process.stderr.write("Only Bool/Int/String are supported as inputs for symbolic testing of Bosque programs.\n");
            process.exit(1);
        }

        const sparams = SMTEmitter.emit(massembly, entrypoint, true);
        const lsrc = FS.readFileSync(smt_runtime).toString();
        const contents = lsrc
            .replace(";;NOMINAL_DECLS_FWD;;", sparams.NOMINAL_DECLS_FWD)
            .replace(";;NOMINAL_CONSTRUCTORS;;", sparams.NOMINAL_CONSTRUCTORS)
            .replace(";;NOMINAL_OBJECT_CONSTRUCTORS;;", sparams.NOMINAL_OBJECT_CONSTRUCTORS)
            .replace(";;NOMINAL_TYPE_TO_DATA_KIND_ASSERTS;;", sparams.NOMINAL_TYPE_TO_DATA_KIND_ASSERTS)
            .replace(";;SPECIAL_NAME_BLOCK_ASSERTS;;", sparams.SPECIAL_NAME_BLOCK_ASSERTS)
            .replace(";;EPHEMERAL_DECLS;;", sparams.EPHEMERAL_DECLS)
            .replace(";;EMPTY_CONTENT_ARRAY_DECLS;;", sparams.EMPTY_CONTENT_ARRAY_DECLS)
            .replace(";;RESULTS_FWD;;", sparams.RESULTS_FWD)
            .replace(";;RESULTS;;", sparams.RESULTS)
            .replace(";;CONCEPT_SUBTYPE_RELATION_DECLARE;;", sparams.CONCEPT_SUBTYPE_RELATION_DECLARE)
            .replace(";;SUBTYPE_DECLS;;", sparams.SUBTYPE_DECLS)
            .replace(";;VFIELD_ACCESS;;", sparams.VFIELD_ACCESS)
            .replace(";;FUNCTION_DECLS;;", sparams.FUNCTION_DECLS)
            .replace(";;ARG_VALUES;;", sparams.ARG_VALUES)
            .replace(";;INVOKE_ACTION;;", sparams.INVOKE_ACTION)
            .replace(";;GET_MODEL;;", Commander.model ? "(get-model)" : "");

        console.log(`Running z3 on SMT encoding...`);

        if (Commander.output) {
            try {
                console.log(`Writing SMT output to "${Commander.output}..."`)
                FS.writeFileSync(Commander.output, contents);
            }
            catch (fex) {
                console.log(chalk.red(`Failed to write file -- ${fex}.`));
            }
        }

        try {
            const res = execSync(`${z3path} -smt2 -in`, { input: contents }).toString().trim();

            if (res === "unsat") {
                console.log(chalk.green("Verified up to bound -- no errors found!"));
            }
            else {
                console.log(chalk.red("Detected possible errors!"));
                if (!Commander.model) {
                    console.log("Rerun with '-m' flag to attempt to generate failing inputs.")
                }
                else {
                    console.log("Attempting to extract inputs...");

                    const splits = res.split("\n");
                    const inputs = entrypoint.params.map((p) => {
                        const ridx = splits.findIndex((str) => str.trim().startsWith(`(define-fun @${p.name}`));
                        if (ridx === -1) {
                            return `${p.name} = ??`;
                        }
                        else {
                            const mres = splits[ridx + 1].trim();
                            return `${p.name} = ${mres.substring(0, mres.length - 1).trim()}`;
                        }
                    });

                    console.log(inputs.join("\n"));
                }
            }
        }
        catch (exx) {
            if(Commander.model) {
                console.log("Cannot generate model '-m' as errors were not found?")
            }
            else {
                throw exx;
            }
        }
    }
    catch (ex) {
        process.stderr.write(chalk.red(`Error -- ${ex}\n`));
    }
});
