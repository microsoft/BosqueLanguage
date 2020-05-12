//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import * as Commander from "commander";

import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl, MIRType } from "../../compiler/mir_assembly";
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
    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "core/", corelibpath);
        const corefiles = FS.readdirSync(coredir);

        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
            code.push({ relativePath: cfpath, contents: FS.readFileSync(cfpath).toString() });
        }
 
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", true, true, code);
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

process.stdout.write(`Symbolic testing of Bosque sources in files:\n${Commander.args.join("\n")}\n...\n`);
const massembly = generateMASM(Commander.args, "symbolic");

setImmediate(() => {
    process.stdout.write(`Transpiling Bosque assembly to bytecode with entrypoint of ${Commander.entrypoint}...\n`);
    const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");

    try {
        if(massembly.invokeDecls.get(Commander.entrypoint) === undefined) {
            process.stderr.write(chalk.red("Could not find specified entrypoint!!!\n"));
            process.exit(1);
        }

        const entrypoint = massembly.invokeDecls.get(Commander.entrypoint) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => !massembly.subtypeOf(massembly.typeMap.get(p.type) as MIRType, massembly.typeMap.get("NSCore::APIValue") as MIRType))) {
            process.stderr.write("Only APIValue types are supported as inputs of Bosque programs.\n");
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

        process.stdout.write(`Running z3 on SMT encoding...\n`);

        if (Commander.output) {
            try {
                process.stdout.write(`Writing SMT output to "${Commander.output}..."\n`)
                FS.writeFileSync(Commander.output, contents);
            }
            catch (fex) {
                process.stderr.write(chalk.red(`Failed to write file -- ${fex}\n`));
            }
        }

        try {
            const res = execSync(`${z3path} -smt2 -in`, { input: contents }).toString().trim();

            if (res === "unsat") {
                process.stdout.write(chalk.green("Verified up to bound -- no errors found!\n"));
            }
            else {
                process.stdout.write(chalk.red("Detected possible errors!\n"));
                if (!Commander.model) {
                    process.stdout.write("Rerun with '-m' flag to attempt to generate failing inputs.\n");
                }
                else {
                    process.stdout.write("Attempting to extract inputs...\n");

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

                    process.stdout.write(`${inputs.join("\n")}\n`);
                }
            }
        }
        catch (exx) {
            if(Commander.model) {
                process.stdout.write("Cannot generate model '-m' as errors were not found?\n");
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
