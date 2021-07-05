//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { ICPPAssembly, TranspilerOptions } from "../tooling/icpp/transpiler/icpp_assembly";
import { MIRInvokeKey } from "../compiler/mir_ops";
import { ICPPEmitter } from "../tooling/icpp/transpiler/icppdecls_emitter";

import chalk from "chalk";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const exepath: string = Path.normalize(Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : "")));

function generateMASM(files: string[], entrypoint: string): MIRAssembly {
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "bin/core/execute");
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

    const macros: string[] = [];
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", macros, {namespace: namespace, names: [entryfunc]}, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function generateICPPAssembly(masm: MIRAssembly, topts: TranspilerOptions, entrypoint: MIRInvokeKey): ICPPAssembly | undefined {
    let res: ICPPAssembly | undefined = undefined;
    try {
        res = ICPPEmitter.generateICPPAssembly(masm, topts, entrypoint);
    } catch(e) {
        process.stdout.write(chalk.red(`ICPP bytecode generate error -- ${e}\n`));
        process.exit(1);
    }
    return res;
}

function emitICPPFile(cfile: string, into: string) {
    try {
        process.stdout.write(`Writing bytecode output to "${into}..."\n`)
        FS.writeFileSync(into, cfile);
    }
    catch (fex) {
        process.stderr.write(chalk.red(`Failed to write file -- ${fex}\n`));
    }
}

function runICPPFile(icppjson: string): string {
    try {
        process.stdout.write(`Running code..."\n`)

        const cmd = `${exepath} --stream`;
        return execSync(cmd, { input: icppjson }).toString().trim();
    }
    catch(ex) {
        return JSON.stringify({result: "error", info: `${ex}`});
    }
}


const mode = process.argv[2];
const args = process.argv.slice(mode === "--output" ? 4 : 3);

const topts = {
} as TranspilerOptions;


if (args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file and target line as arguments\n"));
    process.exit(1);
}

process.stdout.write(`Processing Bosque sources in:\n${args.join("\n")}\n...\n`);
const massembly = generateMASM(args, "NSMain::main");
const icppasm = generateICPPAssembly(massembly, topts, "NSMain::main");
        
if (icppasm === undefined) {
    process.stdout.write(chalk.red("Error -- Failed to generate bytecode\n"));
    process.exit(1);
}

const icppjson = JSON.stringify(icppasm.jsonEmit(), undefined, "  ");

if (mode === "--output") {
    emitICPPFile(icppjson, process.argv[3]);
}
else {
    const output = runICPPFile(icppjson);
    process.stdout.write(output + "\n");
}

