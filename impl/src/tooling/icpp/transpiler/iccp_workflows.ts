//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import { MIRAssembly, PackageConfig } from "../../../compiler/mir_assembly";
import { MIREmitter } from "../../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../../compiler/mir_ops";

import { ICPPAssembly, TranspilerOptions } from "./icpp_assembly";
import { ICPPEmitter } from "./icppdecls_emitter";

import chalk from "chalk";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));
const exepath: string = Path.normalize(Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : "")));

const DEFAULT_TOPTS = {
} as TranspilerOptions;

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

function emitICPPFile(cfile: string, into: string): boolean {
    try {
        FS.writeFileSync(into, cfile);
        return true;
    }
    catch (fex) {
        return false;
    }
}

function runICPPFile(icppjson: string): string | undefined {
    try {
        const cmd = `${exepath} --stream`;
        return execSync(cmd, { input: icppjson }).toString().trim();
    }
    catch(ex) {
        return undefined;
    }
}

function workflowEmitICPPFile(into: string, files: string[], topts: TranspilerOptions, entrypoint: MIRInvokeKey): boolean {
    const massembly = generateMASM(files, entrypoint);
    const icppasm = generateICPPAssembly(massembly, topts, "NSMain::main");
            
    if (icppasm === undefined) {
        return false;
    }

    const icppjson = JSON.stringify(icppasm.jsonEmit(), undefined, 2);
    return emitICPPFile(icppjson, into);
}

function workflowRunICPPFile(args: any[], files: string[], topts: TranspilerOptions, entrypoint: MIRInvokeKey): string | undefined {
    const massembly = generateMASM(files, entrypoint);
    const icppasm = generateICPPAssembly(massembly, topts, "NSMain::main");
            
    if (icppasm === undefined) {
        return undefined;
    }

    const icppjson = JSON.stringify({code: icppasm.jsonEmit(), args: args}, undefined, 2);
    return runICPPFile(icppjson);
}

export {
    DEFAULT_TOPTS,
    workflowEmitICPPFile, workflowRunICPPFile
};
