//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { exec } from "child_process";

import { MIRAssembly, PackageConfig } from "../../../compiler/mir_assembly";
import { MIREmitter } from "../../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../../compiler/mir_ops";

import { ICPPAssembly, TranspilerOptions } from "./icpp_assembly";
import { ICPPEmitter } from "./icppdecls_emitter";
import { CodeFileInfo } from "../../../ast/parser";

import chalk from "chalk";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../../"));
const exepath: string = Path.normalize(Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : "")));

const DEFAULT_TOPTS = {
} as TranspilerOptions;

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

        const coredir = Path.join(bosque_dir, "bin/core/execute");
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

function generateMASM(usercode: CodeFileInfo[], entrypoint: string): MIRAssembly {
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

function runICPPFile(icppjson: {code: object, args: any[]}, cb: (result: string | undefined) => void) {
    try {
        const cmd = `${exepath} --stream`;

        const proc = exec(cmd, (err, stdout, stderr) => {
            cb(stdout.toString().trim());
        });

        proc.stdin.setDefaultEncoding('utf-8');
        proc.stdin.write(JSON.stringify(icppjson, undefined, 2));
        proc.stdin.write("\n");
        proc.stdin.end()
    }
    catch(ex) {
        cb(undefined);
    }
}

function workflowEmitICPPFile(into: string, usercode: CodeFileInfo[], topts: TranspilerOptions, entrypoint: MIRInvokeKey): boolean {
    const massembly = generateMASM(usercode, entrypoint);
    const icppasm = generateICPPAssembly(massembly, topts, "NSMain::main");
            
    if (icppasm === undefined) {
        return false;
    }

    const icppjson = JSON.stringify(icppasm.jsonEmit(), undefined, 2);
    return emitICPPFile(icppjson, into);
}

function workflowRunICPPFile(args: any[], usercode: CodeFileInfo[], topts: TranspilerOptions, entrypoint: MIRInvokeKey, cb: (result: string | undefined) => void) {
    const massembly = generateMASM(usercode, entrypoint);
    const icppasm = generateICPPAssembly(massembly, topts, "NSMain::main");
            
    if (icppasm === undefined) {
        return undefined;
    }

    return runICPPFile({code: icppasm.jsonEmit(), args: args}, cb);
}

export {
    DEFAULT_TOPTS,
    workflowLoadUserSrc, workflowEmitICPPFile, workflowRunICPPFile
};
