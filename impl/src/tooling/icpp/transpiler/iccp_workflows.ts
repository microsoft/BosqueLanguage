//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { exec } from "child_process";

import { MIRAssembly, PackageConfig } from "../../../compiler/mir_assembly";
import { MIREmitter } from "../../../compiler/mir_emitter";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { TranspilerOptions } from "./icpp_assembly";
import { ICPPEmitter } from "./icppdecls_emitter";
import { CodeFileInfo } from "../../../ast/parser";

import * as chalk from "chalk";
import { BuildApplicationMode, BuildLevel } from "../../../ast/assembly";

const bosque_dir: string = Path.join(__dirname, "../../../../");
const exepath: string = Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : ""));

const DEFAULT_TOPTS = {
} as TranspilerOptions;

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

function generateMASM(usercode: PackageConfig, buildlevel: BuildLevel, entrypoint: {filename: string, names: string[]}): MIRAssembly {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    const { masm, errors } = MIREmitter.generateMASM(BuildApplicationMode.Executable, [coreconfig, usercode], buildlevel, entrypoint);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function generateICPPAssembly(srcCode: { fname: string, contents: string }[], masm: MIRAssembly, istestbuild: boolean, topts: TranspilerOptions, entrypoints: MIRInvokeKey[]): any {
    let res: any = undefined;
    try {
        res = ICPPEmitter.generateICPPAssembly(srcCode, masm, istestbuild, topts, entrypoints);
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

function runICPPFile(icppjson: {code: object, args: any[], main: string}, debug: boolean, cb: (result: string | undefined) => void) {
    try {
        const cmd = `${exepath} ${debug ? "--debug " : ""}--stream`;

        const proc = exec(cmd, (err, stdout) => {
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

function workflowEmitICPPFile(into: string, usercode: PackageConfig, emitsrcmap: boolean, buildlevel: BuildLevel, istestbuild: boolean, topts: TranspilerOptions, entrypoint: {filename: string, names: string[], fkeys: MIRResolvedTypeKey[]}): boolean {
    const massembly = generateMASM(usercode, buildlevel, {filename: entrypoint.filename, names: entrypoint.names});

    //TODO: we want to strip to a relative path here to avoid shipping any system specific info
    const srcCode = emitsrcmap ? usercode.src.map((sf) => { return {fname: sf.srcpath, contents: sf.contents}; }) : [];

    const icppasm = generateICPPAssembly(srcCode, massembly, istestbuild, topts, entrypoint.fkeys);
            
    if (icppasm === undefined) {
        return false;
    }

    const icppjson = JSON.stringify({code: {api: massembly.emitAPIInfo(entrypoint.fkeys, istestbuild), bytecode: icppasm }}, undefined, 2);
    return emitICPPFile(icppjson, into);
} 

function workflowRunICPPFile(args: any[], usercode: PackageConfig, emitsrcmap: boolean, buildlevel: BuildLevel, istestbuild: boolean, debug: boolean, topts: TranspilerOptions, entrypoint: {filename: string, name: string, fkey: MIRResolvedTypeKey}, cb: (result: string | undefined) => void) {
    const massembly = generateMASM(usercode, buildlevel, {filename: entrypoint.filename, names: [entrypoint.name]});

    //TODO: we want to strip to a relative path here to avoid shipping any system specific info
    const srcCode = emitsrcmap ? usercode.src.map((sf) => { return {fname: sf.srcpath, contents: sf.contents}; }) : [];

    const icppasm = generateICPPAssembly(srcCode, massembly, istestbuild, topts, [entrypoint.fkey]);
            
    if (icppasm === undefined) {
        return undefined;
    }

    return runICPPFile({code: {api: massembly.emitAPIInfo([entrypoint.fkey], istestbuild), bytecode: icppasm }, args: args, main: entrypoint.fkey}, debug, cb);
}

export {
    DEFAULT_TOPTS,
    workflowLoadUserSrc, workflowEmitICPPFile, workflowRunICPPFile
};
