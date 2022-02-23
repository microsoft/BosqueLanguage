//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { BuildApplicationMode, BuildLevel } from "../../ast/assembly";
import { CodeFileInfo } from "../../ast/parser";
import { MIRAssembly, PackageConfig } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { ICPPEmitter } from "../../tooling/icpp/transpiler/icppdecls_emitter";
import { TranspilerOptions } from "../../tooling/icpp/transpiler/icpp_assembly";
import { VerifierOptions } from "../../tooling/checker/smt_exp";
import { SMTEmitter } from "../../tooling/checker/smtdecls_emitter";

import chalk from "chalk";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../../"));

const icpppath: string = Path.normalize(Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : "")));

const smtruntime_path = Path.join(bosque_dir, "bin/tooling/checker/runtime/smtruntime.smt2");
const smtruntime = FS.readFileSync(smtruntime_path).toString();
const smtpath = Path.normalize(Path.join(bosque_dir, "/build/output/chk" + (process.platform === "win32" ? ".exe" : "")));

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

function generateMASMForICPP(buildlevel: BuildLevel, usercode: PackageConfig[], corecode: CodeFileInfo[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.Executable, [coreconfig, ...usercode], buildlevel, entrypoint);
}

function generateICPPAssembly(masm: MIRAssembly, istestbuild: boolean, topts: TranspilerOptions, entrypoints: MIRInvokeKey[]): [boolean, any] {
    try {
        return [true, ICPPEmitter.generateICPPAssembly(masm, istestbuild, topts, entrypoints)];
    } catch(e: any) {
        return [false, e.toString()];
    }
}

function generateMASMForSMT(usercode: PackageConfig[], corecode: CodeFileInfo[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["CHECK_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.ModelChecker, [coreconfig, ...usercode], "debug", entrypoint);
}

function generateSMTPayload(masm: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): string | undefined {
    try {
        return SMTEmitter.generateSMTPayload(masm, istestbuild, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        return undefined;
    }
}

function generateCheckerPayload(masm: MIRAssembly, smtasm: string, timeout: number, entrypoint: MIRInvokeKey): any {
    return {smt2decl: smtasm, timeout: timeout, apimodule: masm.emitAPIInfo([entrypoint], true), "mainfunc": entrypoint};
}

function runtestsICPP(files: string[], verbose: "std" | "extra" | "max", category: ("sym" | "icpp" | "err" | "chk" | "direct" | "params")[], dirs: string[]) {
    if(category.includes("icpp")) {

    }
}

function runtestsSMT(files: string[], verbose: "std" | "extra" | "max", category: ("sym" | "icpp" | "err" | "chk" | "direct" | "params")[], dirs: string[]) {
    if(category.includes("sym")) {

    }
}

function runtests(files: string[], verbose: "std" | "extra" | "max", category: ("sym" | "icpp" | "err" | "chk" | "direct" | "params")[], dirs: string[]) {
    
}