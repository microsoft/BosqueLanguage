//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { MIRAssembly, PackageConfig } from "../../../compiler/mir_assembly";
import { MIREmitter } from "../../../compiler/mir_emitter";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../../compiler/mir_ops";

import { MorphirEmitter } from "./morphirdecls_emitter";
import { CodeFileInfo } from "../../../ast/parser";

import * as chalk from "chalk";
import { BuildApplicationMode, BuildLevel } from "../../../ast/assembly";

const bosque_dir: string = Path.join(__dirname, "../../../../");
const runtimepath: string = Path.join(bosque_dir, "bin/tooling/morphir/bsqtranspiler/runtime/BSQMain.elm");

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

function workflowLoadRuntime(): string | undefined {
    try {
        let runtime: string = FS.readFileSync(runtimepath).toString();
        return runtime;
    }
    catch (ex) {
        return undefined;
    }
}

function generateMASM(usercode: PackageConfig, buildlevel: BuildLevel, entrypointkeys: MIRInvokeKey[], entrypoint: {filename: string, names: string[]}): MIRAssembly {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    const { masm, errors } = MIREmitter.generateMASM(BuildApplicationMode.FunctionalizedExecutable, [coreconfig, usercode], buildlevel, false, entrypointkeys, entrypoint);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

function generateMorphirAssembly(masm: MIRAssembly, istestbuild: boolean, entrypoints: MIRInvokeKey[], runtime: string): string | undefined {
    let res: string | undefined = undefined;
    try {
        res = MorphirEmitter.generateMorphirPayload(masm, istestbuild, runtime, entrypoints);
    } catch(e) {
        process.stdout.write(chalk.red(`Morphir generate error -- ${e}\n`));
        process.exit(1);
    }
    return res;
}

function emitElmFile(cfile: string, into: string): boolean {
    try {
        FS.writeFileSync(into, cfile);
        return true;
    }
    catch (fex) {
        return false;
    }
}

function workflowEmitMorphirElmFile(into: string, usercode: PackageConfig, buildlevel: BuildLevel, istestbuild: boolean, entrypoint: {filename: string, names: string[], fkeys: MIRResolvedTypeKey[]}): boolean {
    const massembly = generateMASM(usercode, buildlevel, entrypoint.fkeys, {filename: entrypoint.filename, names: entrypoint.names});

    const runtime = workflowLoadRuntime();
    if(runtime === undefined) {
        return false;
    }

    const elmasm = generateMorphirAssembly(massembly, istestbuild, entrypoint.fkeys, runtime);        
    if (elmasm === undefined) {
        return false;
    }

    return emitElmFile(elmasm, into);
} 

export {
    workflowLoadUserSrc, workflowEmitMorphirElmFile
};
