//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";

import { CodeFileInfo } from "../ast/parser";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = Path.join(bosque_dir, "bin/core/verify");
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

function generateMASM(usercode: CodeFileInfo[], entrypoint: string): { masm: MIRAssembly | undefined, errors: string[] } {
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

    return MIREmitter.generateMASM(new PackageConfig(), "debug", [], {namespace: namespace, names: [entryfunc]}, true, code);
}

function runCompilerTest(testsrc: string): { result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string } {
    const start = new Date();
    const codeinfo = [{fpath: "test.bsq", contents: testsrc}];
    try {
        const { masm, errors } = generateMASM(codeinfo, "NSMain::main");

        return {
            result: masm === undefined ? "pass" : "fail",
            start: start,
            end: new Date(),
            info: errors.join("\n")
        }
    }
    catch (ex) {
        return {
            result: "error",
            start: start,
            end: new Date,
            info: `${ex}`
        }
    }
}

export {
    runCompilerTest
};