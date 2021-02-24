//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";
import { exec, ExecException } from "child_process";

import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { SMTAssembly } from "../tooling/verifier/smt_assembly";
import { SMTEmitter } from "../tooling/verifier/smtdecls_emitter";
import { VerifierOptions } from "../tooling/verifier/smt_exp";

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
const smtlib_path = Path.join(bosque_dir, "bin/core/verify");
const smtruntime_path = Path.join(bosque_dir, "bin/tooling/verifier/runtime/smtruntime.smt2");
const z3path = Path.normalize(Path.join(bosque_dir, platpathsmt));

function generateMASM(corefiles: {relativePath: string, contents: string}[], testsrc: string): [MIRAssembly | undefined, string[]] {
    const code: { relativePath: string, contents: string }[] = [...corefiles, { relativePath: "test.bsq", contents: testsrc }];
    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", {namespace: "NSMain", names: ["main"]}, true, code);

    return [masm, errors];
}

function buildSMT2file(smtasm: SMTAssembly, smtruntime: string, timeout: number, mode: "Refute" | "Reach"): string {
    const sfileinfo = smtasm.generateSMT2AssemblyInfo(mode);

    function joinWithIndent(data: string[], indent: string): string {
        if (data.length === 0) {
            return ";;NO DATA;;"
        }
        else {
            return data.map((d, i) => (i === 0 ? "" : indent) + d).join("\n");
        }
    }

    return smtruntime
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

function runSMT2File(cfile: string, mode: "Refute" | "Reach", start: Date, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const res = exec(`${z3path} -smt2 -in`, (err: ExecException | null, stdout: string, stderr: string) => {
        if (err) {
            cb("error", start, new Date(), stderr);
        }
        else {
            const res = stdout.trim();

            if (mode === "Refute") {
                if (res === "unsat") {
                    cb("pass", start, new Date());
                }
                else if (res === "sat") {
                    cb("fail", start, new Date());
                }
                else {
                    cb("unknown/timeout", start, new Date(), stderr);
                }
            }
            else {
                if (res === "sat") {
                    cb("pass", start, new Date());
                }
                else if (res === "unsat") {
                    cb("fail", start, new Date());
                }
                else {
                    cb("unknown/timeout", start, new Date(), stderr);
                }
            }
        }
    });

    res.stdin.setDefaultEncoding('utf-8');
    res.stdin.write(cfile);
    res.stdin.end();
}

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

function enqueueSMTTest(mode: "Refute" | "Reach", corefiles: {relativePath: string, contents: string}[], smtruntime: string, testsrc: string, trgtline: number, cb: (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => void) {
    const start = new Date();
    const massembly = generateMASM(corefiles, testsrc);
    if(massembly[0] === undefined) {
        cb("error", start, new Date(), "Failed to generate assembly -- " + JSON.stringify(massembly[1]));
        return;
    }

    const sasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, { file: "[]", line: -1, pos: -1 }, "NSMain::main", maxgas);
    const errlocation = sasm.allErrors.find((ee) => ee.file === "test.bsq" && ee.line === trgtline);
    if(errlocation === undefined) {
        cb("error", start, new Date(), "Invalid trgt line");
    }
    else {
        const smtasm = SMTEmitter.generateSMTAssemblyForValidate(massembly[0], vopts, errlocation, "NSMain::main", maxgas);
        const smfc = buildSMT2file(smtasm, smtruntime, timeout, mode);

        runSMT2File(smfc, mode, start, cb);
    }
}

export {
    smtlib_path,
    smtruntime_path,
    enqueueSMTTest
};
