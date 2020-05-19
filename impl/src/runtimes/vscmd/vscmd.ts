//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl, MIRType } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { SMTEmitter } from "../../tooling/bmc/smtdecls_emitter";
import { CPPEmitter } from "../../tooling/aot/cppdecls_emitter";

const scratchroot = Path.normalize(Path.join(__dirname, "../../scratch/"));
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
const compilerpath = (process.platform === "win32") ? "\"C:\\Program Files\\LLVM\\bin\\clang.exe\"" : "clang++";
const binext = (process.platform === "win32") ? "exe" : "out";

function checkMASM(files: string[], corelibpath: string, doemit: boolean): boolean {
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
        return false;
    }

    const errors = MIREmitter.generateMASM(new PackageConfig(), "debug", true, false, code).errors;
    if (doemit) {
        process.stdout.write(JSON.stringify(errors));
    }

    return errors.length === 0;
}

function generateMASM(files: string[], corelibpath: string, functionalize: boolean): MIRAssembly {
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
        process.exit(1);
    }

    const masm = MIREmitter.generateMASM(new PackageConfig(), "debug", true, functionalize, code).masm;

    return masm as MIRAssembly;
}

function compile(masm: MIRAssembly, wsroot: string, config: any): boolean {
    try {
        const cparams = CPPEmitter.emit(masm, config.entrypoint);

        const cpp_runtime = Path.join(binroot, "tooling/aot/runtime/");
        const lsrc = FS.readdirSync(cpp_runtime).filter((name) => name.endsWith(".h") || name.endsWith(".cpp"));
        const linked = lsrc.map((fname) => {
            const contents = FS.readFileSync(Path.join(cpp_runtime, fname)).toString();
            let bcontents = contents
            .replace("//%%STATIC_STRING_DECLARE%%", cparams.STATIC_STRING_DECLARE)
            .replace("//%%STATIC_STRING_CREATE%%", cparams.STATIC_STRING_CREATE)
            .replace("//%%STATIC_REGEX_DECLARE%%", cparams.STATIC_REGEX_DECLARE)
            .replace("//%%STATIC_REGEX_CREATE%%", cparams.STATIC_REGEX_CREATE)
            .replace("//%%STATIC_INT_DECLARE%%", cparams.STATIC_INT_DECLARE)
            .replace("//%%STATIC_INT_CREATE%%", cparams.STATIC_INT_CREATE)
            .replace("//%%PROPERTY_ENUM_DECLARE%%", cparams.PROPERTY_ENUM_DECLARE) 
            .replace("//%%NOMINAL_TYPE_ENUM_DECLARE%%", cparams.NOMINAL_TYPE_ENUM_DECLARE)
            .replace("//%%PROPERTY_NAMES%%", cparams.PROPERTY_NAMES)
            .replace("//%%NOMINAL_TYPE_DISPLAY_NAMES%%", cparams.NOMINAL_TYPE_DISPLAY_NAMES)
            .replace("//%%CONCEPT_SUBTYPE_RELATION_DECLARE%%", cparams.CONCEPT_SUBTYPE_RELATION_DECLARE)
            .replace("//%%NOMINAL_TYPE_TO_DATA_KIND%%", cparams.NOMINAL_TYPE_TO_DATA_KIND);


            const bstart = bcontents.indexOf("//%%SPECIAL_NAME_BLOCK_BEGIN%%");
            const bend = bcontents.indexOf("//%%SPECIAL_NAME_BLOCK_END%%");
            if(bstart !== -1) {
                bcontents = bcontents.slice(0, bstart) + "//%%SPECIAL_NAME_BLOCK_BEGIN%%\n" + cparams.SPECIAL_NAME_BLOCK_BEGIN + "\n" + bcontents.slice(bend);
            }

            return { file: fname, contents: bcontents };
        });

        if (masm.invokeDecls.get(config.entrypoint) === undefined) {
            process.stdout.write("Could not find specified entrypoint!!!");
            return false;
        }

        const entrypoint = masm.invokeDecls.get(config.entrypoint) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => !masm.subtypeOf(masm.typeMap.get(p.type) as MIRType, masm.typeMap.get("NSCore::APIValue") as MIRType))) {
            process.stdout.write("Only APIValue types are supported as inputs of Bosque programs.");
            return false;
        }

        const maincpp = "#include \"bsqruntime.h\"\n"
            + "namespace BSQ\n"
            + "{\n/*forward type decls*/\n"
            + cparams.TYPEDECLS_FWD
            + "\n\n/*ephemeral decls*/\n"
            + cparams.EPHEMERAL_LIST_DECLARE
            + "\n\n/*forward vable decls*/\n"
            + "\n\n/*forward function decls*/\n"
            + cparams.FUNC_DECLS_FWD
            + "\n\n/*type decls*/\n"
            + cparams.TYPEDECLS
            + "\n\n/*typecheck decls*/\n"
            + cparams.TYPECHECKS
            + "\n\n/*vable decls*/\n"
            + cparams.VFIELD_ACCESS
            + "\n\n/*function decls*/\n"
            + cparams.FUNC_DECLS
            + "}\n\n"
            + "using namespace BSQ;"
            + "\n\n/*main decl*/\n"
            + cparams.MAIN_CALL
        linked.push({ file: "main.cpp", contents: maincpp });

        const cpppath = Path.join(scratchroot, "cpp");
        FS.mkdirSync(cpppath, { recursive: true });

        linked.forEach((fp) => {
            const outfile = Path.join(cpppath, fp.file);
            FS.writeFileSync(outfile, fp.contents);
        });

        const customsrc = Path.join(cpp_runtime, "bsqcustom")
        const custompath = Path.join(cpppath, "bsqcustom");
        FS.mkdirSync(custompath, { recursive: true });
        const csrc = FS.readdirSync(customsrc).filter((name) => name.endsWith(".h"));

        csrc.forEach((cf) => {
            const fromfile = Path.join(customsrc, cf);
            const outfile = Path.join(custompath, cf);

            const contents = FS.readFileSync(fromfile).toString();
            FS.writeFileSync(outfile, contents);
        });

        const binfile = Path.join(wsroot, config.outdir, `${config.app}.${binext}`);
        execSync(`${compilerpath} -Os -march=native -std=c++17 -o ${binfile} ${cpppath}/*.cpp`);
    }
    catch (ex) {
        process.stdout.write(ex);
        return false;
    }

    return true;
}

function verify(masm: MIRAssembly, config: any, genmodel: boolean): [boolean, boolean] {
    try {
        const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");

        if (masm.invokeDecls.get(config.entrypoint) === undefined) {
            process.stdout.write("Could not find specified entrypoint!!!");
            return [false, false];
        }

        const entrypoint = masm.invokeDecls.get(config.entrypoint) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => !masm.subtypeOf(masm.typeMap.get(p.type) as MIRType, masm.typeMap.get("NSCore::APIValue") as MIRType))) {
            process.stderr.write("Only APIValue types are supported as inputs of Bosque programs.");
            return [false, false];
        }

        const sparams = SMTEmitter.emit(masm, entrypoint, true);
        const lsrc = FS.readFileSync(smt_runtime).toString();
        const contents = lsrc
            .replace(";;NOMINAL_DECLS_FWD;;", sparams.NOMINAL_DECLS_FWD)
            .replace(";;NOMINAL_CONSTRUCTORS;;", sparams.NOMINAL_CONSTRUCTORS)
            .replace(";;NOMINAL_OBJECT_CONSTRUCTORS;;", sparams.NOMINAL_OBJECT_CONSTRUCTORS)
            .replace(";;NOMINAL_TYPE_KIND_DECLS;;", sparams.NOMINAL_TYPE_KIND_DECLS)
            .replace(";;NOMINAL_TYPE_TO_DATA_KIND_ASSERTS;;", sparams.NOMINAL_TYPE_TO_DATA_KIND_ASSERTS)
            .replace(";;SPECIAL_NAME_BLOCK_ASSERTS;;", sparams.SPECIAL_NAME_BLOCK_ASSERTS)
            .replace(";;EPHEMERAL_DECLS;;", sparams.EPHEMERAL_DECLS)
            .replace(";;EMPTY_CONTENT_ARRAY_DECLS;;", sparams.EMPTY_CONTENT_ARRAY_DECLS)
            .replace(";;RESULTS_FWD;;", sparams.RESULTS_FWD)
            .replace(";;RESULTS;;", sparams.RESULTS)
            .replace(";;REGEX_DECLS;;", sparams.REGEX_DECLS)
            .replace(";;CONCEPT_SUBTYPE_RELATION_DECLARE;;", sparams.CONCEPT_SUBTYPE_RELATION_DECLARE)
            .replace(";;SUBTYPE_DECLS;;", sparams.SUBTYPE_DECLS)
            .replace(";;VFIELD_ACCESS;;", sparams.VFIELD_ACCESS)
            .replace(";;FUNCTION_DECLS;;", sparams.FUNCTION_DECLS)
            .replace(";;ARG_VALUES;;", sparams.ARG_VALUES)
            .replace(";;INVOKE_ACTION;;", sparams.INVOKE_ACTION)
            .replace(";;GET_MODEL;;", genmodel ? "(get-model)" : "");

        const res = execSync(`${z3path} -smt2 -in`, { input: contents }).toString().trim();

        if (res === "unsat") {
            return [true, true];
        }
        else {
            if (genmodel) {
                const splits = res.split("\n");
                const inputs = entrypoint.params.map((p) => {
                    const ridx = splits.findIndex((str) => str.trim().startsWith(`(define-fun @${p.name}`));
                    if (ridx === -1) {
                        return `{${p.name}: "???"}`
                    }
                    else {
                        const mres = splits[ridx + 1].trim();
                        return `{${p.name}: ${mres.substring(0, mres.length - 1).trim()}}`;
                    }
                });

                process.stdout.write(`[${inputs.join(", ")}]`);
            }

            return [true, false];
        }
    }
    catch (ex) {
        return [false, false];
    }
}

const command = process.argv[2];
const projectdir = Path.normalize(process.argv[3]);

const config = JSON.parse(FS.readFileSync(Path.join(projectdir, "config.json")).toString());
const pfiles = config.files.map((f: string) => Path.normalize(Path.join(projectdir, f)));

if(command === "typecheck") {
    checkMASM(pfiles, "cpp", true);
    process.exit(0);
}
else if(command === "compile") {
    const checkok = checkMASM(pfiles, "cpp", false);
    if(!checkok) {
        process.exit(1);
    }

    const masm = generateMASM(pfiles, "cpp", false);
    const compileok = compile(masm, projectdir, config);
    
    process.exit(compileok ? 0 : 1);
}
else if(command === "verify") {
    const checkok = checkMASM(pfiles, "symbolic", false);
    if(!checkok) {
        process.exit(1);
    }

    const masm = generateMASM(pfiles, "symbolic", true);
    const verifyyes = verify(masm, config, false);
    if(verifyyes[0] === false) {
        process.exit(1);
    }

    if(!verifyyes[1]) {
        verify(masm, config, true);
    }

    process.exit(0);
}
else {
    process.exit(1);
}