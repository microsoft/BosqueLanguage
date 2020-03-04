"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const FS = require("fs");
const Path = require("path");
const Commander = require("commander");
const mir_assembly_1 = require("../compiler/mir_assembly");
const mir_emitter_1 = require("../compiler/mir_emitter");
const cppdecls_emitter_1 = require("../tooling/aot/cppdecls_emitter");
const smtdecls_emitter_1 = require("../tooling/bmc/smtdecls_emitter");
const scratchroot = Path.normalize(Path.join(__dirname, "../scratch/"));
const binroot = Path.normalize(Path.join(__dirname, "../"));
function generateMASM(files, corelibpath) {
    let code = [];
    try {
        const coredir = Path.join(corelibpath, "/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();
        const collectionsdir = Path.join(corelibpath, "/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();
        code = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }];
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
    }
    const { masm, errors } = mir_emitter_1.MIREmitter.generateMASM(new mir_assembly_1.PackageConfig(), "debug", true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }
        process.exit(1);
    }
    return masm;
}
Commander
    .option("-t --typecheck", "Parse and Typecheck")
    .option("-s --symbolic <entrypoint>", "Symbolic testing from specified entrypoint (default to error finding)")
    .option("-r --result <entrypoint>", "Symbolic execution with non-error result model")
    .option("-c --compile <entrypoint>", "Compile the specified entrypoint");
Commander.parse(process.argv);
if (Commander.typecheck === undefined && Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}
const massembly = generateMASM(Commander.args, Path.normalize(Path.join(__dirname, "../", (Commander.symbolic || Commander.result) ? "core/direct/" : "core/direct/")));
if (Commander.typecheck !== undefined) {
    ; //generate MASM will output errors and exit if there are any
}
else if ((Commander.symbolic || Commander.result) !== undefined) {
    setImmediate(() => {
        const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");
        if (massembly.invokeDecls.get((Commander.symbolic || Commander.result)) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }
        const entrypoint = massembly.invokeDecls.get((Commander.symbolic || Commander.result));
        const APIType = massembly.typeMap.get("NSCore::APIType");
        if (entrypoint.params.some((p) => !massembly.subtypeOf(massembly.typeMap.get(p.type), APIType))) {
            process.stderr.write("Only APITypes are supported for symbolic testing!!!\n");
            process.exit(1);
        }
        const sparams = smtdecls_emitter_1.SMTEmitter.emit(massembly, entrypoint, Commander.symbolic !== undefined);
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
            .replace(";;GET_MODEL;;", (Commander.result !== undefined) ? "(get-model)" : "");
        const smtpath = Path.join(scratchroot, "smt");
        FS.mkdirSync(smtpath, { recursive: true });
        const outfile = Path.join(smtpath, "scratch.smt2");
        FS.writeFileSync(outfile, contents);
    });
}
else {
    setImmediate(() => {
        const cpp_runtime = Path.join(binroot, "tooling/aot/runtime/");
        const cparams = cppdecls_emitter_1.CPPEmitter.emit(massembly, Commander.compile);
        const lsrc = FS.readdirSync(cpp_runtime).filter((name) => name.endsWith(".h") || name.endsWith(".cpp"));
        const linked = lsrc.map((fname) => {
            const contents = FS.readFileSync(Path.join(cpp_runtime, fname)).toString();
            let bcontents = contents
                .replace("//%%STATIC_STRING_DECLARE%%", cparams.STATIC_STRING_DECLARE)
                .replace("//%%STATIC_STRING_CREATE%%", cparams.STATIC_STRING_CREATE)
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
            if (bstart !== -1) {
                bcontents = bcontents.slice(0, bstart) + "//%%SPECIAL_NAME_BLOCK_BEGIN%%\n" + cparams.SPECIAL_NAME_BLOCK_BEGIN + "\n" + bcontents.slice(bend);
            }
            return { file: fname, contents: bcontents };
        });
        if (massembly.invokeDecls.get(Commander.compile) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }
        const entrypoint = massembly.invokeDecls.get(Commander.compile);
        if (entrypoint.params.some((p) => p.type !== "NSCore::Bool" && p.type !== "NSCore::Int" && p.type !== "NSCore::String")) {
            process.stderr.write("Only Bool/Int/String are supported for compilation testing!!!\n");
            process.exit(1);
        }
        const maincpp = "#include \"bsqruntime.h\"\n"
            + "namespace BSQ\n"
            + "{\n/*forward type decls*/\n"
            + cparams.TYPEDECLS_FWD
            + "\n\n/*ephemeral decls*/\n"
            + cparams.EPHEMERAL_LIST_DECLARE
            + "\n\n/*vable decls*/\n"
            + "\n\nclass BSQVable"
            + "{"
            + "\npublic:"
            + "\n  " + cparams.VFIELD_DECLS
            + "\n  " + cparams.VMETHOD_DECLS
            + "};"
            + "\n\n/*forward function decls*/\n"
            + cparams.FUNC_DECLS_FWD
            + "\n\n/*type decls*/\n"
            + cparams.TYPEDECLS
            + "\n\n/*typecheck decls*/\n"
            + cparams.TYPECHECKS
            + "\n\n/*function decls*/\n"
            + cparams.FUNC_DECLS
            + "}\n\n"
            + "using namespace BSQ;"
            + "\n\n/*main decl*/\n"
            + cparams.MAIN_CALL;
        linked.push({ file: "main.cpp", contents: maincpp });
        const cpppath = Path.join(scratchroot, "cpp");
        FS.mkdirSync(cpppath, { recursive: true });
        linked.forEach((fp) => {
            const outfile = Path.join(cpppath, fp.file);
            FS.writeFileSync(outfile, fp.contents);
        });
        const customsrc = Path.join(cpp_runtime, "bsqcustom");
        const custompath = Path.join(cpppath, "bsqcustom");
        FS.mkdirSync(custompath, { recursive: true });
        const csrc = FS.readdirSync(customsrc).filter((name) => name.endsWith(".h"));
        csrc.forEach((cf) => {
            const fromfile = Path.join(customsrc, cf);
            const outfile = Path.join(custompath, cf);
            const contents = FS.readFileSync(fromfile).toString();
            FS.writeFileSync(outfile, contents);
        });
    });
}
//# sourceMappingURL=runner.js.map