//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import * as Commander from "commander";

import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl, MIRType } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { CPPEmitter } from "../tooling/aot/cppdecls_emitter";
import { SMTEmitter } from "../tooling/bmc/smtdecls_emitter";

const scratchroot = Path.normalize(Path.join(__dirname, "../scratch/"));
const binroot = Path.normalize(Path.join(__dirname, "../"));

function generateMASM(files: string[], corelibpath: string): MIRAssembly {
    let code: { relativePath: string, contents: string }[] = [];
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

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), true, true, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
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

if(Commander.typecheck !== undefined) {
    ; //generate MASM will output errors and exit if there are any
}
else if ((Commander.symbolic || Commander.result) !== undefined) {
    setImmediate(() => {
        const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");

        if(massembly.invokeDecls.get((Commander.symbolic || Commander.result)) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }

        const entrypoint = massembly.invokeDecls.get((Commander.symbolic || Commander.result)) as MIRInvokeBodyDecl;
        const PODType = massembly.typeMap.get("NSCore::POD") as MIRType;
        if (entrypoint.params.some((p) => !massembly.subtypeOf(massembly.typeMap.get(p.type) as MIRType, PODType))) {
            process.stderr.write("Only PODTypes are supported for symbolic testing!!!\n");
            process.exit(1);
        }

        const sparams = SMTEmitter.emit(massembly, entrypoint, 4, Commander.symbolic !== undefined);
        const lsrc = FS.readFileSync(smt_runtime).toString();
        const contents = lsrc
            .replace(";;FIXED_TUPLE_DECLS_FWD;;", "  " + sparams.fixedtupledecls_fwd)
            .replace(";;FIXED_RECORD_DECLS_FWD;;", "  " + sparams.fixedrecorddecls_fwd)
            .replace(";;FIXED_TUPLE_DECLS;;", "  " + sparams.fixedtupledecls)
            .replace(";;FIXED_RECORD_DECLS;;", "  " + sparams.fixedrecorddecls)
            .replace(";;NOMINAL_DECLS_FWD;;", "  " + sparams.typedecls_fwd)
            .replace(";;NOMINAL_DECLS;;", "  " + sparams.typedecls)
            .replace(";;CONCEPT_SUBTYPE_RELATION_DECLARE;;", sparams.conceptSubtypeRelation)
            .replace(";;NOMINAL_RESULT_FWD;;", "  " + sparams.resultdecls_fwd)
            .replace(";;NOMINAL_RESULT;;", "  " + sparams.resultdecls)
            .replace(";;SUBTYPE_DECLS;;", sparams.typechecks)
            .replace(";;FUNCTION_DECLS;;", "  " + sparams.function_decls)
            .replace(";;ARG_VALUES;;", sparams.args_info)
            .replace(";;INVOKE_ACTION;;", sparams.main_info)
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

        const cparams = CPPEmitter.emit(massembly, Commander.compile);
        const lsrc = FS.readdirSync(cpp_runtime).filter((name) => name.endsWith(".h") || name.endsWith(".cpp"));
        const linked = lsrc.map((fname) => {
            const contents = FS.readFileSync(Path.join(cpp_runtime, fname)).toString();
            const bcontents = contents
                .replace("//%%NOMINAL_TYPE_ENUM_DECLARE", "    " + cparams.nominalenums)
                .replace("//%%NOMINAL_TYPE_DISPLAY_NAMES", cparams.nomnialdisplaynames)
                .replace("//%%CONCEPT_SUBTYPE_RELATION_DECLARE", "    " + cparams.conceptSubtypeRelation)
                .replace("//%%STATIC_STRING_DECLARE%%", "  " + cparams.conststring_declare)
                .replace("//%%STATIC_STRING_CREATE%%", "  " + cparams.conststring_create)
                .replace("//%%STATIC_INT_DECLARE%%", "  " + cparams.constint_declare)
                .replace("//%%STATIC_INT_CREATE%%", "  " + cparams.constint_create)
                .replace("//%%PROPERTY_ENUM_DECLARE", "    " + cparams.propertyenums)
                .replace("//%%PROPERTY_NAMES", "  " + cparams.propertynames)
                .replace("//%%KNOWN_PROPERTY_LIST_DECLARE", "    " + cparams.known_property_lists_declare)
                .replace("//%%VFIELD_DECLS", "    " + cparams.vfield_decls)
                .replace("//%%VMETHOD_DECLS", "  " + cparams.vmethod_decls);

            return { file: fname, contents: bcontents };
        });

        if(massembly.invokeDecls.get(Commander.compile) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }

        const entrypoint = massembly.invokeDecls.get(Commander.compile) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => p.type !== "NSCore::Bool" && p.type !== "NSCore::Int" && p.type !== "NSCore::String")) {
            process.stderr.write("Only Bool/Int/String are supported for compilation testing!!!\n");
            process.exit(1);
        }

        const maincpp = "#include \"bsqruntime.h\"\n"
            + "namespace BSQ\n"
            + "{\n/*forward type decls*/\n"
            + cparams.typedecls_fwd
            + "\n\n/*forward function decls*/\n"
            + cparams.funcdecls_fwd
            + "\n\n/*type decls*/\n"
            + cparams.typedecls
            + "\n\n/*typecheck decls*/\n"
            + cparams.typechecks
            + "\n\n/*function decls*/\n"
            + cparams.funcdecls
            + "}\n\n"
            + "using namespace BSQ;"
            + "\n\n/*main decl*/\n"
            + cparams.maincall
        linked.push({ file: "main.cpp", contents: maincpp });

        const cpppath = Path.join(scratchroot, "cpp");
        FS.mkdirSync(cpppath, { recursive: true });

        linked.forEach((fp) => {
            const outfile = Path.join(cpppath, fp.file);
            FS.writeFileSync(outfile, fp.contents);
        });
    });
}
