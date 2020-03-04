//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { execSync } from "child_process";

import * as Commander from "commander";

import { MIRAssembly, PackageConfig, MIRInvokeBodyDecl, MIRType } from "../../compiler/mir_assembly";
import { MIREmitter } from "../../compiler/mir_emitter";
import { CPPEmitter } from "../../tooling/aot/cppdecls_emitter";
import chalk from "chalk";

const scratchroot = Path.normalize(Path.join(__dirname, "../../scratch/"));
const binroot = Path.normalize(Path.join(__dirname, "../../"));

function generateMASM(files: string[], blevel: "debug" | "test" | "release", corelibpath: string): MIRAssembly {
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
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), blevel, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    return masm as MIRAssembly;
}

Commander
    .option("-e --entrypoint [entrypoint]", "Entrypoint of the exe", "NSMain::main")
    .option("-o --outfile [outfile]", "Optional name of the output exe", (process.platform === "win32") ? "a.exe" : "a.out")
    .option("-c --compiler [compiler]", "Compiler to use", (process.platform === "win32") ? "\"C:\\Program Files\\LLVM\\bin\\clang.exe\"" : "g++")
    .option("-l --level [level]", "Build level version", "debug");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write(chalk.red("Error -- Please specify at least one source file as an argument\n"));
    process.exit(1);
}

if(!["debug", "test", "release"].includes(Commander.level)) {
    process.stdout.write(chalk.red("Error -- Valid build levels are 'debug', 'test', and 'release'\n"));
    process.exit(1);
}

process.stdout.write(`Compiling Bosque sources in files:\n${Commander.args.join("\n")}\n...\n`);
const massembly = generateMASM(Commander.args, Commander.level, Path.normalize(Path.join(__dirname, "../../", "core/direct/")));

setImmediate(() => {
    process.stdout.write(`Transpiling Bosque assembly to C++ with entrypoint of ${Commander.entrypoint}...\n`);
    const cpp_runtime = Path.join(binroot, "tooling/aot/runtime/");

    try {
        const cparams = CPPEmitter.emit(massembly, Commander.entrypoint);
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
            if(bstart !== -1) {
                bcontents = bcontents.slice(0, bstart) + "//%%SPECIAL_NAME_BLOCK_BEGIN%%\n" + cparams.SPECIAL_NAME_BLOCK_BEGIN + "\n" + bcontents.slice(bend);
            }

            return { file: fname, contents: bcontents };
        });

        if (massembly.invokeDecls.get(Commander.entrypoint) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }

        const entrypoint = massembly.invokeDecls.get(Commander.entrypoint) as MIRInvokeBodyDecl;
        if (entrypoint.params.some((p) => !massembly.subtypeOf(massembly.typeMap.get(p.type) as MIRType, massembly.typeMap.get("NSCore::APIValue") as MIRType))) {
            process.stderr.write("Only APIValue types are supported as inputs of Bosque programs.\n");
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
            + "\n{"
            + "\npublic:"
            + "\n  " + cparams.VFIELD_DECLS
            + "\n  " + cparams.VMETHOD_DECLS
            + "\n};"
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
            + cparams.MAIN_CALL
        linked.push({ file: "main.cpp", contents: maincpp });

        process.stdout.write(`Writting C++ files...\n`);
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

        process.stdout.write(`Compiling C++ code with ${Commander.compiler} into exe file "${chalk.bold(Commander.outfile)}"...\n`);
        let buildOpts = "";
        if(Commander.level === "debug") {
            buildOpts = " -g -DBDEBUG";
        }
        else if (Commander.level === "test") {
            buildOpts = " -g -DBDEBUG -Os"
        }
        else {
            buildOpts = " -Os -march=native"
        }

        execSync(`${Commander.compiler}${buildOpts} -std=c++14 -o ${Commander.outfile} ${cpppath}/*.cpp`);
    }
    catch (ex) {
        process.stderr.write(chalk.red(`Error -- ${ex}\n`));
    }
    process.stdout.write(chalk.green(`Done with executable -- ${Commander.outfile}\n`));
});
