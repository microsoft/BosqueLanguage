//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly } from "../compiler/mir_assembly";

import * as Commander from "commander";

function compile(files: string[], trgt: string) {
    process.stdout.write("Reading app code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
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

    process.stdout.write("Compiling assembly...\n");

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    process.stdout.write(`Writing assembly to ${trgt}...\n`);

    FS.writeFileSync(trgt, JSON.stringify((masm as MIRAssembly).jemit(), undefined, 4));

    process.stdout.write(`Done!\n`);
    process.exit(0);
}

Commander
.usage("--bytecode [--output file] <file ...>")
.option("-j --json", "Compile to json bytecode assembly")
.option("-o --output [file]", "Optional output file target");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

if (Commander.bytecode === undefined) {
    process.stdout.write("Error -- Please specify a compiler target (--assembly)");
    process.exit(1);
}

setImmediate(() => compile(Commander.args, Commander.output || "a.json"));
