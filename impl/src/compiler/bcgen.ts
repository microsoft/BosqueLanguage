//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly } from "../compiler/mir_assembly";

import * as Commander from "commander";

function compile(files: string[], functionalize: boolean, outfile: string, dgf: string | undefined) {
    process.stdout.write("Reading app code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../"));
    let code: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "core/", "verify");
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
        process.stdout.write(`Read failed with exception -- ${ex}\n`);
        process.exit(1);
    }

    process.stdout.write("Compiling assembly...\n");

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", {namespace: "NSMain", names: ["main"]}, functionalize, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    process.stdout.write(`Writing assembly to ${outfile}.json...\n`);
    FS.writeFileSync(outfile + ".json", JSON.stringify((masm as MIRAssembly).jemit(), undefined, 4));

    if(dgf !== undefined) {
        const iiv = (masm as MIRAssembly).invokeDecls.get(dgf);
        if(iiv === undefined) {
            process.stdout.write(`Could not find body for ${dgf}...\n`);
        }
        else {
            process.stdout.write(`Writing assembly to ${outfile}.dgml...\n`);

            const sigargs = iiv.params.map((p) => `${p.name}: ${p.type}`);
            if(iiv.masksize !== 0) {
                sigargs.push("#maskparam#");
            }

            const siginfo = `${iiv.key}(${sigargs.join(", ")}): ${iiv.resultType}`;
            FS.writeFileSync(outfile + ".dgml", iiv.body.dgmlify(siginfo));
        }
    }

    process.stdout.write(`Done!\n`);
    process.exit(0);
}

Commander
.usage("[--output file] <file ...>")
.option("-f --functionalize [boolean]")
.option("-d --dgml [function]", "Optional function to output in DGML format")
.option("-o --output [file]", "Optional output file target");

Commander.parse(process.argv);

if (Commander.args.length === 0) {
    process.stdout.write("Error -- Please specify at least one source file as an argument");
    process.exit(1);
}

setImmediate(() => compile(Commander.args, !!Commander.functionalize, Commander.output || "a", Commander.dgml));
