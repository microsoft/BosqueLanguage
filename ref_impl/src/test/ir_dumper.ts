//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody } from "../compiler/mir_ops";

function runApp(app: string) {
    process.stdout.write("Reading app code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let files: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        const appdir = app;
        const appdata = FS.readFileSync(appdir).toString();

        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }

        process.exit(1);
    }

    try {
        process.stdout.write("Generating IR...\n");

        const irv = (masm as MIRAssembly).functionDecls.get(process.argv[3]) as MIRFunctionDecl;
        const dgml = (irv.invoke.body as MIRBody).dgmlify(irv.fkey);

        process.stdout.write("Writing IR...\n");
        FS.writeFileSync("mir_ir.dgml", dgml);
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        process.exit(1);
    }

    process.stdout.write("Success, ir output in mir_ir.dgml\n");
    process.exit(0);
}

if (!process.argv[3]) {
    process.stdout.write(chalk.red("Error -- Please specify a source file and invokeid as arguments"));
    process.exit(1);
}

////
//Entrypoint

setImmediate(() => runApp(process.argv[2]));
