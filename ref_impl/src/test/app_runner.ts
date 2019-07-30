//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { Interpreter } from "../interpreter/interpreter";
import { ValueOps } from "../interpreter/value";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly } from "../compiler/mir_assembly";

function runApp(app: string) {
    process.stdout.write("Reading app code...\n");

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let files: { relativePath: string, contents: string }[] = [];
    try {
        // All core files, collection files, etc.
        const core_dir = Path.join(bosque_dir, "src/core/");
        const core_files = FS.readdirSync(core_dir);
        core_files.forEach(file => {
            const abs_file = Path.join(core_dir, file);
            files.push({ relativePath: abs_file, contents: FS.readFileSync(abs_file).toString() });
        });

        // Entrypoint file
        const appdir = app;
        const appdata = FS.readFileSync(appdir).toString();
        files.push({ relativePath: appdir, contents: appdata });
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

    process.stdout.write("Executing app code...\n");

    const asm = masm as MIRAssembly;
    const ip = new Interpreter(asm, true, true, true);
    let res: any = undefined;
    try {
        res = ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSMain", "main", []));
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        process.exit(1);
    }

    process.stdout.write(`Done with -- ${res}\n`);
    process.exit(0);
}

if (!process.argv[2]) {
    process.stdout.write(chalk.red("Error -- Please specify a source file as an argument\n"));
    process.exit(1);
}

////
//Entrypoint

setImmediate(() => runApp(process.argv[2]));
