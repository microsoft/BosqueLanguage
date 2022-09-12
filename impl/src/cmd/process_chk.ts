//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";

import * as chalk from "chalk";

import { DEFAULT_SMALL_MODEL_ONLY, extractConfig, help, loadUserSrc, tryLoadPackage } from "./args_load";
import { ConfigAppTest, ConfigTest, Package } from "./package_load";
import { runtests } from "../test/runner/suite_runner";

function processTestAction(args: string[]) {
    if(args.length === 0) {
        args.push("./package.json");
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("test");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigTest>(args, pckg, workingdir, "test");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("test");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.testfiles, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const userpackage = [{ macros: [...cfg.macros, ...cfg.globalmacros], files: srcfiles }];

    let dirs: string[] = ["*"];
    if (Array.isArray(cfg.params.dirs)) {
        dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
    }

    //bosque test [package_path.json] [--config cname]

    runtests(userpackage, [], pckg.src.testfiles.map((tf) => path.resolve(workingdir, tf.path)), cfg.buildlevel, DEFAULT_SMALL_MODEL_ONLY, true, {}, "extra", cfg.params.flavors, dirs);
}

function processAppTestAction(args: string[]) {
    if(args.length === 0) {
        args.push("./package.json");
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("apptest");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigAppTest>(args, pckg, workingdir, "apptest");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("apptest");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const userpackage = [{ macros: [...cfg.macros, ...cfg.globalmacros], files: srcfiles }];

    let dirs: string[] = ["*"];
    if (Array.isArray(cfg.params.dirs)) {
        dirs = cfg.params.dirs.map((pd) => path.resolve(workingdir, pd.path));
    }

    //bosque apptest [package_path.json] [--config cname]

    runtests(userpackage, [], pckg.src.entrypoints.map((ef) => path.resolve(workingdir, ef.path)), cfg.buildlevel, true, DEFAULT_SMALL_MODEL_ONLY, {}, "extra", cfg.params.flavors, dirs);
}

export {
    processTestAction, processAppTestAction
};
