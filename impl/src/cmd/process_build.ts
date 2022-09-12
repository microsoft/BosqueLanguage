//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";

import * as chalk from "chalk";
const fsextra = require("fs-extra");

import { help, loadUserSrc, tryLoadPackage, extractEntryPoint, extractConfig, extractOutput, extractEntryPointsAll, DEFAULT_SMALL_MODEL_ONLY } from "./args_load";
import { ConfigBuild, Package } from "./package_load";
import { PackageConfig, SymbolicActionMode } from "../compiler/mir_assembly";
import { workflowEmitICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";
import { generateStandardVOpts, workflowEmitToFile } from "../tooling/checker/smt_workflows";

import { workflowEmitMorphirElmFile } from "../tooling/morphir/bsqtranspiler/morphir_workflows";

function processBuildActionBytecode(args: string[]) {
    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[1]) === ".json") {
        workingdir = path.dirname(path.resolve(args[1]));
        pckg = tryLoadPackage(path.resolve(args[1]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("build");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("build");
        process.exit(1);
    }

    const entrypoints = extractEntryPointsAll(workingdir, pckg.src.entrypoints);
    if (entrypoints === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("build");
        process.exit(1);
    }

    const output = extractOutput(workingdir, args);
    if (output === undefined) {
        process.stderr.write(chalk.red("Could not parse 'output' option\n"));

        help("build");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    try {
        fsextra.ensureDirSync(output.path);
    }
    catch (ex) {
        process.stderr.write(chalk.red("Could not create 'output' directory\n"));

        help("build");
        process.exit(1);
    }

    //bosque build bytecode [package_path.json] [--config cname] [--output out]
    workflowEmitICPPFile(path.join(output.path, cfg.name + ".json"), userpackage, true, cfg.buildlevel, false, {}, entrypoints);
}

function processBuildActionSymbolic(args: string[]) {
    const timeout = 10000;
    const noerr = { file: "[No Error Trgt]", line: -1, pos: -1 };

    let smtonly = args.includes("--smtlib");
    let vopts = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);

    if (args[1] === "chk") {
        vopts = generateStandardVOpts(SymbolicActionMode.ChkTestSymbolic);
    }
    else if (args[1] === "eval") {
        vopts = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);
    }
    else {
        process.stderr.write(chalk.red("Could not parse symbolic build mode\n"));

        help("build");
        process.exit(1);
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[smtonly ? 3 : 2]) === ".json") {
        workingdir = path.dirname(path.resolve(args[smtonly ? 3 : 2]));
        pckg = tryLoadPackage(path.resolve(args[smtonly ? 3 : 2]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("build");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("build");
        process.exit(1);
    }

    const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
    if (entrypoint === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("build");
        process.exit(1);
    }

    const output = extractOutput(workingdir, args);
    if (output === undefined) {
        process.stderr.write(chalk.red("Could not parse 'output' option\n"));

        help("build");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    try {
        fsextra.ensureDirSync(output.path);
    }
    catch (ex) {
        process.stderr.write(chalk.red("Could not create 'output' directory\n"));

        help("build");
        process.exit(1);
    }

    //bosque build smt [err|chk|eval] [package_path.json] [--config cname] [--output out]
    if (smtonly) {
        workflowEmitToFile(path.join(output.path, cfg.name + ".smt2"), userpackage, cfg.buildlevel, DEFAULT_SMALL_MODEL_ONLY, false, timeout, vopts, entrypoint, noerr, true);
    }
    else {
        workflowEmitToFile(path.join(output.path, cfg.name + ".json"), userpackage, cfg.buildlevel, DEFAULT_SMALL_MODEL_ONLY, false, timeout, vopts, entrypoint, noerr, false);
    }
}

function processBuildActionNode(args: string[]) {
    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[1]) === ".json") {
        workingdir = path.dirname(path.resolve(args[1]));
        pckg = tryLoadPackage(path.resolve(args[1]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("build");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("build");
        process.exit(1);
    }

    const output = extractOutput(workingdir, args);
    if (output === undefined) {
        process.stderr.write(chalk.red("Could not parse 'output' option\n"));

        help("build");
        process.exit(1);
    }

    //bosque build node [package_path.json] [--config cname] [--output out]
    process.stderr.write(chalk.red("Transpile to NPM module not implemented yet.\n"));
    process.exit(1);
}

function processBuildActionBosqueToMorphir(args: string[]) {
    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[1]) === ".json") {
        workingdir = path.dirname(path.resolve(args[1]));
        pckg = tryLoadPackage(path.resolve(args[1]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("build");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigBuild>(args, pckg, workingdir, "build");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("build");
        process.exit(1);
    }

    const entrypoints = extractEntryPointsAll(workingdir, pckg.src.entrypoints);
    if (entrypoints === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("build");
        process.exit(1);
    }

    const output = extractOutput(workingdir, args);
    if (output === undefined) {
        process.stderr.write(chalk.red("Could not parse 'output' option\n"));

        help("build");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    try {
        fsextra.ensureDirSync(output.path);
    }
    catch (ex) {
        process.stderr.write(chalk.red("Could not create 'output' directory\n"));

        help("build");
        process.exit(1);
    }

    //bosque build bytecode [package_path.json] [--config cname] [--output out]
    workflowEmitMorphirElmFile(path.join(output.path, cfg.name + ".elm"), userpackage, cfg.buildlevel, false, entrypoints);
}

function processBuildAction(args: string[]) {
    if(args.length === 1) {
        if(args[0] === "morphir") {
            args.push("./morphir.json");
        }
        else {
            args.push("./package.json");
        }
    }

    if(args[0] === "node") {
        processBuildActionNode(args);
    }
    else if(args[0] === "bytecode") {
        processBuildActionBytecode(args);
    }
    else if(args[0] === "sym") {
        processBuildActionSymbolic(args);
    }
    else if(args[0] === "morphir") {
        processBuildActionBosqueToMorphir(args);
    }
    else {
        process.stderr.write(chalk.red(`Unknown build target '${args[0]}'\n`));

        help("build");
        process.exit(1);
    }
}

export {
    processBuildAction
};
