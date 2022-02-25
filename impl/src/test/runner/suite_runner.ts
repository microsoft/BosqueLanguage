//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { BuildApplicationMode, BuildLevel } from "../../ast/assembly";
import { CodeFileInfo } from "../../ast/parser";
import { MIRAssembly, MIRInvokeDecl, MIRType, PackageConfig } from "../../compiler/mir_assembly";
import { MIREmitter, MIRKeyGenerator } from "../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { ICPPEmitter } from "../../tooling/icpp/transpiler/icppdecls_emitter";
import { TranspilerOptions } from "../../tooling/icpp/transpiler/icpp_assembly";
import { VerifierOptions } from "../../tooling/checker/smt_exp";
import { SMTEmitter } from "../../tooling/checker/smtdecls_emitter";
import { ResolvedType } from "../../ast/resolved_type";
import { ICPPTest, SMT_TIMEOUT, SMT_VOPTS_CHK, SymTest, SymTestInternalChkShouldFail, TestResultKind } from "./test_decls";
import { enqueueICPPTests } from "./icpp_runner";
import { enqueueSymTests } from "./sym_runner";

import chalk from "chalk";

type Verbosity = "std" | "extra" | "max";
type Category = "sym" | "icpp" | "err" | "chk" | "fuzz" | "symexec";

const bosque_dir: string = Path.normalize(Path.join(__dirname, "../../../../"));

const icpppath: string = Path.normalize(Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : "")));

const smtruntime_path = Path.join(bosque_dir, "bin/tooling/checker/runtime/smtruntime.smt2");
const smtruntime = FS.readFileSync(smtruntime_path).toString();
const smtpath = Path.normalize(Path.join(bosque_dir, "/build/output/chk" + (process.platform === "win32" ? ".exe" : "")));

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = Path.join(bosque_dir, "bin/core");
        const corefiles = FS.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: FS.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

function generateMASMForICPP(buildlevel: BuildLevel, usercode: PackageConfig[], corecode: CodeFileInfo[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.Executable, [coreconfig, ...usercode], buildlevel, entrypoint);
}

function generateICPPAssembly(masm: MIRAssembly, istestbuild: boolean, topts: TranspilerOptions, entrypoints: MIRInvokeKey[]): [boolean, any] {
    try {
        return [true, ICPPEmitter.generateICPPAssembly(masm, istestbuild, topts, entrypoints)];
    } catch(e: any) {
        return [false, e.toString()];
    }
}

function generateMASMForSMT(usercode: PackageConfig[], corecode: CodeFileInfo[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["CHECK_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.ModelChecker, [coreconfig, ...usercode], "debug", entrypoint);
}

function generateSMTPayload(masm: MIRAssembly, istestbuild: boolean, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey): string | undefined {
    try {
        return SMTEmitter.generateSMTPayload(masm, istestbuild, smtruntime, vopts, errorTrgtPos, entrypoint);
    } catch(e) {
        return undefined;
    }
}

function generateCheckerPayload(masm: MIRAssembly, smtasm: string, timeout: number, entrypoint: MIRInvokeKey): any {
    return {smt2decl: smtasm, timeout: timeout, apimodule: masm.emitAPIInfo([entrypoint], true), "mainfunc": entrypoint};
}

function runtestsICPP(buildlevel: BuildLevel, istestbuild: boolean, topts: TranspilerOptions, usercode: PackageConfig[], entrypoint: {filename: string, namespace: string, names: string[]}[], verbose: Verbosity, category: Category[], dirs: string[] | undefined, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void, cbdone: (err: string | null) => void) {
    if(!category.includes("icpp")) {
        cbdone(null);
        return;
    }

    const corecode = workflowLoadCoreSrc();
    let testsuites: {testfile: string, test: ICPPTest, icppasm: any}[] = [];

    //check directory is enabled
    const filteredentry = entrypoint.filter((testpoint) => {
        return dirs === undefined || dirs.some((dname) => testpoint.filename.startsWith(dname));
    });

    for(let i = 0; i < filteredentry.length; ++i) {
        const {masm, errors} = generateMASMForICPP(buildlevel, usercode, corecode as CodeFileInfo[], filteredentry[i]);
        if(masm === undefined) {
            cbdone(errors.join("\n"));
            return;
        }

        const entrykeys = filteredentry[i].names.map((fname) => [fname, MIRKeyGenerator.generateFunctionKeyWNamespace(filteredentry[i].namespace, fname, new Map<string, ResolvedType>(), []).keyid]);
        const icppasm = generateICPPAssembly(masm, istestbuild, topts, entrykeys.map((kp) => kp[1]));
        if(!icppasm[0]) {
            cbdone("Failed to generate ICPP assembly");
        }

        const runnableentries = entrykeys.filter((ekey) => {
            const idcl = masm.invokeDecls.get(ekey[1]);
            if(idcl === undefined) {
                return false;
            }

            //check test type is enabled
            if(idcl.attributes.includes("errtest") && !category.includes("err")) {
                return false;
            }
            if(idcl.attributes.includes("chktest") && !category.includes("chk")) {
                return false;
            }

            //check fuzz is enabled
            if(idcl.params.length !== 0 && !category.includes("fuzz")) {
                return false;
            }

            return true;
        });

        const validtests = runnableentries.map((ekey) => {
            const idcl = masm.invokeDecls.get(ekey[1]) as MIRInvokeDecl;
            
            const rkind = idcl.attributes.includes("chktest") ? TestResultKind.ok : TestResultKind.errors;
            const fuzz = idcl.params.length !== 0;

            return {
                testfile: filteredentry[i].filename,
                test: new ICPPTest(rkind, fuzz, filteredentry[i].filename, filteredentry[i].namespace, ekey[0], ekey[1], idcl.params, masm.typeMap.get(idcl.resultType) as MIRType),
                icppasm: icppasm
            };
        });

        validtests.forEach((tt) => {
            testsuites.push(tt);
        });
    }

    if(testsuites.length === 0) {
        cbdone(null);
    }
    else {
        const tests = testsuites.map((ts) => {
            return {test: ts.test, icppasm: ts.icppasm};
        });

        enqueueICPPTests(icpppath, tests, verbose === "max", cbpre, cb, () => cbdone(null));
    }
}

function runtestsSMT(istestbuild: boolean, usercode: PackageConfig[], entrypoint: {filename: string, namespace: string, names: string[]}[], verbose: Verbosity, category: Category[], dirs: string[] | undefined, cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => void, cbdone: (err: string | null) => void) {
    if(!category.includes("sym")) {
        cbdone(null);
        return;
    }

    const corecode = workflowLoadCoreSrc();
    let testsuites: {testfile: string, test: ICPPTest, icppasm: any}[] = [];

    //check directory is enabled
    const filteredentry = entrypoint.filter((testpoint) => {
        return dirs === undefined || dirs.some((dname) => testpoint.filename.startsWith(dname));
    });

    for(let i = 0; i < filteredentry.length; ++i) {
        const {masm, errors} = generateMASMForSMT(usercode, corecode as CodeFileInfo[], {filename: filteredentry[i].filename, names: filteredentry[i].names});
        if(masm === undefined) {
            cbdone(errors.join("\n"));
            return;
        }

        const entrykeys = filteredentry[i].names.map((fname) => [fname, MIRKeyGenerator.generateFunctionKeyWNamespace(filteredentry[i].namespace, fname, new Map<string, ResolvedType>(), []).keyid]);
        const runnableentries = entrykeys.filter((ekey) => {
            const idcl = masm.invokeDecls.get(ekey[1]);
            if(idcl === undefined) {
                return false;
            }

            //check test type is enabled
            if(idcl.attributes.includes("errtest") && !category.includes("err")) {
                return false;
            }
            if(idcl.attributes.includes("chktest") && !category.includes("chk")) {
                return false;
            }

            //check symexec is enabled
            if(idcl.params.length === 0 && !category.includes("symexec")) {
                return false;
            }

            return true;
        });

        const noerrorpos = {file: "[INGORE]", line: -1, pos: -1};
        const validtests = runnableentries.map((ekey) => {
            const idcl = masm.invokeDecls.get(ekey[1]) as MIRInvokeDecl;
            
            if(idcl.attributes.includes("__chktest")) {
                const smtasm = generateSMTPayload(masm, istestbuild, SMT_VOPTS_CHK, noerrorpos, ekey[1]);
                if(smtasm === undefined) {
                    cbdone("Failed to generate SMT assembly");
                }
                
                const smtpayload = generateCheckerPayload(masm, smtasm as string, SMT_TIMEOUT, ekey[1]);
                return {
                    testfile: filteredentry[i].filename,
                    test: new SymTestInternalChkShouldFail(TestResultKind.ok, filteredentry[i].filename, filteredentry[i].namespace, ekey[0], ekey[1], idcl.params, masm.typeMap.get(idcl.resultType) as MIRType, noerrorpos),
                    cpayload: smtpayload
                };
            }
            else {
                const rkind = idcl.attributes.includes("chktest") ? TestResultKind.ok : TestResultKind.errors;

                xxxx;
            if(rkind === TestResultKind.ok) {
            const icppasm = generateSMTPayload(masm, istestbuild, vopts, entrykeys);
            if(!icppasm[0]) {
                cbdone("Failed to generate ICPP assembly");
            }

            return new ICPPTest(rkind, fuzz, filteredentry[i].filename, filteredentry[i].namespace, ekey, idcl.params, masm.typeMap.get(idcl.resultType) as MIRType);
            }
            else {
                xxxx;
            }
        }
        });

        validtests.forEach((tt) => {
            testsuites.push(tt);
        });
    }

    if(testsuites.length === 0) {
        cbdone(null);
    }
    else {
        const tests = testsuites.map((ts) => {
            return {test: ts.test, icppasm: ts.icppasm};
        });

        enqueueSymTests(icpppath, tests, verbose === "max", cbpre, cb, () => cbdone(null));
    }
}

function outputResultsAndExit(totaltime: number, totalicpp: number, failedicpp: {test: ICPPTest, info: string}[], erroricpp: {test: ICPPTest, info: string}[], totalsmt: number, failedsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[], errorsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[]) {
    process.stdout.write(`Ran ${totalicpp} executable tests in ${totaltime}s ...\n`);
    if (failedicpp.length === 0 && erroricpp.length === 0) {
        process.stdout.write(chalk.bold("All executable tests pass!\n\n"));
    }
    else {
        if(failedicpp.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${failedicpp.length}`) + " " + chalk.red("executable test failures") + "\n");

            const rstr = failedicpp.map((tt) => `${tt.test.namespace}::${tt.test.invk} -- "${tt.info}"`).join("\n  ");
            process.stdout.write(rstr + "\n\n");
        }

        if(erroricpp.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${erroricpp.length}`) + " " + chalk.magenta("executable test errors") + "\n");

            const rstr = erroricpp.map((tt) => `${tt.test.namespace}::${tt.test.invk} -- "${tt.info}"`).join("\n  ");
            process.stdout.write(rstr + "\n\n");
        }
    }

    process.stdout.write(`Ran ${totalsmt} SMT tests...\n`);
    if (failedsmt.length === 0 && errorsmt.length === 0) {
        process.stdout.write(chalk.bold("All executable tests pass!\n\n"));
    }
    else {
        if(failedsmt.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${failedsmt.length}`) + " " + chalk.red("executable test failures") + "\n");

            const rstr = failedsmt.map((tt) => `${tt.test.namespace}::${tt.test.invk} -- "${tt.info}"`).join("\n  ");
            process.stdout.write(rstr + "\n\n");
        }

        if(errorsmt.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${errorsmt.length}`) + " " + chalk.magenta("executable test errors") + "\n");

            const rstr = errorsmt.map((tt) => `${tt.test.namespace}::${tt.test.invk} -- "${tt.info}"`).join("\n  ");
            process.stdout.write(rstr + "\n\n");
        }
    }

    if(failedicpp.length !== 0 || erroricpp.length !== 0 || failedsmt.length !== 0 || errorsmt.length !== 0) {
        process.exit(1);
    }

    process.exit(0);
}

function loadUserPackageSrc(files: string[], macrodefs: string[], globalmacros: string[]): PackageConfig | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            code.push({ srcpath: realpath, filename: files[i], contents: FS.readFileSync(realpath).toString() });
        }

        return new PackageConfig([...macrodefs, ...globalmacros], code);
    }
    catch (ex) {
        return undefined;
    }
}

function loadEntryPointInfo(files: string[]): {filename: string, namespace: string, names: string[]}[] | undefined {
    try {
        let epi: {filename: string, namespace: string, names: string[]}[] = [];

        for(let i = 0; i < files.length; ++i) {
            const contents = FS.readFileSync(files[i]).toString();

            const namespacere = /namespace([ \t]+)(?<nsstr>(([A-Z][_a-zA-Z0-9]+)::)*([A-Z][_a-zA-Z0-9]+));/;
            const entryre = /(entrypoint|chktest|errtest|__chktest)(\s+)function(\s+)(?<fname>([_a-z]|([_a-z][_a-zA-Z0-9]*[a-zA-Z0-9])))(\s*)\(/y;
            
            const ns = namespacere.exec(contents);
            if(ns === null || ns.groups === undefined || ns.groups.nsstr === undefined) {
                return undefined;
            }
            const nsstr = ns.groups.nsstr;

            let names: string[] = [];
            let mm: RegExpExecArray | null = null;
            entryre.lastIndex = 0;
            mm = entryre.exec(contents);
            while(mm !== null) {
                if(mm.groups === undefined || mm.groups.fname === undefined) {
                    return undefined;
                }
                names.push(mm.groups.fname);

                entryre.lastIndex += mm[0].length;
                mm = entryre.exec(contents);
            }

            epi.push({filename: files[i], namespace: nsstr, names: names})
        }

        return epi;
    }
    catch (ex) {
        return undefined;
    }
}

function runtests(packageloads: {srcfiles: string[], macros: string[]}[], globalmacros: string[], entrypointfiles: string[], buildlevel: BuildLevel, istestbuild: boolean, topts: TranspilerOptions, vopts: VerifierOptions, files: string[], verbose: Verbosity, category: Category[], dirs: string[]) {
    let icppdone = false;
    let totalicpp = 0;
    let failedicpp: {test: ICPPTest, info: string}[] = [];
    let erroricpp: {test: ICPPTest, info: string}[] = [];

    let smtdone = false;
    let totalsmt = 0;
    let failedsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[] = [];
    let errorsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[] = [];

    const start = new Date();

    const usersrc = packageloads.map((psrc) => loadUserPackageSrc(psrc.srcfiles, psrc.macros, globalmacros));
    if(usersrc.includes(undefined)) {
        process.stdout.write(chalk.red("Failure loading user packages\n"));
        process.exit(1);
    }

    const entrypoints = loadEntryPointInfo(entrypointfiles);
    if(entrypoints === undefined) {
        process.stdout.write(chalk.red("Failure loading entrypoints\n"));
        process.exit(1);
    }

    const cbpre_icpp = (tt: ICPPTest) => {
        process.stdout.write(`Starting ${tt.namespace}::${tt.fname}...\n`);
    };
    const cb_icpp = (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, info?: string) => {
        if(result === "pass") {
            ;
        }
        else if(result === "fail") {
            failedicpp.push({test: test, info: info || "[Missing Info]"});
        }
        else {
            erroricpp.push({test: test, info: info || "[Missing Info]"});
        }

        if(verbose !== "std") {
            let rstr = "";
            if(result === "pass") {
                rstr = chalk.green("pass");
            }
            else if(result === "fail") {
                rstr = chalk.red("fail");
            }
            else {
                rstr = chalk.magenta("error");
            }

            process.stdout.write(`Executable test ${test.namespace}::${test.fname} completed with ${rstr} in ${end.getTime() - start.getTime()}ms\n`);
        }
    };
    const cbdone_icpp = (err: string | null) => {
        if(err !== null) {
            process.stdout.write(chalk.red("Hard failure loading ICPP tests --\n"));
            process.stdout.write("  " + err + "\n");
            process.exit(1);
        }
        else {
            icppdone = true;
            if(smtdone) {
                const end = new Date();
                const totaltime = (end.getTime() - start.getTime()) / 1000;
                outputResultsAndExit(totaltime, totalicpp, failedicpp, erroricpp, totalsmt, failedsmt, errorsmt);
            }
        }
    };

    runtestsICPP(buildlevel, istestbuild, topts, usersrc as PackageConfig[], entrypoints, verbose, category, dirs, cbpre_icpp, cb_icpp, cbdone_icpp);

    xxxx;
}