//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";

import { BuildApplicationMode, BuildLevel } from "../../ast/assembly";
import { cleanCommentsStringsFromFileContents, CodeFileInfo } from "../../ast/parser";
import { MIRAssembly, MIRInvokeDecl, MIRType, PackageConfig } from "../../compiler/mir_assembly";
import { MIREmitter, MIRKeyGenerator } from "../../compiler/mir_emitter";
import { MIRInvokeKey } from "../../compiler/mir_ops";
import { ICPPEmitter } from "../../tooling/icpp/transpiler/icppdecls_emitter";
import { TranspilerOptions } from "../../tooling/icpp/transpiler/icpp_assembly";
import { VerifierOptions } from "../../tooling/checker/smt_exp";
import { SMTEmitter } from "../../tooling/checker/smtdecls_emitter";
import { ResolvedType } from "../../ast/resolved_type";
import { ICPPTest, SMT_TIMEOUT, SMT_VOPTS_CHK, SMT_VOPTS_ERR, SymTest, SymTestInternalChkShouldFail, TestResultKind } from "./test_decls";
import { enqueueICPPTests } from "./icpp_runner";
import { enqueueSymTests } from "./sym_runner";

import * as chalk from "chalk";

type Verbosity = "std" | "extra" | "max";
type Category = "sym" | "icpp" | "err" | "chk" | "fuzz" | "symexec";

const bosque_dir: string = Path.join(__dirname, "../../../");

const icpppath: string = Path.join(bosque_dir, "/build/output/icpp" + (process.platform === "win32" ? ".exe" : ""));

const smtruntime_path = Path.join(bosque_dir, "bin/tooling/checker/runtime/smtruntime.smt2");
const smtruntime = FS.readFileSync(smtruntime_path).toString();
const smtpath = Path.join(bosque_dir, "/build/output/chk" + (process.platform === "win32" ? ".exe" : ""));

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

function generateMASMForICPP(buildlevel: BuildLevel, usercode: PackageConfig[], corecode: CodeFileInfo[], entrypointkeys: MIRInvokeKey[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.Executable, [coreconfig, ...usercode], buildlevel, true, entrypointkeys, entrypoint);
}

function generateICPPAssembly(srcCode: { fname: string, contents: string }[], masm: MIRAssembly, istestbuild: boolean, topts: TranspilerOptions, entrypoints: MIRInvokeKey[]): [boolean, any] {
    try {
        return [true, ICPPEmitter.generateICPPAssembly(srcCode, masm, istestbuild, topts, entrypoints)];
    } catch(e: any) {
        return [false, e.toString()];
    }
}

function generateMASMForSMT(usercode: PackageConfig[], corecode: CodeFileInfo[], buildlevel: BuildLevel, smallmodelonly: boolean, entrypointkeys: MIRInvokeKey[], entrypoint: {filename: string, names: string[]}): { masm: MIRAssembly | undefined, errors: string[] } {
    let smtmacros = ["CHECK_LIBS"];
    if(smallmodelonly) {
        smtmacros.push("CHK_SMALL_ONLY");
    }

    const coreconfig = new PackageConfig(smtmacros, corecode);

    return MIREmitter.generateMASM(BuildApplicationMode.ModelChecker, [coreconfig, ...usercode], buildlevel, true, entrypointkeys, entrypoint);
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

function runtestsICPP(buildlevel: BuildLevel, istestbuild: boolean, topts: TranspilerOptions, usercode: PackageConfig[], entrypoint: {filename: string, namespace: string, names: string[]}[], verbose: Verbosity, category: Category[], dirs: string[], cbpre: (test: ICPPTest) => void, cb: (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => void, cbdone: (err: string | null) => void) {
    if(!category.includes("icpp")) {
        cbdone(null);
        return;
    }

    const corecode = workflowLoadCoreSrc();
    let testsuites: {testfile: string, test: ICPPTest, apiinfo: any, icppasm: any}[] = [];

    //check directory is enabled
    const filteredentry = entrypoint.filter((testpoint) => {
        if(testpoint.names.length === 0) {
            return false;
        }

        return dirs.includes("*") || dirs.some((dname) => testpoint.filename.startsWith(dname));
    });

    for(let i = 0; i < filteredentry.length; ++i) {
        const entrykeys = filteredentry[i].names.map((fname) => [fname, MIRKeyGenerator.generateFunctionKeyWNamespace(filteredentry[i].namespace, fname, new Map<string, ResolvedType>(), []).keyid]);
        
        const {masm, errors} = generateMASMForICPP(buildlevel, usercode, corecode as CodeFileInfo[], entrykeys.map((kp) => kp[1]), filteredentry[i]);
        if(masm === undefined) {
            cbdone(errors.join("\n"));
            return;
        }

        const icppasm = generateICPPAssembly([], masm, istestbuild, topts, entrykeys.map((kp) => kp[1]));
        if(!icppasm[0]) {
            cbdone("Failed to generate ICPP assembly");
        }

        const apiinfo = masm.emitAPIInfo(entrykeys.map((ekey) => ekey[1]), istestbuild);

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
                apiinfo: apiinfo,
                icppasm: icppasm[1]
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
            return {test: ts.test, apiinfo: ts.apiinfo, icppasm: ts.icppasm};
        });

        enqueueICPPTests(icpppath, tests, verbose === "max", cbpre, cb, () => cbdone(null));
    }
}

function runtestsSMT(buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, usercode: PackageConfig[], entrypoint: {filename: string, namespace: string, names: string[]}[], verbose: Verbosity, category: Category[], dirs: string[], cbpre: (test: SymTest | SymTestInternalChkShouldFail) => void, cb: (result: "pass" | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smttime: number, info?: string) => void, cbdone: (err: string | null) => void) {
    if(!category.includes("sym")) {
        cbdone(null);
        return;
    }

    const corecode = workflowLoadCoreSrc();
    let testsuites: {testfile: string, test: SymTest | SymTestInternalChkShouldFail, cpayload: any}[] = [];

    //check directory is enabled
    const filteredentry = entrypoint.filter((testpoint) => {
        if(testpoint.names.length === 0) {
            return false;
        }
        
        return dirs.includes("*") || dirs.some((dname) => testpoint.filename.startsWith(dname));
    });

    for(let i = 0; i < filteredentry.length; ++i) {
        const entrykeys = filteredentry[i].names.map((fname) => [fname, MIRKeyGenerator.generateFunctionKeyWNamespace(filteredentry[i].namespace, fname, new Map<string, ResolvedType>(), []).keyid]);
        
        const {masm, errors} = generateMASMForSMT(usercode, corecode as CodeFileInfo[], buildlevel, smallmodelonly, entrykeys.map((kp) => kp[1]), {filename: filteredentry[i].filename, names: filteredentry[i].names});
        if(masm === undefined) {
            cbdone(errors.join("\n"));
            return;
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

            //check symexec is enabled
            if(idcl.params.length === 0 && !category.includes("symexec")) {
                return false;
            }

            return true;
        });

        const noerrorpos = {file: "[INGORE]", line: -1, pos: -1};
        runnableentries.forEach((ekey) => {
            const idcl = masm.invokeDecls.get(ekey[1]) as MIRInvokeDecl;
            
            if(idcl.attributes.includes("__chktest")) {
                const smtasm = generateSMTPayload(masm, istestbuild, SMT_VOPTS_CHK, noerrorpos, ekey[1]);
                if(smtasm === undefined) {
                    cbdone("Failed to generate SMT assembly");
                }
                else {
                    const smtpayload = generateCheckerPayload(masm, smtasm as string, SMT_TIMEOUT, ekey[1]);
                    testsuites.push({
                        testfile: filteredentry[i].filename,
                        test: new SymTestInternalChkShouldFail(filteredentry[i].filename, filteredentry[i].namespace, ekey[0], ekey[1], idcl.params, masm.typeMap.get(idcl.resultType) as MIRType),
                        cpayload: smtpayload
                    });
                }
            }
            else {
                if(idcl.attributes.includes("chktest")) {
                    const smtasm = generateSMTPayload(masm, istestbuild, SMT_VOPTS_CHK, noerrorpos, ekey[1]);
                    if(smtasm === undefined) {
                        cbdone("Failed to generate SMT assembly");
                    }
                    else {
                    const smtpayload = generateCheckerPayload(masm, smtasm as string, SMT_TIMEOUT, ekey[1]);
                        testsuites.push({
                            testfile: filteredentry[i].filename,
                            test: new SymTest(TestResultKind.ok, filteredentry[i].filename, filteredentry[i].namespace, ekey[0], ekey[1], idcl.params, masm.typeMap.get(idcl.resultType) as MIRType, smtasm, smtpayload, undefined),
                            cpayload: smtpayload
                        });
                    }
                }
                else {
                    const errors = SMTEmitter.generateSMTAssemblyAllErrors(masm, istestbuild, SMT_VOPTS_ERR, ekey[1]);

                    errors.forEach((errpos) => {
                        const smtasm = generateSMTPayload(masm, istestbuild, SMT_VOPTS_ERR, errpos, ekey[1]);
                        if(smtasm === undefined) {
                            cbdone("Failed to generate SMT assembly");
                        }
                        else {
                            const smtpayload = generateCheckerPayload(masm, smtasm as string, SMT_TIMEOUT, ekey[1]);
                            testsuites.push({
                                testfile: filteredentry[i].filename,
                                test: new SymTest(TestResultKind.errors, filteredentry[i].filename, filteredentry[i].namespace, ekey[0], ekey[1], idcl.params, masm.typeMap.get(idcl.resultType) as MIRType, smtasm, smtpayload, errpos),
                                cpayload: smtpayload
                            });
                        }
                    });
                }
            }
        });
    }

    if(testsuites.length === 0) {
        cbdone(null);
    }
    else {
        const tests = testsuites.map((ts) => {
            return {test: ts.test, cpayload: ts.cpayload};
        });

        enqueueSymTests(smtpath, tests, verbose === "max", cbpre, cb, () => cbdone(null));
    }
}

function outputResultsAndExit(verbose: Verbosity, totaltime: number, totalicpp: number, failedicpp: {test: ICPPTest, info: string}[], erroricpp: {test: ICPPTest, info: string}[], totalsmt: number, passlimitsmt: number, failedsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[], errorsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[]) {
    if(verbose !== "std") {
        process.stdout.write("\n");   
    }
    
    process.stdout.write(`Ran ${totalicpp + totalsmt} tests in ${totaltime}s ...\n\n`);
    
    process.stdout.write(`Ran ${totalicpp} executable tests ...\n`);
    if (failedicpp.length === 0 && erroricpp.length === 0) {
        process.stdout.write(chalk.green(chalk.bold("All executable tests pass!\n\n")));
    }
    else {
        process.stdout.write(`${totalicpp - (failedicpp.length + erroricpp.length)} executable tests pass` + "\n");

        if(failedicpp.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${failedicpp.length}`) + " " + chalk.red("executable test failures") + "\n");

            const rstr = failedicpp.map((tt) => `${tt.test.namespace}::${tt.test.fname} -- "${tt.info}"`).join("\n  ");
            process.stdout.write("  " + rstr + "\n\n");
        }

        if(erroricpp.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${erroricpp.length}`) + " " + chalk.magenta("executable test errors") + "\n");

            const rstr = erroricpp.map((tt) => `${tt.test.namespace}::${tt.test.fname} -- "${tt.info}"`).join("\n  ");
            process.stdout.write("  " + rstr + "\n\n");
        }
    }

    process.stdout.write(`Ran ${totalsmt} symbolic tests...\n`);
    if (failedsmt.length === 0 && errorsmt.length === 0) {
        if(passlimitsmt === 0) {
            process.stdout.write(chalk.green(chalk.bold("All symbolic tests pass!\n\n")));
        }
        else {
            process.stdout.write(chalk.green(chalk.bold(`${totalsmt - passlimitsmt} symbolic tests pass!\n`)));
            process.stdout.write(chalk.blue(chalk.bold(`${passlimitsmt} symbolic tests report no error found in resource limit!\n\n`)));
        }
    }
    else {
        process.stdout.write(`${totalsmt - (failedsmt.length + errorsmt.length + passlimitsmt)} symbolic tests pass\n`);

        if(failedsmt.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${failedsmt.length}`) + " " + chalk.red("symbolic test failures") + "\n");

            const rstr = failedsmt.map((tt) => {
                let infostr = tt.info;
                try {
                    infostr = JSON.stringify(JSON.parse(tt.info), undefined, 2);
                }
                catch (ex) {
                    ;
                }

                const tname = chalk.bold(`${tt.test.namespace}::${tt.test.fname}`);
                return `---- ${tname} ----\n"${infostr}"`;
            }).join("\n");

            process.stdout.write(rstr + "\n\n");
        }

        if(errorsmt.length !== 0) {
            process.stdout.write(chalk.bold(`Suite had ${errorsmt.length}`) + " " + chalk.magenta("symbolic test errors") + "\n");

            const rstr = errorsmt.map((tt) => {
                const tname = chalk.bold(`${tt.test.namespace}::${tt.test.fname}`);
                return`${tname} -- "${tt.info}"`
            }).join("\n  ");
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
            code.push({ srcpath: realpath, filename: Path.basename(files[i]), contents: FS.readFileSync(realpath).toString() });
        }

        return new PackageConfig([...macrodefs, ...globalmacros], code);
    }
    catch (ex) {
        return undefined;
    }
}

function loadEntryPointInfo(files: string[], istestbuild: boolean): {filename: string, namespace: string, names: string[]}[] | undefined {
    try {
        let epi: {filename: string, namespace: string, names: string[]}[] = [];

        for(let i = 0; i < files.length; ++i) {
            const contents = cleanCommentsStringsFromFileContents(FS.readFileSync(files[i]).toString());

            const namespacere = /namespace([ \t]+)(?<nsstr>(([A-Z][_a-zA-Z0-9]+)::)*([A-Z][_a-zA-Z0-9]+));/;
            const entryre = /(entrypoint|chktest|errtest|__chktest)(\s+)function(\s+)(?<fname>([_a-z]|([_a-z][_a-zA-Z0-9]*[a-zA-Z0-9])))(\s*)\(/g;
            
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

                if(mm[0].startsWith("entrypoint") || istestbuild) {
                    names.push(mm.groups.fname);
                }

                entryre.lastIndex += mm[0].length;
                mm = entryre.exec(contents);
            }

            epi.push({filename: files[i], namespace: nsstr, names: names});
        }

        return epi;
    }
    catch (ex) {
        return undefined;
    }
}

function runtests(packageloads: {macros: string[], files: string[]}[], globalmacros: string[], entrypointfiles: string[], buildlevel: BuildLevel, smallmodelonly: boolean, istestbuild: boolean, topts: TranspilerOptions, verbose: Verbosity, category: Category[], dirs: string[]) {
    let totalicpp = 0;
    let failedicpp: {test: ICPPTest, info: string}[] = [];
    let erroricpp: {test: ICPPTest, info: string}[] = [];

    let totalsmt = 0;
    let passlimitsmt = 0;
    let failedsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[] = [];
    let errorsmt: {test: (SymTest | SymTestInternalChkShouldFail), info: string}[] = [];

    const start = new Date();

    const usersrc = packageloads.map((psrc) => loadUserPackageSrc(psrc.files.map((src) => src), psrc.macros, globalmacros));
    if(usersrc.includes(undefined)) {
        process.stdout.write(chalk.red("Failure loading user packages\n"));
        process.exit(1);
    }

    const entrypoints = loadEntryPointInfo(entrypointfiles, istestbuild);
    if(entrypoints === undefined) {
        process.stdout.write(chalk.red("Failure loading entrypoints\n"));
        process.exit(1);
    }

    const cbpre_smt = (tt: SymTest | SymTestInternalChkShouldFail) => {
        process.stdout.write(`Starting ${tt.namespace}::${tt.fname}...\n`);
    };
    const cb_smt = (result: "pass"  | "passlimit" | "fail" | "error", test: SymTest | SymTestInternalChkShouldFail, start: Date, end: Date, smtime: number, info?: string) => {
        totalsmt++;

        if(result === "pass") {
            ;
        }
        else if(result === "passlimit") {
            passlimitsmt++;
        }
        else if(result === "fail") {
            failedsmt.push({test: test, info: info || "[Missing Info]"});
        }
        else {
            errorsmt.push({test: test, info: info || "[Missing Info]"});
        }

        if(verbose !== "std") {
            let rstr = "";
            if(result === "pass") {
                rstr = chalk.green("pass");
            }
            else if(result === "passlimit") {
                rstr = chalk.blue("no error found");
            }
            else if(result === "fail") {
                rstr = chalk.red("fail");
            }
            else {
                rstr = chalk.magenta("error");
            }

            if(test instanceof SymTestInternalChkShouldFail) {
                process.stdout.write(`Symbolic test ${test.namespace}::${test.fname} completed with ${rstr} in ${smtime}ms (${end.getTime() - start.getTime()}ms elapsed)\n`);
            }
            else {
                if(test.trgterror === undefined) {
                    process.stdout.write(`Symbolic test ${test.namespace}::${test.fname} completed with ${rstr} in ${smtime}ms (${end.getTime() - start.getTime()}ms elapsed)\n`);       
                }
                else {
                    process.stdout.write(`Symbolic test completed with ${rstr} in ${smtime}ms (${end.getTime() - start.getTime()}ms elapsed)\n`);
                    
                    if(result === "fail" || result === "passlimit") {
                        process.stdout.write(`    Error was ${test.trgterror.msg} in ${Path.basename(test.trgterror.file)}@${test.trgterror.line} from ${test.namespace}::${test.fname} entrypoint\n`);
                    }
                }
            }
        }
    };
    const cbdone_smt = (err: string | null) => {
        if(err !== null) {
            process.stdout.write(chalk.red("Hard failure loading Symbolic tests --\n"));
            process.stdout.write("  " + err + "\n");
            process.exit(1);
        }
        else {
            const end = new Date();
            const totaltime = (end.getTime() - start.getTime()) / 1000;
            outputResultsAndExit(verbose, totaltime, totalicpp, failedicpp, erroricpp, totalsmt, passlimitsmt, failedsmt, errorsmt);
        }
    };

    const cbpre_icpp = (tt: ICPPTest) => {
        process.stdout.write(`Starting ${tt.namespace}::${tt.fname}...\n`);
    };
    const cb_icpp = (result: "pass" | "fail" | "error", test: ICPPTest, start: Date, end: Date, icpptime: number, info?: string) => {
        totalicpp++;
        
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

            process.stdout.write(`Executable test ${test.namespace}::${test.fname} completed with ${rstr} in ${icpptime}ms (${end.getTime() - start.getTime()}ms elapsed)\n`);
        }
    };
    const cbdone_icpp = (err: string | null) => {
        if(err !== null) {
            process.stdout.write(chalk.red("Hard failure loading ICPP tests --\n"));
            process.stdout.write("  " + err + "\n");
            process.exit(1);
        }
        else {
            runtestsSMT(buildlevel, smallmodelonly, istestbuild, usersrc as PackageConfig[], entrypoints, verbose, category, dirs, cbpre_smt, cb_smt, cbdone_smt);
        }
    };

    runtestsICPP(buildlevel, istestbuild, topts, usersrc as PackageConfig[], entrypoints, verbose, category, dirs, cbpre_icpp, cb_icpp, cbdone_icpp);
}

export {
    Verbosity, Category,
    runtests
};
