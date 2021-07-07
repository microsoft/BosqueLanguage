//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import * as FS from "fs";
import * as Path from "path";

import * as Commander from "commander";
import chalk from "chalk";

import { enqueueSMTTestEvaluate, enqueueSMTTestRefute, enqueueSMTTestWitness } from "./smt_runner";
import { runCompilerTest } from "./compile_runner";
import { enqueueICPPTest } from "./icpp_runner";

const testroot = Path.normalize(Path.join(__dirname, "tests"));

abstract class IndividualTestInfo {
    readonly name: string;
    readonly fullname: string;

    readonly code: string;

    readonly extraSrc: string | undefined;

    constructor(name: string, fullname: string, code: string, extraSrc: string | undefined) {
        this.name = name;
        this.fullname = fullname;
        this.code = code;
        this.extraSrc = extraSrc;
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        if(restriction === "compile") {
            if(this instanceof IndividualCompileWarnTest) {
                tests.push(this);
            }
        }
        else if(restriction === "check") {
            if((this instanceof IndividualInfeasibleTestInfo) || (this instanceof IndividualWitnessTestInfo)) {
                tests.push(this);
            }
        }
        else if(restriction === "evaluate") {
            if((this instanceof IndividualEvaluateTestInfo)) {
                tests.push(this);
            }
        }
        else if(restriction === "smt") {
            if((this instanceof IndividualInfeasibleTestInfo) || (this instanceof IndividualWitnessTestInfo) || (this instanceof IndividualEvaluateTestInfo)) {
                tests.push(this);
            }
        }
        else if(restriction === "execute") {
            if(this instanceof IndividualICPPTestInfo) {
                tests.push(this);
            }
        }
        else { 
            if(restriction === "*" || this.fullname.startsWith(restriction)) {
                tests.push(this);
            }
        }
    }
}

class IndividualCompileWarnTest extends IndividualTestInfo {
    private static ctemplate = 
"namespace NSMain;\n\
\n\
%%SIG%% {\n\
    return %%ACTION%%;\n\
}\n\
\n\
%%CODE%%\n\
";

    constructor(name: string, fullname: string, code: string, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);
    }

    static create(name: string, fullname: string, sig: string, action: string, code: string, extraSrc: string | undefined): IndividualCompileWarnTest {
        const rcode = IndividualCompileWarnTest.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CODE%%", code);

        return new IndividualCompileWarnTest(name, fullname, rcode, extraSrc);
    }
}

class IndividualInfeasibleTestInfo extends IndividualTestInfo {
    readonly line: number;

    private static ctemplate = 
"namespace NSMain;\n\
\n\
%%SIG%% {\n\
    let res = %%ACTION%%;\n\
    assert %%CHECK%%;\n\
    return res;\n\
}\n\
\n\
%%CODE%%\n\
";

    constructor(name: string, fullname: string, code: string, line: number, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.line = line;
    }

    static create(name: string, fullname: string, sig: string, action: string, check: string, code: string, extraSrc: string | undefined): IndividualInfeasibleTestInfo {
        const rcode = IndividualInfeasibleTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CHECK%%", check)
            .replace("%%CODE%%", code);

        return new IndividualInfeasibleTestInfo(name, fullname, rcode, 5, extraSrc);
    }
}

class IndividualWitnessTestInfo extends IndividualTestInfo {
    readonly line: number;

    private static ctemplate = 
"namespace NSMain;\n\
\n\
%%SIG%% {\n\
    let res = %%ACTION%%;\n\
    assert %%CHECK%%;\n\
    return res;\n\
}\n\
\n\
%%CODE%%\n\
";

    constructor(name: string, fullname: string, code: string, line: number, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.line = line;
    }

    static create(name: string, fullname: string, sig: string, action: string, check: string, code: string, extraSrc: string | undefined): IndividualWitnessTestInfo {
        const rcode = IndividualWitnessTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CHECK%%", check)
            .replace("%%CODE%%", code);

        return new IndividualWitnessTestInfo(name, fullname, rcode, 5, extraSrc);
    }
}

class IndividualEvaluateTestInfo extends IndividualTestInfo {
    readonly jargs: any[];
    readonly expected: any; //undefined is infeasible

    private static ctemplate = 
"namespace NSMain;\n\
\n\
%%SIG%% {\n\
    return %%ACTION%%;\n\
}\n\
\n\
%%CODE%%\n\
";

    constructor(name: string, fullname: string, code: string, jargs: any[], expected: any, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.jargs = jargs;
        this.expected = expected;
    }

    static create(name: string, fullname: string, sig: string, action: string, code: string, jargs: any[], expected: any, extraSrc: string | undefined): IndividualEvaluateTestInfo {
        const rcode = IndividualEvaluateTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CODE%%", code);

        return new IndividualEvaluateTestInfo(name, fullname, rcode, jargs, expected, extraSrc);
    }
}

class IndividualICPPTestInfo extends IndividualTestInfo {
    readonly jargs: any[];
    readonly expected: string | undefined; //undefined is exception

    private static ctemplate = 
"namespace NSMain;\n\
\n\
%%SIG%% {\n\
    return %%ACTION%%;\n\
}\n\
\n\
%%CODE%%\n\
";

    constructor(name: string, fullname: string, code: string, jargs: any[], expected: string | undefined, extraSrc: string | undefined) {
        super(name, fullname, code, extraSrc);

        this.jargs = jargs;
        this.expected = expected;
    }

    static create(name: string, fullname: string, sig: string, action: string, code: string, jargs: any[], expected: string | undefined, extraSrc: string | undefined): IndividualICPPTestInfo {
        const rcode = IndividualICPPTestInfo.ctemplate
            .replace("%%SIG%%", sig)
            .replace("%%ACTION%%", action)
            .replace("%%CODE%%", code);

        return new IndividualICPPTestInfo(name, fullname, rcode, jargs, expected, extraSrc);
    }
}

type APICheckTestBundle = {
    action: string,
    check: string
};

type APIExecTestBundle = {
    action: string,
    args: any[],
    result: any
};

type APITestGroupJSON = {
    test: string,
    src: string | null,
    sig: string,
    code: string,
    typechk: string[],
    infeasible: APICheckTestBundle[],
    witness: APICheckTestBundle[],
    evaluates: APIExecTestBundle[],
    icpp: APIExecTestBundle[]
};

class APITestGroup {
    readonly groupname: string;
    readonly tests: IndividualTestInfo[];

    constructor(groupname: string, tests: IndividualTestInfo[]) {
        this.groupname = groupname;
        this.tests = tests;
    }

    static create(scopename: string, spec: APITestGroupJSON): APITestGroup {
        const groupname = `${scopename}.${spec.test}`;
        const compiles = (spec.typechk || []).map((tt, i) => IndividualCompileWarnTest.create(`compiler#${i}`, `${groupname}.compiler#${i}`, spec.sig, tt, spec.code, spec.src || undefined));
        const infeasible = (spec.infeasible || []).map((tt, i) => IndividualInfeasibleTestInfo.create(`infeasible#${i}`, `${groupname}.infeasible#${i}`, spec.sig, tt.action, tt.check, spec.code, spec.src || undefined));
        const witness = (spec.witness || []).map((tt, i) => IndividualWitnessTestInfo.create(`witness#${i}`, `${groupname}.witness#${i}`, spec.sig, tt.action, tt.check, spec.code, spec.src || undefined));
        const evaluate = (spec.evaluates || []).map((tt, i) => IndividualEvaluateTestInfo.create(`evaluate#${i}`, `${groupname}.evaluate#${i}`, spec.sig, tt.action, spec.code, tt.args, tt.result, spec.src || undefined));
        const icpp = (spec.icpp || []).map((tt, i) => IndividualICPPTestInfo.create(`icpp#${i}`, `${groupname}.icpp#${i}`, spec.sig, tt.action, spec.code, tt.args, tt.result, spec.src || undefined));

        return new APITestGroup(groupname, [...compiles, ...infeasible, ...witness, ...evaluate, ...icpp]);
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

type CategoryTestGroupJSON = {
    suite: string,
    tests: APITestGroupJSON[]
};

class CategoryTestGroup {
    readonly categoryname: string;
    readonly apitests: APITestGroup[];

    constructor(categoryname: string, apitests: APITestGroup[]) {
        this.categoryname = categoryname;
        this.apitests = apitests;
    }

    static create(scopename: string, spec: CategoryTestGroupJSON) {
        const categoryname = `${scopename}.${spec.suite}`;
        const apitests = spec.tests.map((tt) => APITestGroup.create(categoryname, tt));

        return new CategoryTestGroup(categoryname, apitests);
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.apitests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

class TestFolder {
    readonly path: string;
    readonly testname: string;

    readonly tests: CategoryTestGroup[];

    constructor(path: string, testname: string, tests: CategoryTestGroup[]) {
        this.path = path;
        this.testname = testname;
        this.tests = tests;
    }

    generateTestPlan(restriction: string, tests: IndividualTestInfo[]) {
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));
    }
}

class TestSuite {
    readonly tests: TestFolder[];

    constructor(tests: TestFolder[]) {
        this.tests = tests;
    }

    generateTestPlan(restriction: string): TestPlan {
        let tests: IndividualTestInfo[] = [];
        this.tests.forEach((tt) => tt.generateTestPlan(restriction, tests));

        return new TestPlan(this, tests);
    }
}

class TestPlan {
    readonly suite: TestSuite;
    readonly tests: IndividualTestInfo[];

    constructor(suite: TestSuite, tests: IndividualTestInfo[]) {
        this.suite = suite;
        this.tests = tests;
    }
}

class TestResult {
    readonly test: IndividualTestInfo;
    readonly start: Date;
    readonly end: Date;

    readonly status: "pass" | "fail" | "error";
    readonly info: string | undefined;

    constructor(test: IndividualTestInfo, start: Date, end: Date, status: "pass" | "fail" | "error", info: string | undefined) {
        this.test = test;
        this.start = start;
        this.end = end;
        this.status = status;
        this.info = info;
    }
}

class TestRunResults {
    readonly suite: TestSuite;

    start: Date = new Date(0);
    end: Date = new Date(0);

    passed: TestResult[] = [];
    failed: TestResult[] = [];
    errors: TestResult[] = [];

    constructor(suite: TestSuite) {
        this.suite = suite;
    }

    getOverallResults(): {total: number, elapsed: number, passed: number, failed: number, errors: number} {
        return {
            total: this.passed.length + this.failed.length + this.errors.length,
            elapsed: (this.end.getTime() - this.start.getTime()) / 1000,
            passed: this.passed.length,
            failed: this.failed.length,
            errors: this.errors.length
        }
    }
}

function loadTestSuite(): TestSuite {
    const tdirs = FS.readdirSync(testroot, {withFileTypes: true}).filter((de) => de.isDirectory());

    let tfa: TestFolder[] = [];
    for(let i = 0; i < tdirs.length; ++i) {
        const dpath = Path.join(testroot, tdirs[i].name);
        const tfiles = FS.readdirSync(dpath).filter((fp) => fp.endsWith(".json"));

        let ctgs: CategoryTestGroup[] = [];
        for (let j = 0; j < tfiles.length; ++j) {
            const fpath = Path.join(dpath, tfiles[j]);
            const fcontents = JSON.parse(FS.readFileSync(fpath, "utf8")) as CategoryTestGroupJSON;
            ctgs.push(CategoryTestGroup.create(`${tdirs[i].name}.${tfiles[j].replace(".json", "")}`, fcontents));
        }

        tfa.push(new TestFolder(dpath, tdirs[i].name, ctgs));
    }

    return new TestSuite(tfa);
}

type SMTTestAssets = {
    extras: Map<string, string>
};

function loadSMTTestAssets(suite: TestSuite): SMTTestAssets {
    let extras = new Map<string, string>();
    for(let i = 0; i < suite.tests.length; ++i) {
        const tf = suite.tests[i];
        for (let j = 0; j < tf.tests.length; ++j) {
            const ctg = tf.tests[j];
            for (let k = 0; k < ctg.apitests.length; ++k) {
                const stg = ctg.apitests[k];
                stg.tests.filter((iti) => iti.extraSrc !== undefined).forEach((iti) => {
                    const cc = Path.join(testroot, iti.extraSrc as string);
                    const contents = FS.readFileSync(cc, "utf8");

                    extras.set(iti.extraSrc as string, contents);
                });
            }
        }
    }

    return {
        extras: extras
    };
}

type ICPPTestAssets = {
    extras: Map<string, string>
};

function loadICPPTestAssets(suite: TestSuite): ICPPTestAssets {
    let extras = new Map<string, string>();
    for(let i = 0; i < suite.tests.length; ++i) {
        const tf = suite.tests[i];
        for (let j = 0; j < tf.tests.length; ++j) {
            const ctg = tf.tests[j];
            for (let k = 0; k < ctg.apitests.length; ++k) {
                const stg = ctg.apitests[k];
                stg.tests.filter((iti) => iti.extraSrc !== undefined).forEach((iti) => {
                    const cc = Path.join(testroot, iti.extraSrc as string);
                    const contents = FS.readFileSync(cc, "utf8");

                    extras.set(iti.extraSrc as string, contents);
                });
            }
        }
    }

    return {
        extras: extras
    };
}

class TestRunner {
    readonly suite: TestSuite;
    readonly plan: TestPlan;

    pending: IndividualTestInfo[];
    queued: string[];
    results: TestRunResults;

    maxpar: number;
    ppos: number = 0;

    inccb: (msg: string) => void = (m: string) => {;};
    done: (results: TestRunResults) => void = (r: TestRunResults) => {;};

    smt_assets: SMTTestAssets;
    icpp_assets: ICPPTestAssets;
    
    private testCompleteActionProcess(test: IndividualTestInfo, result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) {
        if (result === "pass") {
            this.results.passed.push(new TestResult(test, start, end, "pass", undefined));
            this.inccb(test.fullname + ": " + chalk.green("pass") + "\n");
        }
        else if (result === "fail") {
            this.results.failed.push(new TestResult(test, start, end, "fail", info));
            const failinfo = info !== undefined ? ` with: \n${info.slice(0, 80)}${info.length > 80 ? "..." : ""}` : "";
            this.inccb(test.fullname + ": " + chalk.red("fail") + failinfo + "\n");
        }
        else {
            this.results.failed.push(new TestResult(test, start, end, "error", info));
            const errinfo = info !== undefined ? ` with ${info.slice(0, 80)}${info.length > 80 ? "..." : ""}` : "";
            this.inccb(test.fullname + ": " + chalk.magenta("error") + errinfo + "\n");
        }
    }

    private testCompleteActionQueued(test: IndividualTestInfo, result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) {
        const qidx = this.queued.findIndex((vv) => vv === test.fullname);
        assert(qidx !== -1);

        this.queued.splice(qidx, 1);

        this.testCompleteActionProcess(test, result, start, end, info);
    }

    private testCompleteActionInline(test: IndividualTestInfo, result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) {
        this.testCompleteActionProcess(test, result, start, end, info);
    }

    private generateTestResultCallback(test: IndividualTestInfo) {
        return (result: "pass" | "fail" | "unknown/timeout" | "error", start: Date, end: Date, info?: string) => {
            this.testCompleteActionQueued(test, result, start, end, info);

            this.checkAndEnqueueTests();

            if(this.ppos === this.pending.length && this.queued.length === 0) {
                this.done(this.results);
            }
        };
    }

    private checkAndEnqueueTests() {
        while(this.queued.length < this.maxpar && this.ppos < this.pending.length) {
            const tt = this.pending[this.ppos++];

            if (tt instanceof IndividualCompileWarnTest) {
                let code = tt.code;
                if(tt.extraSrc !== undefined) {
                    code = code + "\n\n" + this.smt_assets.extras.get(tt.extraSrc) as string;
                }

                const tinfo = runCompilerTest(code);
                this.testCompleteActionInline(tt, tinfo.result, tinfo.start, tinfo.end, tinfo.info);
            }
            else if (tt instanceof IndividualInfeasibleTestInfo) {
                let code = tt.code;
                if(tt.extraSrc !== undefined) {
                    code = code + "\n\n" + this.smt_assets.extras.get(tt.extraSrc) as string;
                }

                const handler = this.generateTestResultCallback(tt);
                this.queued.push(tt.fullname);
                try {
                    enqueueSMTTestRefute(code, tt.line, handler);
                }
                catch (ex) {
                    handler("error", new Date(), new Date(), `${ex}`);
                }
            }
            else if (tt instanceof IndividualWitnessTestInfo) {
                let code = tt.code;
                if(tt.extraSrc !== undefined) {
                    code = code + "\n\n" + this.smt_assets.extras.get(tt.extraSrc) as string;
                }

                const handler = this.generateTestResultCallback(tt);
                this.queued.push(tt.fullname);
                try {
                    enqueueSMTTestWitness(code, tt.line, handler);
                }
                catch (ex) {
                    handler("error", new Date(), new Date(), `${ex}`);
                }
            }
            else if(tt instanceof IndividualEvaluateTestInfo) {
                let code = tt.code;
                if(tt.extraSrc !== undefined) {
                    code = code + "\n\n" + this.smt_assets.extras.get(tt.extraSrc) as string;
                }

                const handler = this.generateTestResultCallback(tt);
                this.queued.push(tt.fullname);
                try {
                    enqueueSMTTestEvaluate(code, tt.jargs, tt.expected, handler);
                }
                catch (ex) {
                    handler("error", new Date(), new Date(), `${ex}`);
                }
            }
            else if(tt instanceof IndividualICPPTestInfo) {
                let code = tt.code;
                if(tt.extraSrc !== undefined) {
                    code = code + "\n\n" + this.icpp_assets.extras.get(tt.extraSrc) as string;
                }

                const handler = this.generateTestResultCallback(tt);
                this.queued.push(tt.fullname);
                try {
                    enqueueICPPTest(code, tt.jargs, tt.expected, handler);
                }
                catch (ex) {
                    handler("error", new Date(), new Date(), `${ex}`);
                }
            }
            else {
                assert(false);
                break;
            }
        }
    }

    constructor(suite: TestSuite, smtassets: SMTTestAssets, icppassets: ICPPTestAssets, plan: TestPlan, maxpar?: number) {
        this.suite = suite;
        this.plan = plan;
        this.smt_assets = smtassets;
        this.icpp_assets = icppassets;

        this.pending = [...this.plan.tests];
        this.queued = [];
        this.results = new TestRunResults(suite);

        this.maxpar = maxpar || 8;
    }

    run(inccb: (msg: string) => void, oncomplete: (results: TestRunResults) => void) {
        this.results.start = new Date();

        this.inccb = inccb;
        this.done = oncomplete;

        this.checkAndEnqueueTests();
    }
}

////
//Application

Commander
    .option("-m --parallel [parallel]", "Number of parallel tests to run simultaniously", 4)
    .option("-r --restriction [spec]", "Limit the test run to a specific set of tests", "*")
    //
    //TODO: maybe want to run only SMT or only compiler tests too
    //
    ;

Commander.parse(process.argv);

const suite = loadTestSuite();
const plan = suite.generateTestPlan(Commander.restriction)

const smt_assets = loadSMTTestAssets(suite);
const icpp_assets = loadICPPTestAssets(suite);

const runner = new TestRunner(suite, smt_assets, icpp_assets, plan, Commander.parallel);
runner.run(
    (msg: string) => process.stdout.write(msg),
    (results: TestRunResults) => {
        const gresults = results.getOverallResults();
        process.stdout.write(`Completed ${gresults.total} tests...\n`);
        if(gresults.failed === 0 && gresults.errors === 0) {
            process.stdout.write(chalk.bold(`${gresults.passed}`) + " " + chalk.green("ok") + "\n");
            process.exit(0);
        }
        else {
            process.stdout.write(chalk.bold(`${gresults.failed}`) + " " + chalk.red("failures") + "\n");
            process.stdout.write(chalk.bold(`${gresults.errors}`) + " " + chalk.magenta("errors") + "\n");
            process.exit(1);
        }
    }
);
