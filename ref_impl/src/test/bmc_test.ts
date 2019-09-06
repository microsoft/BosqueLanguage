//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TestInfo } from "./test_runner";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";
import { SMTLIBGenerator } from "../analysis/smtlib/generator";

import * as Path from "path";
import { execSync } from "child_process";

let z3path: string | undefined = undefined;
if (process.platform === "win32") {
    z3path = Path.resolve("./utils/win/z3/z3.exe");
}
else if (process.platform === "linux") {
    z3path = Path.resolve("./utils/linux/z3/z3.exe");
}
else {
    z3path = Path.resolve("./utils/macos/z3/z3.exe");
}

const bmc_test = `
namespace NSTestBMC;

entity E1 {
    field f: Int;
    field g: Bool;
}

entrypoint function add(x: Int, y: Int): Int {
    return x + y;
}

entrypoint function addOpt1(x: [Int, ?: Int]): Int {
    return x.0 + (x.1 ?| 0);
}

function abs(x: Int): Int {
    if(x < 0) {
        return -x;
    }
    else {
        return x;
    }
}

entrypoint function absOpt(x?: Int): Int {
    if(x == none) {
        return 0;
    }

    return abs(x);
}

entrypoint function maxTuple(x: [Int, Int]): Int {
    if(x.0 > x.1) {
        return x.0;
    }
    else {
        return x.1;
    }
}

entrypoint function swapTuple(x: [Int, Int]): [Int, Int] {
    return [x.1, x.0];
}

entrypoint function modifyTuple(x: [Int, Int]): [Int, Int, Bool] {
    return x->update(1=0, 2=true);
}

entrypoint function simpleEntity(i: Int, b: Bool): Int {
    var e = E1{f=i, g=!b};
    if(e.g) {
        return e.f;
    }
    else {
        return 0;
    }
}

entrypoint function simpleList1(i: Int): Int {
    var e = List<Int>{0, i, 2};
    return e->at(i);
}
`;

const bmc_tests: TestInfo[] = [
    {
        name: "add_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$add 1 3))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },
    {
        name: "add_BADASRT",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$add p1 p2))))",
            "(assert (not (and (>= res p1) (>= res p2))))",
            "(check-sat)"
        ],
        expected: `sat`
    },
    {
        name: "addOpt1_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$addOpt1 (bsq_term_tuple 2 (store (store ((as const (Array Int BTerm)) bsq_term_none) 0 (bsq_term_int 1)) 1 (bsq_term_int 3)))))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },
    {
        name: "addOpt1_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$addOpt1 (bsq_term_tuple 2 (store ((as const (Array Int BTerm)) bsq_term_none) 0 (bsq_term_int p1)))))))",
            "(assert (not (= res p1)))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "absOpt_CHK_1",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$absOpt bsq_term_none))))",
            "(assert (not (= res 0)))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "absOpt_CHK_2",
        input: [
            "(declare-const p1 BTerm)",
            "(declare-const res Int)",
            "(assert (is-bsq_term_int p1))",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$absOpt p1))))",
            "(assert (not (>= res (bsq_term_int_value p1))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "add_SAT",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$add 1 3))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 4) )`
    },

    {
        name: "maxTuple_EXEC",
        input: [
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$maxTuple (bsq_tuple$_Int$Int_$ 1 3)))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun res () Int 3) )`
    },
    {
        name: "maxTuple_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const res Int)",
            "(assert (= res (Result_Int@result_value (NSTestBMC$cc$maxTuple (bsq_tuple$_Int$Int_$ p1 p2)))))",
            "(assert (not (and (>= res p1) (>= res p2) (or (= res p1) (= res p2)))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "swapTuple_EXEC",
        input: [
            "(declare-const p1 Int)",
            "(assert (= (bsq_tuple$_Int$Int_$ p1 1) (Result_Tbsq_tuple$_Int$Int_$@result_value (NSTestBMC$cc$swapTuple (bsq_tuple$_Int$Int_$ 1 3)))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun p1 () Int 3) )`
    },
    {
        name: "swapTuple_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const p2 Int)",
            "(declare-const r1 Int)",
            "(declare-const r2 Int)",
            "(assert (= (bsq_tuple$_Int$Int_$ r1 r2) (Result_Tbsq_tuple$_Int$Int_$@result_value (NSTestBMC$cc$swapTuple (bsq_tuple$_Int$Int_$ p1 p2)))))",
            "(assert (not (and (= r1 p2) (= r2 p1))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "modifyTuple_EXEC",
        input: [
            "(declare-const r2 Int)",
            "(assert (= (bsq_tuple$_Int$Int$Bool_$ 1 r2 true) (Result_Tbsq_tuple$_Int$Int$Bool_$@result_value (NSTestBMC$cc$modifyTuple (bsq_tuple$_Int$Int_$ 1 2)))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun r2 () Int 0) )`
    },
    {
        name: "modifyTuple_CHK",
        input: [
            "(declare-const p1 Int)",
            "(declare-const r1 Int)",
            "(declare-const r2 Int)",
            "(declare-const r3 Bool)",
            "(assert (= (bsq_tuple$_Int$Int$Bool_$ r1 r2 r3) (Result_Tbsq_tuple$_Int$Int$Bool_$@result_value (NSTestBMC$cc$modifyTuple (bsq_tuple$_Int$Int_$ p1 3)))))",
            "(assert (not (and (= r1 p1) r3)))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "simpleEntity_EXEC",
        input: [
            "(declare-const r Int)",
            "(assert (= r (Result_Int@result_value (NSTestBMC$cc$simpleEntity 5 false))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun r () Int 5) )`
    },
    {
        name: "simpleEntity_CHK",
        input: [
            "(declare-const i Int)",
            "(declare-const b Bool)",
            "(declare-const r Int)",
            "(assert (= r (Result_Int@result_value (NSTestBMC$cc$simpleEntity i b))))",
            "(assert (not (=> b (= r 0))))",
            "(assert (not (=> (not b) (= r i))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "simpleList1_EXEC",
        input: [
            "(declare-const r Int)",
            "(assert (= r (Result_Int@result_value (NSTestBMC$cc$simpleList1 2))))",
            "(check-sat)",
            "(get-model)"
        ],
        expected: `sat (model (define-fun r () Int 2) )`
    },
    {
        name: "simpleList1_CHK",
        input: [
            "(declare-const i Int)",
            "(declare-const r Int)",
            "(assert (= r (Result_Int@result_value (NSTestBMC$cc$simpleList1 i))))",
            "(assert (not (=> (and (<= 0 i) (< i 3)) (< r 3))))",
            "(check-sat)"
        ],
        expected: `unsat`
    },
    {
        name: "simpleList1_Err",
        input: [
            "(declare-const i Int)",
            "(declare-const r Result_Int)",
            "(assert (= r (NSTestBMC$cc$simpleList1 i)))",
            "(assert (is-Result_Int@result_with_code r))",
            "(check-sat)"
        ],
        expected: `sat`
    }
];

function bmc_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "bmc_test.bsq", contents: bmc_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), true, true, true, files);
}

function runz3(smtlib: string): string {
    try {
        const res = execSync(`${z3path} -smt2 -in `, { input: smtlib });
        return res.toString().replace(/\s{2,}/g, " ").trim();
    }
    catch (ex) {
        console.log(smtlib);
        return `[${ex}]`;
    }
}

function bmc_action(assembly: MIRAssembly, args: any[]): any {
    const smt2 = new SMTLIBGenerator(assembly).generateSMTAssembly() + "\n\n" + args.join("\n");
    return runz3(smt2);
}

const testBMC = { name: "BMC", setup: bmc_setup, action: bmc_action, tests: bmc_tests, xmlid: "BMCUnitTests" };

export { testBMC };
