//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Interpreter } from "../interpreter/interpreter";
import { TestInfo } from "./test_runner";
import { ValueOps } from "../interpreter/value";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";

const corelib_test = `
namespace NSTestCoreLibraries;

entrypoint function mathAbs(): Float {
    var n: Float = '-2.0'@Float;
    return Math::abs(n);
}

entrypoint function mathAcos(): Float {
    var x: Float = '0.0'@Float;
    return Math::acos(x);
}

entrypoint function mathAsin(): Float {
    var x: Float = '1.0'@Float;
    return Math::asin(x);
}

entrypoint function mathAtan(): Float {
    var x: Float = '3.0'@Float;
    return Math::atan(x);
}

entrypoint function mathAtan2(): Float {
    var y: Float = '3.0'@Float;
    var x: Float = '5.0'@Float;
    return Math::atan2(y, x);
}

entrypoint function mathCeil(): Float {
    var n: Float = '6.4'@Float;
    return Math::ceil(n);
}

entrypoint function mathCos(): Float {
    var x: Float = '90.0'@Float;
    return Math::cos(x);
}

entrypoint function mathFloor(): Float {
    var n: Float = '3.1'@Float;
    return Math::floor(n);
}

entrypoint function mathLog(): Float {
    var n: Float = '4.0'@Float;
    return Math::log(n);
}

entrypoint function mathPow(): Float {
    var b: Float = '3.0'@Float;
    var e: Float = '3.0'@Float;
    return Math::pow(b, e);
}

entrypoint function mathRound(): Float {
    var n: Float = '3.4'@Float;
    return Math::round(n);
}

entrypoint function mathSin(): Float {
    var x: Float = '90.0'@Float;
    return Math::sin(x);
}

entrypoint function mathSqrt(): Float {
    var x: Float = '36.0'@Float;
    return Math::sqrt(x);
}

entrypoint function mathTan(): Float {
    var x: Float = '60.0'@Float;
    return Math::tan(x);
}

entrypoint function literalFooBarReverse(): String {
    var foobar: String = "foobar";
    return foobar->reverse();
}

entrypoint function literalUpCase(): String {
    var foobar: String = "foobar";
    return foobar->upperCase();
}

entrypoint function literalDownCase(): String {
    var foobar: String = "FOOBAR";
    return foobar->lowerCase();
}
`;

const corelib_tests: TestInfo[] = [
    { name: "mathAbs", input: ["mathAbs"], expected: "2" },
    { name: "mathAcos", input: ["mathAcos"], expected: "1.5707963267948966" },
    { name: "mathAsin", input: ["mathAsin"], expected: "1.5707963267948966" },
    { name: "mathAtan", input: ["mathAtan"], expected: "1.2490457723982544" },
    { name: "mathAtan2", input: ["mathAtan2"], expected: "0.5404195002705842" },
    { name: "mathCeil", input: ["mathCeil"], expected: "7" },
    { name: "mathCos", input: ["mathCos"], expected: "-0.4480736161291702" },
    { name: "mathFloor", input: ["mathFloor"], expected: "3" },
    { name: "mathLog", input: ["mathLog"], expected: "1.3862943611198906" },
    { name: "mathPow", input: ["mathPow"], expected: "27" },
    { name: "mathRound", input: ["mathRound"], expected: "3" },
    { name: "mathSin", input: ["mathSin"], expected: "0.8939966636005579" },
    { name: "mathSqrt", input: ["mathSqrt"], expected: "6" },
    { name: "mathTan", input: ["mathTan"], expected: "0.320040389379563" },

    { name: "stringReverse", input: ["literalFooBarReverse"], expected: "\"raboof\"" },
    { name: "stringUpCase", input: ["literalUpCase"], expected: "\"FOOBAR\"" },
    { name: "stringDownCase", input: ["literalDownCase"], expected: "\"foobar\"" }
];

function corelib_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "corelib_tests.bsq", contents: corelib_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function corelib_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestCoreLibraries", args[0], []));
}

const testCoreLibs = { name: "CoreLibs", setup: corelib_setup, action: corelib_action, tests: corelib_tests, xmlid: "CoreLibUnitTests" };

const collectionlib_test = `
namespace NSTestCollections;

entrypoint function findLastMatchingElementInList(): { f: Int, b: Int } {
    return List[{ f: Int, b: Int }]@{ @{ f = 1, b = 2 }, @{ f = 2, b = 3 }, @{ f = 2, b = 4 } }->findLast(fn(x) => x.f == 2);
}

entrypoint function tryFindLastMatchingElementInList1(): { f: Int, b: Int } | None {
    return List[{ f: Int, b: Int }]@{ @{ f = 1, b = 2 }, @{ f = 2, b = 3 }, @{ f = 2, b = 4 } }->tryFindLast(fn(x) => x.f == 3);
}

entrypoint function tryFindLastMatchingElementInList2(): { f: Int, b: Int } | None {
    return List[{ f: Int, b: Int }]@{ @{ f = 1, b = 2 }, @{ f = 2, b = 3 }, @{ f = 2, b = 4 } }->tryFindLast(fn(x) => x.f == 2);
}

entrypoint function fillList(): List[Int] {
    var list: List[Int] = List[Int]@{1,2,3,4,5};
    return list->fill(1);
}
`;

const collectionlib_tests: TestInfo[] = [
    { name: "findLastMatchingElementInList", input: ["findLastMatchingElementInList"], expected: "@{ b=4, f=2 }" },
    { name: "tryFindLastMatchingElementInList1", input: ["tryFindLastMatchingElementInList1"], expected: "none" },
    { name: "tryFindLastMatchingElementInList2", input: ["tryFindLastMatchingElementInList2"], expected: "@{ b=4, f=2 }" },
    { name: "fillList", input: ["fillList"], expected: "NSCore::List[T=NSCore::Int]@{ 1, 1, 1, 1, 1 }" }
];

function collectionlib_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "collectionlib_tests.bsq", contents: collectionlib_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function collectionlib_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestCollections", args[0], []));
}

const testCollectionLibs = { name: "CollectionLibs", setup: collectionlib_setup, action: collectionlib_action, tests: collectionlib_tests, xmlid: "CollectionLibUnitTests" };


export { testCoreLibs, testCollectionLibs };
