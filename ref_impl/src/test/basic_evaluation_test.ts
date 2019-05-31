//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Interpreter } from "../interpreter/interpreter";
import { TestInfo } from "./test_runner";
import { ValueOps, Value } from "../interpreter/value";
import { MIRAssembly, PackageConfig } from "../compiler/mir_assembly";
import { MIREmitter } from "../compiler/mir_emitter";

const expression_test = `
namespace NSTestExpression;

///////
//These entities are not tested but are used in other tests

entity Foo provides Parsable {
    override static tryParse(str: String): Foo | None {
        return str == "hello" ? Foo@{} : none;
    }
}

concept Bar {
    field x: Any;
    field y: Int = 3;
}

concept Baz {
    field z: Bool;
}

entity E1 provides Bar, Baz {
    field f: Int;

    factory static create(arg: Int): {x: Any, y: Int, z: Bool, f: Int} {
        return @{ x=none, y=1, z=true, f=3 };
    }

    factory static creat[T](arg: T): {x: T, y: Int, z: Bool, f: Int} {
        return @{ x=arg, y=1, z=true, f=3 };
    }
}

entity E2[T] {
    field f: T;
    field g: Any;

    factory static create(arg: T): {f: T, g: Int} {
        return @{ f=arg, g=1 };
    }

    factory static creat[U](x: T, y: U): {f: T, g: U} {
        return @{ f=x, g=y };
    }
}

concept Fizz[T] {
    method m1(x: Int): Int {
        return x + 1;
    }

    virtual method ii(x: T): T {
        return x;
    }

    virtual method m3(x: Int): Int {
        return x + 3;
    }
}

entity E3 provides Fizz[Int] {
    field func: fn(this: E3, x: Int) -> Int = fn(this: E3, x: Int): Int => x + 1;

    override method m3(x: Int): Int {
        return 0;
    }

    method mc(x: Int, y: Int): Int {
        return x + y;
    }
}

entity E4[T] provides Fizz[Int] {
    field func: fn(this: E4[T], x?: T) -> Bool = fn(this: E4[T], x?: T): Bool => x == none;

    method mc(x?: T): Int {
        return x == none ? 1 : 0;
    }

    method mcc[U](y: U, x?: T): U | T {
        return x == none ? y : x;
    }
}

///////
//These functions is not tested but are called from other tests

function emptyArgs(): Int {
    return 0;
}

function requiredArgs(v1: Int, v2: Int): Int {
    return v1 + v2;
}

function optionalArgs(v1?: Int, v2?: Int): Int? {
    return (v1 ?& v2 ?& v1 + v2);
}

function mixedArgs(v1: Int, v2?: Int): Int {
    return (v2 ?& v1 + v2) ?| -1;
}

function identityAny[T](x: T): T {
    return x;
}

function identityInt[T where Int](x: T): T {
    return x;
}

function prePost(arg: Int): Int?
    requires 2 < arg && arg < 10;
    ensures _return_ != none;
{
    return arg + 1;
}

function lambdaArgument(f: fn(_: Int) -> Int, x: Int): Int {
    return f(x);
}

function restArgListSimple(...arg: List[Int]): List[Int] {
    return arg;
}

function restArgSetSimple[T](...arg: HashSet[T]): HashSet[T] {
    return arg;
}

function restArgMapSimple(...arg: HashMap[Int, Bool]): HashMap[Int, Bool] {
    return arg;
}

function argListMixed(v: Bool, ...arg: List[Int]): List[Int] {
    return v ? arg : List[Int]@{ 1 };
}

///////
//These functions are the tests we run

entrypoint function literalNone(): None {
    return none;
}

entrypoint function literalTrue(): Bool {
    return true;
}

entrypoint function literalFalse(): Bool {
    return false;
}

entrypoint function literal1(): Int {
    return 1;
}

entrypoint function literal3(): Int {
    return 3;
}

entrypoint function literalEmptyString(): String {
    return "";
}

entrypoint function literalHello(): String {
    return "hello";
}

entrypoint function literalFooString(): String[Foo] {
    return 'hello'#Foo;
}

entrypoint function literalFooObject(): Foo {
    return 'hello'@Foo;
}

entrypoint function emptyTuple(): [] {
    return @[];
}

entrypoint function oneTuple(): [Int] {
    return @[ 1 ];
}

entrypoint function fourTuple(): [Int, Int, None, Bool] {
    return @[ 1, 2, none, true ];
}

entrypoint function emptyRecord(): {} {
    return @{};
}

entrypoint function oneRecord(): {f: Int} {
    return @{ f=1 };
}

entrypoint function fourRecord(): {f: Int, g: Int, h: None, k: Bool} {
    return @{ f=1, g=2, h=none, k=true };
}

entrypoint function nestedTuples(): [Int, [None, []]] {
    return @[ 1, @[ none, @[] ] ];
}

entrypoint function nestedRecords(): {f: Int, g: {f: Int, h: {}}} {
    return @{ f=1, g=@{ f=2, h=@{} } };
}

entrypoint function nestedTupleRecord(): [Int, {f: Int}] {
    return @[ 1, @{ f=1 } ];
}

entrypoint function nestedRecordTuple(): {f: Int, g: [Int]} {
    return @{ f=1, g=@[ 1 ] };
}

entrypoint function getIndex(): Int {
    return @[ 1 ][0];
}

entrypoint function getIndexOpt(): Int? {
    return @[][1];
}

entrypoint function getIndexBailout(arg?: [Int]): Int? {
    return arg?[0];
}

entrypoint function getField(): Int {
    return @{ f=1 }.f;
}

entrypoint function getFieldOpt(): Int? {
    return @{}.f;
}

entrypoint function getFieldBailout(arg?: {f: Int}): Int? {
    return arg?.f;
}

entrypoint function projectIndecies(): [Int] {
    return @[ 1, 2 ]@[1];
}

entrypoint function projectIndeciesOpt(): [Int, Int?] {
    return @[ 1, 2 ]@[1, 5];
}

entrypoint function projectIndeciesBailout(arg?: [Int]): [Int]? {
    return arg?@[0];
}

entrypoint function projectProperties(): {f: Int} {
    return @{ f=1, g=2 }@{f};
}

entrypoint function projectPropertiesOpt(): {f: Int, h: None} {
    return @{ f=1, g=2 }@{f, h};
}

entrypoint function projectPropertiesBailout(arg?: {f: Int}): {f: Int}? {
    return arg?@{f};
}

entrypoint function projectTupleType(): [Bool] {
    return @[ true, false ]@#[ Bool ];
}

entrypoint function projectTupleTypeOptional(): [Bool, Bool, ?:Int] {
    return @[ true, false ]@#[Bool, Bool, ?:Int];
}

entrypoint function projectTupleTypeOpen(): [Bool, ...] {
    return @[ true, false ]@#[Bool, ...];
}

entrypoint function projectRecordType(): {f: Int} {
    return @{ f=1, g=2 }@#{f:Int};
}

entrypoint function projectRecordTypeOptional(): {f: Int, h?: String} {
    return @{ f=1, g=2 }@#{f:Int, h?:String};
}

entrypoint function projectRecordTypeOpen(): {f:Int, ...} {
    return @{ f=1, g=2 }@#{f:Int, ...};
}

entrypoint function projectTypeBailout(arg?: {f: Int}): { f:Int, ... }? {
    return arg?@#{ f:Int, ... };
}

entrypoint function modifyIndecies(): [Int, Int] {
    return @[ 1, 2 ]<~(1=5);
}

entrypoint function modifyIndeciesOpt(): [Int, Int, None, None, Int] {
    return @[ 1, 2 ]<~(1=5, 4=4);
}

entrypoint function modifyIndeciesBailout(arg?: [Int, Int]): [Int, Int]? {
    return arg?<~(1=5);
}

entrypoint function modifyProperties(): {f: Int, g: Int} {
    return @{f=1, g=2}<~(f=5);
}

entrypoint function modifyPropertiesOpt(): {f: Int, g: Int, h: Int} {
    return @{ f=1, g=2 }<~(f=5, h=3);
}

entrypoint function modifyPropertiesBailout(arg?: {f: Int}): {f: Int}? {
    return arg?<~(f=3);
}

entrypoint function extendTupleType(): [Bool, Bool, Int] {
    return @[ true, false ]<+(@[ 3 ]);
}

entrypoint function extendTupleTypeBailout(arg?: []): [Int]? {
    return arg?<+(@[ 3 ]);
}

entrypoint function extendRecordType(): {f: Int, g: Int} {
    return @{ f=1, g=2 }<+(@{ f=5 });
}

entrypoint function extendRecordTypeWNew(): {f: Int, g: Int, h: Int} {
    return @{ f=1, g=2 }<+(@{ f=5, h=6 });
}

entrypoint function prefixNot(): Bool {
    return !false;
}

entrypoint function prefixNotNone(): Bool {
    return !none;
}

entrypoint function prefixPlus(): Int {
    return +1;
}

entrypoint function prefixNegate(): Int {
    return -1;
}

entrypoint function infixAdd(): Int {
    return 1 + 2;
}

entrypoint function infixSub(): Int {
    return 1 - 2;
}

entrypoint function infixMult(): Int {
    return 1 * 2;
}

entrypoint function infixDiv(): Int {
    return 4 / 2;
}

entrypoint function infixMod(): Int {
    return 3 % 2;
}

entrypoint function infixPrecedence1(): Int {
    return 2 * 3 - 3;
}

entrypoint function infixPrecedence2(): Int {
    return 1 + 2 / 2;
}

entrypoint function eqNoneFalse(): Bool {
    return none == 2;
}

entrypoint function eqNoneTrue(): Bool {
    return none == @{}.f;
}

entrypoint function eqIntTrue(): Bool {
    return 1 == 1;
}

entrypoint function eqIntFalse(): Bool {
    return 1 == 2;
}

entrypoint function eqStringFalse(): Bool {
    return "1" == "";
}

entrypoint function eqStringTrue(): Bool {
    return "hi" == "hi";
}

entrypoint function eqTypedStringTrue(): Bool {
    return 'hello'#Foo == 'hello'#Foo;
}

entrypoint function eqTypedStringMixedTrue(): Bool {
    return 'hello'#Foo == "hello";
}

entrypoint function eqTypedStringMixedFalse(): Bool {
    return 'hello'#Foo == "hi";
}

entrypoint function eqTupleTrue(): Bool {
    return @[1, 2] == @[1, 2];
}

entrypoint function eqTupleFalse(): Bool {
    return @[1] == @[3];
}

entrypoint function eqRecordTrue(): Bool {
    return @{f=2} == @{f=2};
}

entrypoint function eqRecordFalse(): Bool {
    return @{f=2, g=5} == @{f=2, g=1};
}

entrypoint function eqTupleTrue_Mix(): Bool {
    var tup: [Int, Int, ?:String] = (1 != 0) ? @[1, 2] : @[1, 2, "ok"];
    return @[1, 2] == tup;
}

entrypoint function eqTupleFalse_Mix(): Bool {
    var tup: [Int, Int, ?:String] = (1 == 0) ? @[1, 2] : @[1, 2, "ok"];
    return @[1, 2] == tup;
}

entrypoint function eqRecordTrue_Mix(): Bool {
    var rec: {f:Int, g?:Int} = (1 != 0) ? @{f=2} : @{f=2, g=5};
    return @{f=2} == rec;
}

entrypoint function eqRecordFalse_Mix(): Bool {
    var rec: {f:Int, g?:Int} = (1 == 0) ? @{f=2} : @{f=2, g=5};
    return @{f=2} == rec;
}

entrypoint function neqIntTrue(): Bool {
    return 1 != 2;
}

entrypoint function neqIntFalse(): Bool {
    return 1 != 1;
}

entrypoint function ltIntFalse(): Bool {
    return 2 < 1;
}

entrypoint function lteqIntFalse(): Bool {
    return 2 <= 1;
}

entrypoint function ltIntTrue(): Bool {
    return 1 < 2;
}

entrypoint function lteqIntTrue(): Bool {
    return 2 <= 2;
}

entrypoint function ltStringFalseEmpty(): Bool {
    return "" < "";
}

entrypoint function ltStringFalseOne(): Bool {
    return "1" < "";
}

entrypoint function ltStringFalseValues(): Bool {
    return "12" < "11";
}

entrypoint function ltStringTrue(): Bool {
    return "11" < "12";
}

entrypoint function lteqStringTrue(): Bool {
    return "11" <= "11";
}

entrypoint function lteqTypedStringTrue(): Bool {
    return 'hello'#Foo <= 'hello'#Foo;
}

entrypoint function lteqTypedStringMixedTrue(): Bool {
    return 'hello'#Foo <= "hello";
}

entrypoint function ltTypedStringMixedFalse(): Bool {
    return 'hello'#Foo < "h";
}

entrypoint function gtIntFalse(): Bool {
    return 1 > 1;
}

entrypoint function gteqIntFalse(): Bool {
    return 1 >= 2;
}

entrypoint function impliesEasyTrue(): Bool {
    return (1 == 2) ==> (1 == 2);
}

entrypoint function impliesRealTrue(): Bool {
    return (1 == 1) ==> (1 == 1);
}

entrypoint function impliesFalse(): Bool {
    return (1 == 1) ==> (1 == 2);
}

entrypoint function impliesShortEval(): Bool {
    return (1 == 2) ==> (1 == 1);
}

entrypoint function orEasyTrue(): Bool {
    return (1 == 1) || (1 == 2);
}

entrypoint function orRealTrue(): Bool {
    return (1 == 2) || (1 == 1);
}

entrypoint function orFalse(): Bool {
    return (1 == 2) || (1 == 2);
}

entrypoint function orShortEval(): Bool {
    return (1 == 1) || (1 == 2);
}

entrypoint function andEasyFalse(): Bool {
    return (1 == 2) && (1 == 1);
}

entrypoint function andRealFalse(): Bool {
    return (1 == 1) && (1 == 2);
}

entrypoint function andTrue(): Bool {
    return (1 == 1) && (1 == 1);
}

entrypoint function andShortEval(): Bool {
    return (1 == 2) && (1 == 1);
}

entrypoint function logicPrecedenceBasic(): Bool {
    return (1 == 2) || 2 < 3;
}

entrypoint function logicPrecedenceImplies(): Bool {
    return (1 == 1) ==> (1 == 2) || 2 <= 3;
}

entrypoint function logicPrecedenceAndOr(): Bool {
    return (1 == 2) && (1 == 1) || (1 == 1);
}

entrypoint function impliesNone(arg?: Bool): Bool {
    return arg ==> (1 == 2);
}

entrypoint function orNone(arg?: Bool): Bool {
    return arg || (1 == 1);
}

entrypoint function andNone(arg?: Bool): Bool {
    return (1 == 1) && arg;
}

entrypoint function noneCheckYes(arg?: Int): Int? {
    return arg ?& 1;
}

entrypoint function noneCheckNo(arg?: Int): Int? {
    return arg ?& 2;
}

entrypoint function coalesceCheckYes(arg?: Int): Int? {
    return arg ?| 1;
}

entrypoint function coalesceCheckNo(arg?: Int): Int? {
    return arg ?| 2;
}

entrypoint function coalesceCheckOut(arg?: Int): Int? {
    return arg ?| none;
}

entrypoint function selectTrue(): Int {
    return 1 < 2 ? 1 : 2;
}

entrypoint function selectFalse(): Int {
    return 1 > 2 ? 1 : 2;
}

entrypoint function selectNone(arg?: Bool): Int {
    return arg ? 1 : 2;
}

entrypoint function emptyArgsTest(): Int {
    return emptyArgs();
}

entrypoint function requiredArgsTest(): Int {
    return requiredArgs(1, 2);
}

entrypoint function optionalArgsTest0(): Int? {
    return optionalArgs();
}

entrypoint function optionalArgsTest1(): Int? {
    return optionalArgs(1);
}

entrypoint function optionalArgsTest2(): Int? {
    return optionalArgs(1, 2);
}

entrypoint function mixedArgsTest1(): Int {
    return mixedArgs(1);
}

entrypoint function mixedArgsTest2(): Int {
    return mixedArgs(1, 2);
}

entrypoint function optionalArgsNamedTest1(): Int? {
    return optionalArgs(3, v1=1);
}

entrypoint function optionalArgsNamedTest2(): Int? {
    return optionalArgs(v2=1, 3);
}

entrypoint function mixedArgsNamedTest1(): Int {
    return mixedArgs(v1=1);
}

entrypoint function mixedArgsNamedTest2(): Int {
    return mixedArgs(v2=1, v1=2);
}

entrypoint function identityAnyTest(): Int | String {
    var x = identityAny[Int](3);
    return x == 3 ? identityAny[Int | String](1) : 2;
}

entrypoint function identityIntTest(): Int {
    var x = identityInt[Int](3);
    return x == 3 ? identityInt[Int](1) : 2;
}

entrypoint function prePostTest(): Int?
{
    return prePost(3);
}

entrypoint function lambdaTest():Int {
    var f = fn(x: Int): Int => { return x * 2; };
    return f(3);
}

entrypoint function lambdaCaptureTest(): Int {
    var y = 2;
    var f = fn(x: Int): Int => { return x * y; };
    return f(3);
}

entrypoint function lambdaShortTestOk(): Int? {
    var fobj = (1 == 1) ? @{ func=fn(x: Int): Int => { return x * 2; } } : @{ };
    return fobj.func?(3);
}

entrypoint function lambdaShortTestOut(): Int? {
    var fobj = (1 == 2) ? @{ func=fn(x: Int): Int => { return x * 2; } } : @{ };
    return fobj.func?(3);
}

entrypoint function lambdaArgumentTest(): Int {
    return lambdaArgument(fn(x: Int): Int => { return x * 2; }, 3);
}

entrypoint function lambdaArgumentInferTest(): Int {
    return lambdaArgument(fn(x) => { return x * 2; }, 3);
}

entrypoint function lambdaMultiTest():Int {
    var f = (1 == 1) ? fn(x: Int): Int => { return x * 2; } : fn(x: Any): Int => { return 2; };
    return f(3);
}

entrypoint function createObjSimple(): E1 {
    return E1@{ x=none, y=1, z=true, f=3 };
}

entrypoint function createObjDefault(): E1 {
    return E1@{ x=none, z=true, f=3 };
}

entrypoint function createObjExpando(): E1 {
    return E1@{ ...@{ x=none, z=true, f=3 } };
}

entrypoint function createObjFactory(): E1 {
    return E1@create(3);
}

entrypoint function createObjFactoryTemplate(): E1 {
    return E1@creat[String]("ok");
}

entrypoint function createObjTFactory(): E2[Int] {
    return E2[Int]@create(3);
}

entrypoint function createObjTFactoryTemplate(): E2[Int] {
    return E2[Int]@creat[String](3, "ok");
}

entrypoint function getObjFieldF(): Int {
    return E1@create(3).f;
}

entrypoint function getObjFieldX(): Any {
    return E1@create(3).x;
}

entrypoint function getObjFields(): {f: Int, x: Any} {
    return E1@create(3)@{f, x};
}

entrypoint function projectObjType(): {x: Any, y:Int} {
    return E1@create(3)@#Bar;
}

entrypoint function modifyObjFields(): E1 {
    return E1@create(3)<~(f=5, x=false);
}

entrypoint function updateObj(): E1 {
    return E1@create(3)<+(@{ f=5, x=false });
}

entrypoint function restCallSimpleArgsList(): List[Int] {
    return restArgListSimple[Int](1, 1, 2);
}

entrypoint function restCallSimpleArgsSet(): Set[Int] {
    return restArgSetSimple[Int](4, ...List[Int]@{ 1, 2, 3 });
}

entrypoint function restCallOverlapArgsSet(): Set[Int] {
    return restArgSetSimple[Int](2, ...List[Int]@{ 1, 2, 3 });
}

entrypoint function restCallSimpleArgsMap(): Map[Int, Bool] {
    return restArgMapSimple[Int, Bool](@[ 1, false ], @[ 2, true ]);
}

entrypoint function restCallOverlapArgsMap(): Map[Int, Bool] {
    return restArgMapSimple[Int, Bool](@[ 1, false ], @[ 1, true ]);
}

entrypoint function restCallMixedList1(): List[Int] {
    return argListMixed(true, 4, ...List[Int]@{ 1, 2, 3 });
}

entrypoint function restCallMixedList2(): List[Int] {
    return argListMixed(4, v=true, ...List[Int]@{ 1, 2, 3 });
}

entrypoint function createList(): List[Int] {
    return List[Int]@{ 1, 1, 2 };
}

entrypoint function createListExpando(): List[Int] {
    return List[Int]@{...List[Int]@{ 1, 1, 2 }, 4};
}

entrypoint function createSet(): Set[Int] {
    return HashSet[Int]@{ 1, 2, 3 };
}

entrypoint function createSetOverlap(): Set[Int] {
    return HashSet[Int]@{ 1, 2, 3, 2 };
}

entrypoint function createSetExpando(): Set[Int] {
    return HashSet[Int]@{ ...HashSet[Int]@{ 1 }, 2, ...List[Int]@{ 4, 5 } };
}

entrypoint function createMap(): Map[Int, Bool] {
    return HashMap[Int, Bool]@{ @[ 1, true ], @[ 2, true ] };
}

entrypoint function createMapOverlap(): Map[Int, Bool] {
    return HashMap[Int, Bool]@{ @[ 1, true ], @[ 2, false ], @[ 2, true ] };
}

entrypoint function createMapExpando(): Map[Int, Bool] {
    return HashMap[Int, Bool]@{ @[ 1, true ], ...HashMap[Int, Bool]@{ @[ 1, false ], @[ 2, true ] }, @[ 5, true ] };
}

entrypoint function invokee3func(): Int {
    return E3@{}->func(3);
}

entrypoint function invokee4func(): Bool {
    return E4[Int]@{}->func(3);
}

entrypoint function invokerecordfunc(): Int {
    return @{ func=fn(this: Any, x: Int): Int => x + 1 }->func(3);
}

entrypoint function invokee3m1(): Int {
    return E3@{}->m1(3);
}

entrypoint function invokee3ii(): Int {
    return E3@{}->ii(3);
}

entrypoint function invokee3m3(): Int {
    return E3@{}->m3(3);
}

entrypoint function invokee3mc(): Int {
    return E3@{}->mc(3, 5);
}

entrypoint function invokee4m1(): Int {
    return E4[Int]@{}->m1(3);
}

entrypoint function invokee4ii(): Int {
    return E4[Int]@{}->ii(3);
}

entrypoint function invokee4m3(): Int {
    return E4[Int]@{}->m3(3);
}

entrypoint function invokee4mc(): Int {
    return E4[Int]@{}->mc(3);
}

entrypoint function invokee4mcc(): Int {
    return E4[Int]@{}->mcc[Int](3);
}

entrypoint function eblock_4(): Int {
    return {| var x = 3; yield x + 1; |};
}

entrypoint function eblock_5(): Int {
    return {|
        var x = 3;
        var y = 5;
        if(x >= y) {
            yield x;
        }
        yield y;
    |};
}

entrypoint function eblock_3(): Int {
    return {|
        var x = 3;
        var y = {| yield 5; |} == 5 ? 3 : 1;
        yield y;
    |};
}

entrypoint function eif_abs1(): Int {
    var x = -3;
    var y = if(x < 0) -x else x;
    return y;
}

entrypoint function eif_abs2(): Int {
    var x = 3;
    return if(x < 0) {|
        yield -x;
    |}
    else {|
        yield x;
    |};
}

entrypoint function eif_absy_none(): Int {
    var x = (1 > 2) ? 1 : none;
    return if(x == none) 0 else {|
        var! y = x;
        if(y < 0) {
            y = -y;
        }
        yield y;
    |};
}

entrypoint function eif_absy_1(): Int {
    var x = (3 > 2) ? 1 : none;
    return if(x == none)
        0
    else {|
        var! y = x;
        if(y < 0) {
            y = -y;
        }
        yield y;
    |};
}

entrypoint function enestif_abs1(): Int {
    var x = (3 > 2) ? -3 : none;
    var y = if(x == none) 0 else if(x > 0) x else -x;
    return y;
}

function ematch(arg: Any, tv?: Bool): Int {
    return switch(arg) {
        type None => 1
        case 2 => 2
        case @[var x: Int, 3] => {| yield x + 1; |}
        type {f?: Int} => switch(arg.f) {
            case none => 0
            case _ => -1
        }
        case _ => if(tv) 10 else 11
    };
}

entrypoint function ematch_1(): Int {
    return ematch(none);
}

entrypoint function ematch_2(): Int {
    return ematch(2);
}

entrypoint function ematch_3(): Int {
    return ematch(@[2, 3]);
}

entrypoint function ematch_10(): Int {
    return ematch("yes", true);
}

entrypoint function ematch_0(): Int {
    return ematch(@{});
}

entrypoint function ematch_n1(): Int {
    return ematch(@{f=2});
}

entrypoint function ematch_11(): Int {
    return ematch("no", false);
}

entrypoint function ematch_11alt(): Int {
    return ematch("no");
}
`;

const expression_tests: TestInfo[] = [
    { name: "literalNone", input: ["literalNone"], expected: "none" },
    { name: "literalTrue", input: ["literalTrue"], expected: "true" },
    { name: "literalFalse", input: ["literalFalse"], expected: "false" },
    { name: "literal1", input: ["literal1"], expected: "1" },
    { name: "literal3", input: ["literal3"], expected: "3" },
    { name: "literalEmptyString", input: ["literalEmptyString"], expected: "\"\"" },
    { name: "literalHello", input: ["literalHello"], expected: "\"hello\"" },

    { name: "literalFooString", input: ["literalFooString"], expected: "'hello'#NSTestExpression::Foo" },
    { name: "literalFooObject", input: ["literalFooObject"], expected: "NSTestExpression::Foo@{}" },

    { name: "emptyTuple", input: ["emptyTuple"], expected: "@[]" },
    { name: "oneTuple", input: ["oneTuple"], expected: "@[ 1 ]" },
    { name: "fourTuple", input: ["fourTuple"], expected: "@[ 1, 2, none, true ]" },
    { name: "emptyRecord", input: ["emptyRecord"], expected: "@{}" },
    { name: "oneRecord", input: ["oneRecord"], expected: "@{ f=1 }" },
    { name: "fourRecord", input: ["fourRecord"], expected: "@{ f=1, g=2, h=none, k=true }" },
    { name: "nestedTuples", input: ["nestedTuples"], expected: "@[ 1, @[ none, @[] ] ]" },
    { name: "nestedRecords", input: ["nestedRecords"], expected: "@{ f=1, g=@{ f=2, h=@{} } }" },
    { name: "nestedTupleRecord", input: ["nestedTupleRecord"], expected: "@[ 1, @{ f=1 } ]" },
    { name: "nestedRecordTuple", input: ["nestedRecordTuple"], expected: "@{ f=1, g=@[ 1 ] }" },

    { name: "getIndex", input: ["getIndex"], expected: "1" },
    { name: "getIndexOpt", input: ["getIndexOpt"], expected: "none" },
    { name: "getIndexBailout", input: ["getIndexBailout"], expected: "none" },
    { name: "getField", input: ["getField"], expected: "1" },
    { name: "getFieldOpt", input: ["getFieldOpt"], expected: "none" },
    { name: "getFieldBailout", input: ["getFieldBailout"], expected: "none" },

    { name: "projectIndecies", input: ["projectIndecies"], expected: "@[ 2 ]" },
    { name: "projectIndeciesOpt", input: ["projectIndeciesOpt"], expected: "@[ 2, none ]" },
    { name: "projectIndeciesBailout", input: ["projectIndeciesBailout"], expected: "none" },
    { name: "projectProperties", input: ["projectProperties"], expected: "@{ f=1 }" },
    { name: "projectPropertiesOpt", input: ["projectPropertiesOpt"], expected: "@{ f=1, h=none }" },
    { name: "projectPropertiesBailout", input: ["projectPropertiesBailout"], expected: "none" },

    { name: "projectTupleType", input: ["projectTupleType"], expected: "@[ true ]" },
    { name: "projectTupleTypeOptional", input: ["projectTupleTypeOptional"], expected: "@[ true, false ]" },
    { name: "projectTupleTypeOpen", input: ["projectTupleTypeOpen"], expected: "@[ true, false ]" },
    { name: "projectRecordType", input: ["projectRecordType"], expected: "@{ f=1 }" },
    { name: "projectRecordTypeOptional", input: ["projectRecordTypeOptional"], expected: "@{ f=1 }" },
    { name: "projectRecordTypeOpen", input: ["projectRecordTypeOpen"], expected: "@{ f=1, g=2 }" },
    { name: "projectTypeBailout", input: ["projectTypeBailout"], expected: "none" },

    { name: "modifyIndecies", input: ["modifyIndecies"], expected: "@[ 1, 5 ]" },
    { name: "modifyIndeciesOpt", input: ["modifyIndeciesOpt"], expected: "@[ 1, 5, none, none, 4 ]" },
    { name: "modifyIndeciesBailout", input: ["modifyIndeciesBailout"], expected: "none" },
    { name: "modifyProperties", input: ["modifyProperties"], expected: "@{ f=5, g=2 }" },
    { name: "modifyPropertiesOpt", input: ["modifyPropertiesOpt"], expected: "@{ f=5, g=2, h=3 }" },
    { name: "modifyPropertiesBailout", input: ["modifyPropertiesBailout"], expected: "none" },
    { name: "extendTupleType", input: ["extendTupleType"], expected: "@[ true, false, 3 ]" },
    { name: "extendTupleTypeBailout", input: ["extendTupleTypeBailout"], expected: "none" },
    { name: "extendRecordType", input: ["extendRecordType"], expected: "@{ f=5, g=2 }" },
    { name: "extendRecordTypeWNew", input: ["extendRecordTypeWNew"], expected: "@{ f=5, g=2, h=6 }" },

    { name: "prefixNot", input: ["prefixNot"], expected: "true" },
    { name: "prefixNotNone", input: ["prefixNot"], expected: "true" },
    { name: "prefixPlus", input: ["prefixPlus"], expected: "1" },
    { name: "prefixNegate", input: ["prefixNegate"], expected: "-1" },
    { name: "infixAdd", input: ["infixAdd"], expected: "3" },
    { name: "infixSub", input: ["infixSub"], expected: "-1" },
    { name: "infixMult", input: ["infixMult"], expected: "2" },
    { name: "infixDiv", input: ["infixDiv"], expected: "2" },
    { name: "infixMod", input: ["infixMod"], expected: "1" },
    { name: "infixPrecedence1", input: ["infixPrecedence1"], expected: "3" },
    { name: "infixPrecedence2", input: ["infixPrecedence2"], expected: "2" },

    { name: "eqNoneFalse", input: ["eqNoneFalse"], expected: "false" },
    { name: "eqNoneTrue", input: ["eqNoneTrue"], expected: "true" },
    { name: "eqIntTrue", input: ["eqIntTrue"], expected: "true" },
    { name: "eqIntFalse", input: ["eqIntFalse"], expected: "false" },
    { name: "eqStringFalse", input: ["eqStringFalse"], expected: "false" },
    { name: "eqStringTrue", input: ["eqStringTrue"], expected: "true" },
    { name: "eqTypedStringTrue", input: ["eqTypedStringTrue"], expected: "true" },
    { name: "eqTypedStringMixedTrue", input: ["eqTypedStringMixedTrue"], expected: "true" },
    { name: "eqTypedStringMixedFalse", input: ["eqTypedStringMixedFalse"], expected: "false" },
    { name: "eqTupleTrue", input: ["eqTupleTrue"], expected: "true" },
    { name: "eqTupleFalse", input: ["eqTupleFalse"], expected: "false" },
    { name: "eqRecordTrue", input: ["eqRecordTrue"], expected: "true" },
    { name: "eqRecordFalse", input: ["eqRecordFalse"], expected: "false" },
    { name: "eqTupleTrue_Mix", input: ["eqTupleTrue_Mix"], expected: "true" },
    { name: "eqTupleFalse_Mix", input: ["eqTupleFalse_Mix"], expected: "false" },
    { name: "eqRecordTrue_Mix", input: ["eqRecordTrue_Mix"], expected: "true" },
    { name: "eqRecordFalse_Mix", input: ["eqRecordFalse_Mix"], expected: "false" },
    { name: "neqIntTrue", input: ["neqIntTrue"], expected: "true" },
    { name: "neqIntFalse", input: ["neqIntFalse"], expected: "false" },

    { name: "ltIntFalse", input: ["ltIntFalse"], expected: "false" },
    { name: "lteqIntFalse", input: ["lteqIntFalse"], expected: "false" },
    { name: "ltIntTrue", input: ["ltIntTrue"], expected: "true" },
    { name: "lteqIntTrue", input: ["lteqIntTrue"], expected: "true" },
    { name: "ltStringFalseEmpty", input: ["ltStringFalseEmpty"], expected: "false" },
    { name: "ltStringFalseOne", input: ["ltStringFalseOne"], expected: "false" },
    { name: "ltStringFalseValues", input: ["ltStringFalseValues"], expected: "false" },
    { name: "ltStringTrue", input: ["ltStringTrue"], expected: "true" },
    { name: "lteqStringTrue", input: ["lteqStringTrue"], expected: "true" },
    { name: "lteqTypedStringTrue", input: ["lteqTypedStringTrue"], expected: "true" },
    { name: "lteqTypedStringMixedTrue", input: ["lteqTypedStringMixedTrue"], expected: "true" },
    { name: "ltTypedStringMixedFalse", input: ["ltTypedStringMixedFalse"], expected: "false" },
    { name: "gtIntFalse", input: ["gtIntFalse"], expected: "false" },
    { name: "gteqIntFalse", input: ["gteqIntFalse"], expected: "false" },

    { name: "impliesEasyTrue", input: ["impliesEasyTrue"], expected: "true" },
    { name: "impliesRealTrue", input: ["impliesRealTrue"], expected: "true" },
    { name: "impliesFalse", input: ["impliesFalse"], expected: "false" },
    { name: "impliesShortEval", input: ["impliesShortEval"], expected: "true" },
    { name: "orEasyTrue", input: ["orEasyTrue"], expected: "true" },
    { name: "orRealTrue", input: ["orRealTrue"], expected: "true" },
    { name: "orFalse", input: ["orFalse"], expected: "false" },
    { name: "orShortEval", input: ["orShortEval"], expected: "true" },
    { name: "andEasyFalse", input: ["andEasyFalse"], expected: "false" },
    { name: "andRealFalse", input: ["andRealFalse"], expected: "false" },
    { name: "andTrue", input: ["andTrue"], expected: "true" },
    { name: "andShortEval", input: ["andShortEval"], expected: "false" },
    { name: "logicPrecedenceBasic", input: ["logicPrecedenceBasic"], expected: "true" },
    { name: "logicPrecedenceImplies", input: ["logicPrecedenceImplies"], expected: "true" },
    { name: "logicPrecedenceAndOr", input: ["logicPrecedenceAndOr"], expected: "true" },
    { name: "impliesNone", input: ["impliesNone"], expected: "true" },
    { name: "orNone", input: ["orNone"], expected: "true" },
    { name: "andNone", input: ["andNone"], expected: "false" },

    { name: "noneCheckYes", input: ["noneCheckYes"], expected: "none" },
    { name: "noneCheckNo", input: ["noneCheckNo", 1], expected: "2" },
    { name: "coalesceCheckYes", input: ["coalesceCheckYes"], expected: "1" },
    { name: "coalesceCheckNo", input: ["coalesceCheckNo", 1], expected: "1" },
    { name: "coalesceCheckOut", input: ["coalesceCheckOut"], expected: "none" },
    { name: "selectTrue", input: ["selectTrue"], expected: "1" },
    { name: "selectFalse", input: ["selectFalse"], expected: "2" },
    { name: "selectNone", input: ["selectNone"], expected: "2" },

    { name: "emptyArgsTest", input: ["emptyArgsTest"], expected: "0" },
    { name: "requiredArgsTest", input: ["requiredArgsTest"], expected: "3" },
    { name: "optionalArgsTest0", input: ["optionalArgsTest0"], expected: "none" },
    { name: "optionalArgsTest1", input: ["optionalArgsTest1"], expected: "none" },
    { name: "optionalArgsTest2", input: ["optionalArgsTest2"], expected: "3" },
    { name: "mixedArgsTest1", input: ["mixedArgsTest1"], expected: "-1" },
    { name: "mixedArgsTest2", input: ["mixedArgsTest2"], expected: "3" },
    { name: "optionalArgsNamedTest1", input: ["optionalArgsNamedTest1"], expected: "4" },
    { name: "optionalArgsNamedTest2", input: ["optionalArgsNamedTest2"], expected: "4" },
    { name: "mixedArgsNamedTest1", input: ["mixedArgsNamedTest1"], expected: "-1" },
    { name: "mixedArgsNamedTest2", input: ["mixedArgsNamedTest2"], expected: "3" },
    { name: "identityAnyTest", input: ["identityAnyTest"], expected: "1" },
    { name: "identityIntTest", input: ["identityIntTest"], expected: "1" },

    { name: "prePostTest", input: ["prePostTest"], expected: "4" },

    { name: "lambdaTest", input: ["lambdaTest"], expected: "6" },
    { name: "lambdaCaptureTest", input: ["lambdaCaptureTest"], expected: "6" },
    { name: "lambdaShortTestOk", input: ["lambdaShortTestOk"], expected: "6" },
    { name: "lambdaShortTestOut", input: ["lambdaShortTestOut"], expected: "none" },
    { name: "lambdaArgumentTest", input: ["lambdaArgumentTest"], expected: "6" },
    { name: "lambdaArgumentInferTest", input: ["lambdaArgumentInferTest"], expected: "6" },
    { name: "lambdaMultiTest", input: ["lambdaMultiTest"], expected: "6" },

    { name: "createObjSimple", input: ["createObjSimple"], expected: "NSTestExpression::E1@{ f=3, x=none, y=1, z=true }" },
    { name: "createObjDefault", input: ["createObjDefault"], expected: "NSTestExpression::E1@{ f=3, x=none, y=3, z=true }" },
    { name: "createObjExpando", input: ["createObjExpando"], expected: "NSTestExpression::E1@{ f=3, x=none, y=3, z=true }" },
    { name: "createObjFactory", input: ["createObjFactory"], expected: "NSTestExpression::E1@{ f=3, x=none, y=1, z=true }" },
    { name: "createObjFactoryTemplate", input: ["createObjFactoryTemplate"], expected: "NSTestExpression::E1@{ f=3, x=\"ok\", y=1, z=true }" },
    { name: "createObjTFactory", input: ["createObjTFactory"], expected: "NSTestExpression::E2[T=NSCore::Int]@{ f=3, g=1 }" },
    { name: "createObjTFactoryTemplate", input: ["createObjTFactoryTemplate"], expected: "NSTestExpression::E2[T=NSCore::Int]@{ f=3, g=\"ok\" }" },

    { name: "getObjFieldF", input: ["getObjFieldF"], expected: "3" },
    { name: "getObjFieldX", input: ["getObjFieldX"], expected: "none" },
    { name: "getObjFields", input: ["getObjFields"], expected: "@{ f=3, x=none }" },
    { name: "projectObjType", input: ["projectObjType"], expected: "@{ x=none, y=1 }" },
    { name: "modifyObjFields", input: ["modifyObjFields"], expected: "NSTestExpression::E1@{ f=5, x=false, y=1, z=true }" },
    { name: "updateObj", input: ["updateObj"], expected: "NSTestExpression::E1@{ f=5, x=false, y=1, z=true }" },

    { name: "restCallSimpleArgsList", input: ["restCallSimpleArgsList"], expected: "NSCore::List[T=NSCore::Int]@{ 1, 1, 2 }" },
    { name: "restCallSimpleArgsSet", input: ["restCallSimpleArgsSet"], expected: "NSCore::HashSet[T=NSCore::Int]@{ 4, 1, 2, 3 }" },
    { name: "restCallOverlapArgsSet", input: ["restCallOverlapArgsSet"], expected: "NSCore::HashSet[T=NSCore::Int]@{ 1, 2, 3 }" },
    { name: "restCallSimpleArgsMap", input: ["restCallSimpleArgsMap"], expected: "NSCore::HashMap[K=NSCore::Int, V=NSCore::Bool]@{ @[ 1, false ], @[ 2, true ] }" },
    { name: "restCallOverlapArgsMap", input: ["restCallOverlapArgsMap"], expected: "NSCore::HashMap[K=NSCore::Int, V=NSCore::Bool]@{ @[ 1, true ] }" },
    { name: "restCallMixedList1", input: ["restCallMixedList1"], expected: "NSCore::List[T=NSCore::Int]@{ 4, 1, 2, 3 }" },
    { name: "restCallMixedList2", input: ["restCallMixedList2"], expected: "NSCore::List[T=NSCore::Int]@{ 4, 1, 2, 3 }" },

    { name: "createList", input: ["createList"], expected: "NSCore::List[T=NSCore::Int]@{ 1, 1, 2 }" },
    { name: "createListExpando", input: ["createListExpando"], expected: "NSCore::List[T=NSCore::Int]@{ 1, 1, 2, 4 }" },
    { name: "createSet", input: ["createSet"], expected: "NSCore::HashSet[T=NSCore::Int]@{ 1, 2, 3 }" },
    { name: "createSetOverlap", input: ["createSetOverlap"], expected: "NSCore::HashSet[T=NSCore::Int]@{ 1, 3, 2 }" },
    { name: "createSetExpando", input: ["createSetExpando"], expected: "NSCore::HashSet[T=NSCore::Int]@{ 1, 2, 4, 5 }" },
    { name: "createMap", input: ["createMap"], expected: "NSCore::HashMap[K=NSCore::Int, V=NSCore::Bool]@{ @[ 1, true ], @[ 2, true ] }" },
    { name: "createMapOverlap", input: ["createMapOverlap"], expected: "NSCore::HashMap[K=NSCore::Int, V=NSCore::Bool]@{ @[ 1, true ], @[ 2, true ] }" },
    { name: "createMapExpando", input: ["createMapExpando"], expected: "NSCore::HashMap[K=NSCore::Int, V=NSCore::Bool]@{ @[ 1, false ], @[ 2, true ], @[ 5, true ] }" },

    { name: "invokee3func", input: ["invokee3func"], expected: "4" },
    { name: "invokee4func", input: ["invokee4func"], expected: "false" },
    { name: "invokerecordfunc", input: ["invokerecordfunc"], expected: "4" },
    { name: "invokee3m1", input: ["invokee3m1"], expected: "4" },
    { name: "invokee3ii", input: ["invokee3ii"], expected: "3" },
    { name: "invokee3m3", input: ["invokee3m3"], expected: "0" },
    { name: "invokee3mc", input: ["invokee3mc"], expected: "8" },
    { name: "invokee4m1", input: ["invokee4m1"], expected: "4" },
    { name: "invokee4ii", input: ["invokee4ii"], expected: "3" },
    { name: "invokee4m3", input: ["invokee4m3"], expected: "6" },
    { name: "invokee4mc", input: ["invokee4mc"], expected: "0" },
    { name: "invokee4mcc", input: ["invokee4mcc"], expected: "3" },

    { name: "eblock_4", input: ["eblock_4"], expected: "4" },
    { name: "eblock_5", input: ["eblock_5"], expected: "5" },
    { name: "eblock_3", input: ["eblock_3"], expected: "3" },

    { name: "eif_abs1", input: ["eif_abs1"], expected: "3" },
    { name: "eif_abs2", input: ["eif_abs2"], expected: "3" },
    { name: "eif_absy_none", input: ["eif_absy_none"], expected: "0" },
    { name: "eif_absy_1", input: ["eif_absy_1"], expected: "1" },
    { name: "enestif_abs1", input: ["enestif_abs1"], expected: "3" },

    { name: "ematch_1", input: ["ematch_1"], expected: "1" },
    { name: "ematch_2", input: ["ematch_2"], expected: "2" },
    { name: "ematch_3", input: ["ematch_3"], expected: "3" },
    { name: "ematch_10", input: ["ematch_10"], expected: "10" },
    { name: "ematch_0", input: ["ematch_0"], expected: "0" },
    { name: "ematch_n1", input: ["ematch_n1"], expected: "-1" },
    { name: "ematch_11", input: ["ematch_11"], expected: "11" },
    { name: "ematch_11", input: ["ematch_11"], expected: "11" }
];

function expression_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "basic_expression_test.bsq", contents: expression_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function expression_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestExpression", args[0], args.slice(1) as Value[]));
}

const testExpression = { name: "Basic Expression", setup: expression_setup, action: expression_action, tests: expression_tests, xmlid: "ExpressionUnitTests" };

const statement_test = `
namespace NSTestStatement;

global nsconst1: Int = 3;
global nsconst2: Int = 3;

entity SE {
    const sconst1: Int = 3;
    const sconst2: Int = 3;
}

entrypoint function constDeclNoType(): Int {
    var x = 3;
    return x;
}

entrypoint function constDeclWithType(): Int {
    var x: Int = 3;
    return x;
}

entrypoint function constDeclWithUnionType(): Int {
    var x: Int | String = 3;
    return x;
}

entrypoint function varDeclWithType(): Int {
    var! x: Int = 3;
    return x;
}

entrypoint function varDeclWithNoValue(): Int {
    var! x: Int?;
    return 1;
}

entrypoint function varDeclAndAssignWithType(): Int {
    var! x: Int = 3;
    x = 4;
    return x;
}

entrypoint function varDeclAndAssignNoType(): Int {
    var! x = 3;
    x = 4;
    return x;
}

entrypoint function varDeclAndAssignWithNoValue(): Int? {
    var! x: Int?;
    x = 5;
    return x;
}

entrypoint function structuredDeclTuple(): Int {
    @[var x: Int, var y] = @[1, 2];
    return x + y;
}

entrypoint function structuredDeclMutableTuple(): Int {
    @[var! x: Int, var! y] = @[1, 2];
    x = x + 1;
    y = y + 1;
    return x + y;
}

entrypoint function structuredAssignTuple(): Int {
    var! x: Int = 4;
    var! y: Int;

    @[x, y] = @[1, 2];
    return x + y;
}

entrypoint function structuredDeclRecord(): Int {
    @{f=var x: Int, g=var y} = @{f=1, g=2};
    return x + y;
}

entrypoint function structuredDeclMutableRecord(): Int {
    @{f=var! x: Int, g=var! y} = @{f=1, g=2};
    return x + y;
}

entrypoint function structuredAssignRecord(): Int {
    var! x: Int = 4;
    var! y: Int;

    @{f=x, g=y} = @{f=1, g=2};
    return x + y;
}

entrypoint function structuredDeclAndAssign(): Int {
    var! y: Int;

    @[var x: Int, y] = @[1, 2];
    return x + y;
}

entrypoint function structuredDeclGlobal(): Int {
    var @{f=x, g=y} = @{f=1, g=2};
    return x + y;
}

entrypoint function structuredDeclGlobalMutable(): Int {
    var! @{f=x: Int, g=y} = @{f=1, g=2};
    x = x + 1;
    y = y + 1;
    return x + y;
}

entrypoint function structuredRecordWithTuple(): Int {
    var @{f=x, g=@[y, z]} = @{f=1, g=@[2, 3]};
    return x + y + z;
}

entrypoint function structuredTupleWithRecord(): Int {
    var @[x, @{f=y, g=z}] = @[1, @{f=2, g=3}];
    return x + y + z;
}

entrypoint function structuredDeclAndAssignOptionalsMatch(): Int {
    var @{f=x?: Int, g=y?} = @{f=1, g=2};
    return x + y;
}

entrypoint function structuredDeclAndAssignOptionalsDefault(): Int {
    var @{f=x?: Int, g=y?} = (0 < 1) ? @{} : @{f=1, g=2};
    return (x ?| 1) + (y ?| 2);
}

entrypoint function structuredDeclAndAssignOpenTuple(): Int {
    @[var x: Int, var y, ...] = @[1, 2, 4];
    return x + y;
}

entrypoint function structuredDeclAndAssignOpenRecord(): Int {
    var @{f=x, g=y, ...} = @{f=1, h=12, g=2};
    return x + y;
}

entrypoint function structuredDeclAndAssignIgnores(): Int {
    var @{f=_, g=@[y, _:Int]} = @{f=1, g=@[2, 3]};
    return y;
}

entrypoint function ifAssignInBranches(): Int | Bool | None {
    var x = 1;

    var! y: Int | Bool | None = none;
    if (x == 0) {
        y = true;
    }
    else {
        y = 1;
    }

    return y;
}

entrypoint function ifReAssignInBranches(): Int {
    var x = 0;

    var! y = 5;
    if (x == 0) {
        y = 2;
    }
    else {
        y = 1;
    }

    return y;
}

entrypoint function ifReturnInBranches(): Int {
    var x = 1;

    if (x == 0) {
        return 5;
    }
    else {
        return 1;
    }
}

entrypoint function ifEarlyReturnYes(): Bool {
    var x: Int = 1;

    if (x == 1) {
        return true;
    }

    return false;
}

entrypoint function ifEarlyReturnNo(): Bool {
    var x = 1;

    if (x == 0) {
        return true;
    }

    return false;
}

entrypoint function ifReturnInElifBranch(): Int {
    var x: Int = 1;

    if (x == 0) {
        return 8;
    }
    elif (x == 1) {
        return x;
    }
    else {
        return 5;
    }
}

function switchCaseInt(x: Int): Int {
    switch(x) {
        case 1 => { return 1; }
        case 2 => { return 2; }
        case 3 => { return 3; }
        case _ => { ; }
    }

    return x;
}

function switchCaseMixedTypes(x: Any): Int {
    switch(x) {
        case none => { return 1; }
        case @[1, 2] => { return 2; }
        case @{f=1} => { return 3; }
        case "ok" => { return 4; }
        case _ => { ; }
    }

    return 31;
}

function switchCaseBindTypes(x: Any): Int {
    var! z: Int;
    switch(x) {
        case @[1, var y: Int] => { return y; }
        case @[2, var! y: Int] => { return y; }
        case @[3, _:Int, var y: Int] => { return y; }
        case @[3, _:Int, var y: Int, ...] => { return y; }
        case @{f=1, g=var y: Int} => { return y; }
        case var @{f=2, g=y: Int} => { return y; }
        case @{f=3, g=z} => { return z; }
        case var y: Int => { return y; }
        case _ => { ; }
    }

    return 31;
}

function switchCaseBindWhen(x: Any): Int {
    var! z: Int;
    switch(x) {
        case @[1, var y: Int] when y > 0 => { return y; }
        case @[1, var y: Int] when y <= 0 => { return 0; }
        case @[2, var y?: Int] => { return y ?| 20; }
        case @[2, var y: Int, z] => { return y + z; }
        case _ => { ; }
    }

    return 31;
}

function switchCaseType(x: Any): Int {
    switch(x) {
        type Int => { return 1; }
        type [Int, Int] => { return 2; }
        type {f:Int, g?:Int} => { return x.g ?| x.f; }
        case _ => { ; }
    }

    return 31;
}

function switchCaseTypeWhen(x: Any): Int {
    switch(x) {
        type Int when x > 0 => { return x; }
        type Int => { return -x; }
        type {f:Int, g?:Int} when x.f == 10 => { return x.f; }
        case _ => { ; }
    }

    return 31;
}

function switchCaseEx(x: Any): Any {
    switch(x) {
        type Int => { return 0; }
        type Bool => { return false; }
    }
}

entrypoint function switchCaseInt_1(): Int {
    return switchCaseInt(1);
}

entrypoint function switchCaseInt_2(): Int {
    return switchCaseInt(2);
}

entrypoint function switchCaseInt_3(): Int {
    return switchCaseInt(3);
}

entrypoint function switchCaseInt_x(): Int {
    return switchCaseInt(5);
}

entrypoint function switchCaseAny_none(): Int {
    return switchCaseMixedTypes(none);
}

entrypoint function switchCaseAny_tup(): Int {
    return switchCaseMixedTypes(@[1,2]);
}

entrypoint function switchCaseAny_rec(): Int {
    return switchCaseMixedTypes(@{f=1});
}

entrypoint function switchCaseAny_string(): Int {
    return switchCaseMixedTypes("ok");
}

entrypoint function switchCaseAny_x(): Int {
    return switchCaseMixedTypes("fallthrough");
}

entrypoint function switchCaseBindTypes_1(): Int {
    return switchCaseBindTypes(@[1, 1]);
}

entrypoint function switchCaseBindTypes_2(): Int {
    return switchCaseBindTypes(@[1, 2]);
}

entrypoint function switchCaseBindTypes_3(): Int {
    return switchCaseBindTypes(@[3, 5, 3]);
}

entrypoint function switchCaseBindTypes_4(): Int {
    return switchCaseBindTypes(@[3, 5, 4, 7, 11]);
}

entrypoint function switchCaseBindTypes_5(): Int {
    return switchCaseBindTypes(@{f=1, g=5});
}

entrypoint function switchCaseBindTypes_6(): Int {
    return switchCaseBindTypes(@{f=2, g=6});
}

entrypoint function switchCaseBindTypes_7(): Int {
    return switchCaseBindTypes(@{f=3, g=7});
}

entrypoint function switchCaseBindTypes_8(): Int {
    return switchCaseBindTypes(8);
}

entrypoint function switchCaseBindWhen_1(): Int {
    return switchCaseBindWhen(@[1, 1]);
}

entrypoint function switchCaseBindWhen_0(): Int {
    return switchCaseBindWhen(@[1, -1]);
}

entrypoint function switchCaseBindWhen_5(): Int {
    return switchCaseBindWhen(@[2, 5]);
}

entrypoint function switchCaseBindWhen_20(): Int {
    return switchCaseBindWhen(@[2]);
}

entrypoint function switchCaseBindWhen_101(): Int {
    return switchCaseBindWhen(@[2, 1, 100]);
}

entrypoint function switchCaseType_1(): Int {
    return switchCaseType(3);
}

entrypoint function switchCaseType_2(): Int {
    return switchCaseType(@[1, 2]);
}

entrypoint function switchCaseType_3(): Int {
    return switchCaseType(@{f=3});
}

entrypoint function switchCaseType_4(): Int {
    return switchCaseType(@{f=3, g=4});
}

entrypoint function switchCaseType_31(): Int {
    return switchCaseType(true);
}

entrypoint function switchCaseTypeWhen_10(): Int {
    return switchCaseTypeWhen(10);
}

entrypoint function switchCaseTypeWhen_3(): Int {
    return switchCaseTypeWhen(-3);
}

entrypoint function switchCaseTypeWhen_10v1(): Int {
    return switchCaseTypeWhen(@{f=10});
}

entrypoint function switchCaseTypeWhen_10v2(): Int {
    return switchCaseTypeWhen(@{f=10, g=3});
}

entrypoint function switchCaseTypeWhen_31v1(): Int {
    return switchCaseTypeWhen(@{f=10, g=true});
}

entrypoint function switchCaseTypeWhen_31v2(): Int {
    return switchCaseTypeWhen(@{f=20});
}

entrypoint function switchCaseTypeWhen_31v3(): Int {
    return switchCaseTypeWhen("ok");
}

entrypoint function switchCaseEx_0(): Any {
    return switchCaseEx(5);
}

entrypoint function switchCaseEx_false(): Any {
    return switchCaseEx(true);
}

entrypoint function switchCaseEx_error(): Any {
    return switchCaseEx(@{});
}

entrypoint function abortOk(): Int {
    if(1 < 2) {
        return 1;
    }
    else {
        abort;
    }
}

entrypoint function abortFail(): Int {
    if(1 == 2) {
        return 1;
    }
    else {
        abort;
    }
}

entrypoint function assertOk(): Int {
    assert 1 < 2;
    return 1;
}

entrypoint function assertFail(): Int {
    assert 1 > 2;
    return 1;
}

entrypoint function checkOk(): Int {
    check 1 < 2;
    return 1;
}

entrypoint function checkFail(): Int {
    check 1 > 2;
    return 1;
}

entrypoint function namespaceConstEval(): Int {
    var y = NSTestStatement::nsconst1;
    var x: Int = NSTestStatement::nsconst2;

    if (x == 0) {
        return 7;
    }
    elif (x == 1) {
        return x;
    }
    else {
        return x + y;
    }
}

entrypoint function staticConstEval(): Int {
    var y = SE::sconst1;
    var x: Int = SE::sconst2;

    if (x == 0) {
        return 7;
    }
    elif (x == 1) {
        return x;
    }
    else {
        return x + y;
    }
}
`;

const statement_tests: TestInfo[] = [
    { name: "constDeclNoType", input: ["constDeclNoType"], expected: "3" },
    { name: "constDeclWithType", input: ["constDeclWithType"], expected: "3" },
    { name: "constDeclWithUnionType", input: ["constDeclWithUnionType"], expected: "3" },
    { name: "varDeclWithType", input: ["varDeclWithType"], expected: "3" },
    { name: "varDeclWithNoValue", input: ["varDeclWithNoValue"], expected: "1" },
    { name: "varDeclAndAssignWithType", input: ["varDeclAndAssignWithType"], expected: "4" },
    { name: "varDeclAndAssignNoType", input: ["varDeclAndAssignNoType"], expected: "4" },
    { name: "varDeclAndAssignWithNoValue", input: ["varDeclAndAssignWithNoValue"], expected: "5" },

    { name: "structuredDeclTuple", input: ["structuredDeclTuple"], expected: "3" },
    { name: "structuredDeclMutableTuple", input: ["structuredDeclMutableTuple"], expected: "5" },
    { name: "structuredAssignTuple", input: ["structuredAssignTuple"], expected: "3" },
    { name: "structuredDeclRecord", input: ["structuredDeclRecord"], expected: "3" },
    { name: "structuredDeclMutableRecord", input: ["structuredDeclMutableRecord"], expected: "3" },
    { name: "structuredAssignRecord", input: ["structuredAssignRecord"], expected: "3" },
    { name: "structuredDeclAndAssign", input: ["structuredDeclAndAssign"], expected: "3" },
    { name: "structuredDeclGlobal", input: ["structuredDeclGlobal"], expected: "3" },
    { name: "structuredDeclGlobalMutable", input: ["structuredDeclGlobalMutable"], expected: "5" },
    { name: "structuredRecordWithTuple", input: ["structuredRecordWithTuple"], expected: "6" },
    { name: "structuredTupleWithRecord", input: ["structuredTupleWithRecord"], expected: "6" },
    { name: "structuredDeclAndAssignOptionalsMatch", input: ["structuredDeclAndAssignOptionalsMatch"], expected: "3" },
    { name: "structuredDeclAndAssignOptionalsDefault", input: ["structuredDeclAndAssignOptionalsDefault"], expected: "3" },

    { name: "structuredDeclAndAssignOpenTuple", input: ["structuredDeclAndAssignOpenTuple"], expected: "3" },
    { name: "structuredDeclAndAssignOpenRecord", input: ["structuredDeclAndAssignOpenRecord"], expected: "3" },
    { name: "structuredDeclAndAssignIgnores", input: ["structuredDeclAndAssignIgnores"], expected: "2" },

    { name: "ifAssignInBranches", input: ["ifAssignInBranches"], expected: "1" },
    { name: "ifReAssignInBranches", input: ["ifReAssignInBranches"], expected: "2" },
    { name: "ifReturnInBranches", input: ["ifReturnInBranches"], expected: "1" },
    { name: "ifEarlyReturnYes", input: ["ifEarlyReturnYes"], expected: "true" },
    { name: "ifEarlyReturnNo", input: ["ifEarlyReturnNo"], expected: "false" },
    { name: "ifReturnInElifBranch", input: ["ifReturnInElifBranch"], expected: "1" },

    { name: "switchCaseInt_1", input: ["switchCaseInt_1"], expected: "1" },
    { name: "switchCaseInt_2", input: ["switchCaseInt_2"], expected: "2" },
    { name: "switchCaseInt_3", input: ["switchCaseInt_3"], expected: "3" },
    { name: "switchCaseInt_x", input: ["switchCaseInt_x"], expected: "5" },

    { name: "switchCaseAny_none", input: ["switchCaseAny_none"], expected: "1" },
    { name: "switchCaseAny_tup", input: ["switchCaseAny_tup"], expected: "2" },
    { name: "switchCaseAny_rec", input: ["switchCaseAny_rec"], expected: "3" },
    { name: "switchCaseAny_string", input: ["switchCaseAny_string"], expected: "4" },
    { name: "switchCaseAny_x", input: ["switchCaseAny_x"], expected: "31" },

    { name: "switchCaseBindTypes_1", input: ["switchCaseBindTypes_1"], expected: "1" },
    { name: "switchCaseBindTypes_2", input: ["switchCaseBindTypes_2"], expected: "2" },
    { name: "switchCaseBindTypes_3", input: ["switchCaseBindTypes_3"], expected: "3" },
    { name: "switchCaseBindTypes_4", input: ["switchCaseBindTypes_4"], expected: "4" },
    { name: "switchCaseBindTypes_5", input: ["switchCaseBindTypes_5"], expected: "5" },
    { name: "switchCaseBindTypes_6", input: ["switchCaseBindTypes_6"], expected: "6" },
    { name: "switchCaseBindTypes_7", input: ["switchCaseBindTypes_7"], expected: "7" },
    { name: "switchCaseBindTypes_8", input: ["switchCaseBindTypes_8"], expected: "8" },

    { name: "switchCaseBindWhen_1", input: ["switchCaseBindWhen_1"], expected: "1" },
    { name: "switchCaseBindWhen_0", input: ["switchCaseBindWhen_0"], expected: "0" },
    { name: "switchCaseBindWhen_5", input: ["switchCaseBindWhen_5"], expected: "5" },
    { name: "switchCaseBindWhen_20", input: ["switchCaseBindWhen_20"], expected: "20" },
    { name: "switchCaseBindWhen_101", input: ["switchCaseBindWhen_101"], expected: "101" },

    { name: "switchCaseType_1", input: ["switchCaseType_1"], expected: "1" },
    { name: "switchCaseType_2", input: ["switchCaseType_2"], expected: "2" },
    { name: "switchCaseType_3", input: ["switchCaseType_3"], expected: "3" },
    { name: "switchCaseType_4", input: ["switchCaseType_4"], expected: "4" },
    { name: "switchCaseType_31", input: ["switchCaseType_31"], expected: "31" },

    { name: "switchCaseTypeWhen_10", input: ["switchCaseTypeWhen_10"], expected: "10" },
    { name: "switchCaseTypeWhen_3", input: ["switchCaseTypeWhen_3"], expected: "3" },
    { name: "switchCaseTypeWhen_10v1", input: ["switchCaseTypeWhen_10v1"], expected: "10" },
    { name: "switchCaseTypeWhen_10v2", input: ["switchCaseTypeWhen_10v2"], expected: "10" },

    { name: "switchCaseTypeWhen_31v1", input: ["switchCaseTypeWhen_31v1"], expected: "31" },
    { name: "switchCaseTypeWhen_31v2", input: ["switchCaseTypeWhen_31v2"], expected: "31" },
    { name: "switchCaseTypeWhen_31v3", input: ["switchCaseTypeWhen_31v3"], expected: "31" },

    { name: "switchCaseEx_0", input: ["switchCaseEx_0"], expected: "0" },
    { name: "switchCaseEx_false", input: ["switchCaseEx_false"], expected: "false" },
    { name: "switchCaseEx_error", input: ["switchCaseEx_error"], expected: "[NO RESULT]", expectedError: true },

    { name: "abortOk", input: ["abortOk"], expected: "1" },
    { name: "abortFail", input: ["abortFail"], expected: "[NO RESULT]", expectedError: true },
    { name: "assertOk", input: ["assertOk"], expected: "1" },
    { name: "assertFail", input: ["assertFail"], expected: "[NO RESULT]", expectedError: true },
    { name: "checkOk", input: ["checkOk"], expected: "1" },
    { name: "checkFail", input: ["checkFail"], expected: "[NO RESULT]", expectedError: true },

    { name: "namespaceConstEval", input: ["namespaceConstEval"], expected: "6" },
    { name: "staticConstEval", input: ["staticConstEval"], expected: "6" }
];

function statement_setup(core: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
    const files = core.concat([{ relativePath: "basic_statement_test.bsq", contents: statement_test }]);

    return MIREmitter.generateMASM(new PackageConfig(), files);
}

function statement_action(assembly: MIRAssembly, args: any[]): any {
    let ip = new Interpreter(assembly, true, true, true);
    return ValueOps.diagnosticPrintValue(ip.evaluateRootNamespaceCall("NSTestStatement", args[0], []));
}

const testStatement = { name: "Basic Statement", setup: statement_setup, action: statement_action, tests: statement_tests, xmlid: "StatementUnitTests" };

export { testExpression, testStatement };
