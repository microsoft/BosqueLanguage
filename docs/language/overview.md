# Bosque Language Overview

The Bosque language derives from a combination of [TypeScript](https://www.typescriptlang.org/) inspired syntax and types plus [ML](https://www.smlnj.org/) and [Node/JavaScript](https://nodejs.org/en/) inspired semantics. This document provides an overview of the syntax, operations, and semantics in the Bosque language with an emphasis on the distinctive or unusual features in the language.

# Table of Contents

- [0 Highlight Features](#0-Highlight-Features)
  - [0.1 Immutable Values](#0.1-Immutable-Values)
  - [0.2 Block Scoping](#0.2-Block-Scoping)
  - [0.3 Reference Parameter Threading](#0.3-Reference-Parameter-Threading)
  - [0.4 Typed Strings](#0.4-Typed-Strings)
  - [0.5 Flexible Invocations](#0.5-Flexible-Invocations)
  - [0.6 Bulk Algebraic Data Operations](#0.6-Bulk-Algebraic-Data-Operations)
  - [0.7 None Processing](#0.7-None-Processing)
  - [0.8 Iterative Processing](#0.8-Iterative-Processing)
  - [0.9 Recursion](#0.9-Recursion)
  - [0.10 Determinacy](#0.10-Determinacy)
  - [0.11 Equality and Representation](#0.11-Equality-and-Representation)
  - [0.12 Errors and Checks](#0.12-Errors-and-Checks)
  - [0.13 Atomic Constructors and Factories](#0.13-Atomic-Constructors-and-Factories)
  - [0.14 Synthesis Blocks](#0.14-Synthesis-Blocks)
- [1 Type System](#1-Type-System)
  - [1.1 Nominal Types](#1.1-Nominal-Types)
  - [1.2 Structural Types](#1.2-Structural-Types)
  - [1.3 Function Types](#1.3-Function-Types)
  - [1.4 Combination Types](#1.4-Combination-Types)
  - [1.5 Generics](#1.5-Generics)
- [2 Core Types](#2-Core-Types)
- [3 Collections](#3-Collections)
- [4 Type Checking](#4-Type-Checking)
- [5 Expressions](#5-Expressions)
  - [5.1 Arguments](#5.1-Arguments)
  - [5.2 Constants](#5.2-Constants)
  - [5.3 Variable and Scoped Access](#5.3-Variable-and-Scoped-Access)
  - [5.4 Tuple and Record Constructors](#5.4-Tuple-and-Record-Constructors)
  - [5.5 Entity Constructors](#5.5-Entity-Constructors)
  - [5.6 Lambda Constructors](#5.6-Lambda-Constructors)
  - [5.7 Scoped Invokes](#5.7-Scoped-Invokes)
  - [5.8 None-Chaining](#5.8-Chaining-and-None-Chaining)
  - [5.9 Tuple Typed Access Operators](#5.9-Tuple-Typed-Access-Operators)
  - [5.10 Record Typed Access Operators](#5.10-Record-Typed-Access-Operators)
  - [5.11 Nominal Typed Access Operators](#5.11-Nominal-Typed-Access-Operators)
  - [5.12 Typed Projection](#5.12-Typed-Projection)
  - [5.13 Difference](#5.13-Difference)
  - [5.14 Update](#5.14-Update)
  - [5.15 Merge](#5.15-Merge)
  - [5.16 Lambda Apply](#5.16-Lambda-Apply)
  - [5.17 Invoke](#5.17-Invoke)
  - [5.18 Pipeline](#5.18-Pipeline)
  - [5.19 Unary Operators](#5.19-Unary-Operators)
  - [5.20 Binary Operators](#5.20-Binary-Operators)
  - [5.21 Equality Comparison](#5.21-Equality-Comparison)
  - [5.22 Order Comparison](#5.22-Order-Comparison)
  - [5.23 Logic Operators](#5.23-Logic-Operators)
  - [5.24 None Coalescing](#5.24-None-Coalescing)
  - [5.25 Select](#5.25-Select)
  - [5.26 Statement Expressions](#5.26-Statement-Expressions)
  - [5.27 Thunk Blocks](#5.27-Thunk-Blocks)
  - [5.28 Synthesis Blocks](#5.28-Synthesis-Blocks)
- [6 Statements](#6-Statements)
  - [6.1 Empty](#6.1-Empty)
  - [6.2 Variable Declaration](#6.2-Variable-Declaration)
  - [6.3 Variable Assignment](#6.3-Variable-Assignment)
  - [6.4 Structured Declaration and Assignment](#6.4-Structured-Declaration-and-Assignment)
  - [6.5 Return and Yield](#6.5-Return-and-Yield)
  - [6.6 Validation](#6.6-Validation)
  - [6.7 If-Then-Else](#6.7-If-Then-Else)
  - [6.8 Match](#6.8-Match)
  - [6.9 Block](#6.9-Block)
- [7 Invokable Declarations](#7-Invokable-Declarations)
- [8 Concept and Entity Declarations](#8-Concept-and-Entity-Declarations)
- [9 Namespace Declarations](#9-Namespace-Declarations)

# <a name="0-Highlight-Features"></a>0 Highlight Features

The Bosque programming language is designed for writing code that is simple, obvious, and easy to reason about for both humans and machines. The design was driven heavily by the identification and elimination of various sources of _accidental complexity_ and insights on how they can be alleviated via the thoughtful language design.

This section highlights and contains information on many of the most notable and/or unique features and design choices in the Bosque programming language.

## <a name="0.1-Immutable-Values"></a>0.1 Immutable Values

All values in the Bosque language are immutable!

Reasoning about and understanding the effect of a statement or block of code is greatly simplified when it is side-effect free. Functional languages have long benefited from the simplifications to program development, sophisticated tooling, and aggressive compiler optimizations that this model allows. From this perspective the natural choice for the Bosque language is to adopt a pure functional model with immutable data only.

## <a name="0.2-Block-Scoping"></a>0.2 Block Scoping

Local variables with block structured code is a very appealing model for structuring code. The Bosque language fuses functional programming with block scopes and `{...}` braces by allowing multiple assignments to updatable variables `var!` ([6.3 Variable Assignment](#6.3-Variable-Assignment)). This supports functional style programming in a block-scoped language and allows developers to write code such as:

```none
function abs(x: Int): Int {
    var! sign = 1; //declare updatable variable with initial value
    if(x < 0) {
        sign = -1; //update the variable
    }

    return x * sign;
}
```

## <a name="0.3-Reference-Parameter-Threading"></a>0.3 Reference Parameter Threading

**[NOT IMPLEMENTED YET]**

In addition to allowing multiple assignments to variables, the Bosque language also allows developers to thread parameters via `ref` argument passing. This alternative to multi-return values simplifies scenarios where a variable (often some sort of environment) is passed to a method which may use and update it. Allowing the update in the parameter eliminates the extra return value management that would otherwise be needed:

```none
function internString(ref env: Map<String, Int>, str: String): Int {
    if(env.has(str)) {              //use the ref parameter
        return env.get(str);
    }

    env = env.add(str, env.size()); //update the ref parameter
    return env.size();
}
```

## <a name="0.4-Typed-Strings"></a>0.4 Typed Strings

Typed strings provide a novel mechanism for lifting known structure about the contents of a string into the type in a way that is meaningful to humans and that can be used by the type checker ([1.1.2 Typed Strings](#1.1.2-Typed-Strings)). This allows for code such as the following:

```none
function foo(zip: String[Zipcode], name: String) {...}

var zc: String[Zipcode] = ...;
var user: String = ...;

foo(user, zc); //Type error String not convertible to String[Zipcode]
foo(zc, user); //ok
```

## <a name="0.5-Flexible-Invocations"></a>0.5 Flexible Invocations

Bosque provides _named arguments_ along with _rest_ and _spread_ operators. These can be used to perform simple and powerful data manipulation as part of invocations and constructor operations ([5.1 Arguments](#5.1-Arguments)).

```none
function nsum(d: Int, ...args: List[Int]): Int {
    return args.sum(default=d);
}

function np(p1: Int, p2: Int): {x: Int, y: Int} {
    return @{x=p1, y=p2};
}

//calls with explicit arguments
var x = nsum(0, 1, 2, 3); //returns 6

var a = np(1, 2);         //returns @{x=1, y=2}
var b = np(p2=2, 1);      //also returns @{x=1, y=2}

//calls with spread arguments
var t = @[1, 2, 3];
var p = nsum(0, ...t);    //returns 6 -- same as explicit call

var r = @{p1=1, p2=2};
var q = np(...r);         //returns @{x=1, y=2} -- same as explicit call
```

## <a name="0.6-Bulk-Algebraic-Data-Operations"></a>0.6 Bulk Algebraic Data Operations

Bulk algebraic operations in Bosque start with support for bulk reads and updates to data values. Consider the common case of having a struct with 3 fields where 2 of them need to be updated. In most languages this would need to be done on a field-by-field basis. However with the bulk data operations it is possible to perform the update as an atomic operation (unlike in an imperative style) and without manually extracting and copying fields (like in a functional style).

```none
var x = @{f=1, g=2, h=3};
x<~(f=-1, g=-2); //@{f=-1, @g=-2, h=3}
```

In addition to eliminating opportunities to forget or confuse a field these operators help focus the code on the overall intent, instead of being hidden in the individual steps, and allow a developer to perform algebraic reasoning on the data structure operations. Bosque provides several flavors of these algebraic operations for various data types, tuples, records, and nominal types, and for various operations including projection, multi-update, and merge.

```none
var l = @[7, 8, 9];
var r = @{f=7, g=8};

l@[0, 2];     //@[7, 9]
l<+(@[5, 6]); //@[7, 8, 9, 5, 6]
l#[Int, Int]; //@[7, 8]

r@{f, h};         //@{f=7, h=none}
r<~(f=5, h=1);    //@{f=5, g=8, h=1}
r<+(@{f=5, h=1}); //@{f=5, g=8, h=1}
```

## <a name="0.7-None-Processing"></a>0.7 None Processing

Handling `none` values is a relatively common task that can obscure the fundamental intent of a section of code with nests of cases and conditional handling for the special case. To simplify this type of code, Bosque includes various forms of _coalescing_ or _short-circuit_ operators ([5.8 Chaining and None Chaining](#5.8-Chaining-and-None-Chaining)) to enable code like:

```none
function foo(val?: {tag: Int, value?: String}): String {
    return val?.value ?| "[No Value]";
}
```

## <a name="0.8-Iterative-Processing"></a>0.8 Iterative Processing

A fundamental concept in a programming language is the iteration construct and a critical question is should this construct be provided as high-level functors, such as filter/map/reduce, or do programmers benefit from the flexibility available with iterative, while or for, looping constructs. To answer this question in a definitive manner the authors of [Mining Semantic Loop Idioms](https://www.microsoft.com/en-us/research/uploads/prod/2018/10/LoopIdioms.pdf) engaged in a study of all the loops "idioms" found in real-world code. The categorization and coverage results showed that almost every loop a developer would want to write falls into a small number of idiomatic patterns which correspond to higher level concepts developers are using in the code, e.g., filter, find, group, map, etc. With this result in mind the Bosque language trades structured loops for a set of high-level iterative processing constructs ([3 Collections](#3-Collections) and [5.18 Pipeline](#5.18-Pipeline)).

```none
var v: List[Int?] = List@{1, 2, none, 4};

//Chained - List@{1, 4, 16}
v->filter(fn(x) => x != none)->map[Int](fn(x) => x*x);

//Piped none filter - List@{1, 4, 16}
v |> filter(fn(x) => x != none) |> map[Int](fn(x) => x*x);

//Piped with noneable filter - List@{1, 4, 16}
v |??> map[Int](fn(x) => x*x);

//Piped with none to result - List@{1, 4, none, 16}
v |?> map[Int](fn(x) => x*x);
```

Eliminating the boilerplate of writing the same loops repeatedly eliminates whole classes of errors including, e.g. bounds computations, and makes the intent clear with a descriptively named functor instead of relying on a shared set of mutually known loop patterns. Critically, for enabling automated program validation and optimization, eliminating loops also eliminates the need for computing loop-invariants. Instead, and with a careful design of the collection libraries, it is possible to write precise transformers for each functor. In this case the computation of _strongest-postconditions_ or _weakest-preconditions_ avoids the complexity of generating a loop invariant and instead becomes a simple and deterministic case of formula pushing!

## <a name="0.9-Recursion"></a>0.9 Recursion

The lack of explicit looping constructs, and the presence of collection processing functors, is not unusual in functional languages. However, the result is often the replacement of complex loop structures with complex recursion structures. Complex raw flows obfuscate the intent of the code and hinder automated analysis and tooling regardless of if the flow is a loop or recursion.

Thus, Bosque is designed to encourage limited uses of recursion, increase the clarity of the recursive structure, and enable compilers/runtimes to avoid stack related errors. This is done by introducing the `rec` keyword which is used at both declaration sites to indicate a function/method is recursive and again at the call site so as to affirm that the caller is aware of the recursive nature of the call ([7 Invokable-Declarations](#7-Invokable-Declarations)).

## <a name="0.10-Determinacy"></a>0.10 Determinacy

When the behavior of a code block is under-specified the result is code that is harder to reason about and more prone to errors. As a key goal of the Bosque language is to eliminate sources of unneeded complexity that lead to confusion and errors we naturally want to eliminate these under-specified behaviors. Thus, Bosque does not have any _undefined_ behavior such as allowing uninitialized variable reads and eliminates all _under defined_ behavior as well including sorting stability and all associative collections (sets and maps) have a fixed and stable enumeration order.

As a result of these design choices there is always a single _unique_ and _canonical_ result for any Bosque program. This means that developers will never see intermittent production failures or flaky unit-tests!

## <a name="0.11-Equality-and-Representation"></a>0.11 Equality and Representation

Equality is a multifaceted concept in programming and ensuring consistent behavior across the many areas it can surface in a modern programming language such as `==`, `.equals`, `Set.has`, `List.sort`, is a source of subtle bugs.
This complexity further manifests itself in the need to consider the possible aliasing relations of values, in addition to their structural data, in order to understand the behavior of a block of code. The fact that _reference equality_ is chosen as a default, or is an option, is also a bit of an anachronism as reference equality heavily ties the execution to a hardware model in which objects are associated with a memory location.

In light of these issues the Bosque language does not allow user visible _reference equality_ in any operation including `==` or container operations. Instead equality is defined either by the core language for the primitives `Bool`, `Int`, `String`, `GUID`, etc., or as a user defined _composite key_ `ckey` type ([5.21 Equality Comparison](#5.21-Equality-Comparison)). The composite key type allows a developer to create a distinct type to represent a composite equality comparable value that provides the notion of equality e.g. identity, primary key, equivalence, etc. that makes sense for their domain. The language also allows types to define a key field that will be used for equality/order by the associative containers in the language ([3 Collections](#3-Collections)).

## <a name="0.12-Errors-and-Checks"></a>0.12 Errors and Checks

A central goal of the Bosque language is to simplify the process of building high reliability software. As part of this, the language provides first-class support for expressing a full range of invariants, sanity-checks, and diagnostic assertions.

```none
entity Foo {
    field x: Int;

    invariant x > 0; //check whenever a Foo is constructed

    method m(y: Int): Int
        requires y >= 0; //precondition
        ensures _return_ > 0; //postcondition
    {
        check this.x - y > 0;   //sanity check - enabled on optimized builds
        assert this.x * y != 0; //diagnostic assert - only for test/debug

        return x * y;
    }
}
```

## <a name="0.13-Atomic-Constructors-and-Factories"></a>0.13 Atomic Constructors and Factories

To reduce the amount of boilerplate code introduced by constructors, and in particular constructors that have long argument lists that are mainly passed through to super constructors, Bosque uses construction via direct field initialization to construct entity (object) values. For many uses, this simple direct initializer approach is sufficient and there is no need for complex constructors that compute derived values as part of the constructor execution.

However, it is sometimes useful to encapsulate initialization logic and, to accomplish this, we allow for the definition of `factory` functions which operate similar to constructors but, in some sense, are upside down. A factory function returns a record with all the fields needed for the enclosing entity/concept ([5.5 Entity Constructors](#5.5-Entity-Constructors)).

```none
concept Bar {
    field f: Int;

    factory default(): {f: Int} {
        return @{f=1};
    }
}

entity Baz provides Bar {
    field g: Int;
    field h: Bool = true;

    factory identity(i: Int): {f: Int, g: Int} {
        return @{f=i, g=i};
    }
}

var x = Baz@{f=1, g=2};
var y = Baz@{f=1, g=2, h=false};

var p = Baz@identity(1); //equivalent to Baz@{...Baz::identity(1)}
var q = Baz@{...Bar::default(), g=2};
```

In this code the two `Baz` entities are allocated via the atomic initialization constructor. In the first case the omitted `h` field is set to the provided default value of `true`. The `identity` factory defines `f` and `g` values for the entity via the returned record. When invoked with the constructor syntax
this is desugared to the atomic initializer with the result of factory.

With this design the need to pass data up through super calls is eliminated as the data can be directly inserted into the initializer or, if the super constructor has factory logic, then the super factory can be called and the result expanded directly into the atomic constructor as in `p = Baz@{...Bar::default(), g=2}`. The result of this inverted constructor logic is that _only_ the arguments needed for internal computation of initialization values must be propagated while all others can be directly set in the initializer. The elimination of the constructor boilerplate code and reduction in argument passing simplifies the definition of new nominal types as well as the impact of cascading changes when a field (or constructor argument) is added/removed in a base definition.

## <a name="0.14-Synthesis-Blocks"></a>0.14 Synthesis Blocks

**[NOT IMPLEMENTED YET]**

# <a name="1-Type-System"></a>1 Type System

The Bosque language supports a simple and non-opinionated type system that allows developers to use a range of structural, nominal, and combination types to best convey their intent and flexibly encode the relevant features of the problem domain.

_Notation_:
As part of describing the type system we use the following notation which is **not** part of the Bosque language:

```none
T1 <: T2 //Type T1 is a subtype of T2
T1 <! T2 //Type T1 is not a subtype of T2
T1 === T2 //Type T1 is equal to T2
```

## <a name="1.1-Nominal-Types"></a>1.1 Nominal Types

The nominal type system is a mostly standard _object-oriented_ design with parametric polymorphism provided by generics. All type names **must** start with a capital letter - `MyType` is a valid type name while `myType` is not.

Users can define abstract types ([TODO]()), `concept` declarations, which allow both abstract definitions and inheritable implementations for `const` members ([TODO]()), `static` functions ([TODO]()), `field` members ([TODO]()), and virtual `method` members ([TODO]()). Bosque `concept` types are fully abstract and can never be instantiated concretely. The `entity` types can provide concepts as well as override definitions in them and can be instantiated concretely but can never be further inherited from.

Developers can alias types or create special types ([TODO]()) using `typedef`, `enum`, and `ckey` constructs ([TODO]()).

The Bosque core library defines several unique concepts/entities. The `Any` type is a uber type which all others are a subtype of, the `None` and `Some` types are for distinguishing around the unique `none` value, and `Tuple`, `Record`, etc. exist to unify with the structural type system ([section 2](#2-Core-Types)). The language has primitives for `Bool`, `Int`, `String`, etc. as well as the expected set of parametric collection types such as `List[T]` `Map[K, V]` ([section 3](#2-Collections)).

Examples of nominal types include:

```none
MyType       //user declared concept or entity
Some         //core library declared concept
NSCore::Some //core library concept with explicit namespace scope
List[Int]    //core collection with generic parameter Int
```

### <a name="1.1.1-Type-Relation-on-Nominal-Types"></a>1.1.1 Type Relation on Nominal Types

The subtype relation on nominal types `T1` and `T2` is the standard parametric inheritance relation where `T1 <: T2` if any of the following are true:

1. `T1 === T2`
2. `T1` provides `T3` && `T3 <: T2` ([8 Concept and Entity Declarations](#8-Concept-and-Entity-Declarations))
3. `T1 === B1[G1]` && `T2 === B2[G2]` && `B1 === B2` && `G1 <: G2`

The first cases is if the two types are syntactically identical names. The second case covers the situation in which `T1` is declared to provide a concept that is, transitively, a subtype of `T2`. The final case is the standard parametric subtype relation on generic parameters. Some examples of these include:

```none
MyType <: MyType             //true - by case 1
Some <: Any                  //true - Some provides Any
Int <: Bool                  //false - no suitable `T3` for case 2
List[Int] <: List[Any]       //true - Int <: Any
List[Int] <: List[Bool]      //false - Int <! Bool
List[Int] <: Collection[Int] //true - List[T] provides Collection[T]
```

Note that the subtype relation is _covariant_ as all generic types are subtyped on the parameters. This is always safe as all data types in Bosque are immutable ([0.1 Immutable Values](#0.1-Immutable-Values)).

### <a name="1.1.2-Typed-Strings"></a>1.1.2 Typed Strings

Typed strings provide a novel mechanism for lifting known structure about the contents of a string into the type in a way that is meaningful to humans and that can be used by the type checker. If a type `Ty` is declared to `provide` the `Parsable` concept, which has the static method `tryParse(str: String): Ty | None` then it is possible to declare a string value type as `String[Ty]` which indicates that the call `Ty::tryParse` returns `Ty` (not `None`).

This ties the type of the string to the entity and then, by extension, into the larger type system. If we have the type relation `Ty <: Ty2` then the type checker will allow `String[Ty] <: String[Ty2]` and of course `String[Ty] <: String`.

This allows for code such as the following:

```none
function foo(zip: String[Zipcode], name: String) {...}

var zc: String[Zipcode] = ...;
var user: String = ...;

foo(user, zc) //Type error String not convertible to String[Zipcode]
foo(zc, user) //ok
```

## <a name="1.2-Structural-Types"></a>1.2 Structural Types

The structural type system includes Tuples and Records. These are self-describing, allow for optional entries with the `?` syntax, and can be specified as closed or open using the `...` syntax.

### <a name="1.2.1-Tuples"></a>1.2.1 Tuples

A tuple is a list of entries where each entry provides a type and can be marked as optional. Some examples include:

```none
[Int, Bool]   //Tuple of an Int and Bool
[Int, ?:Bool] //Tuple of an Int and optionally a Bool
[Int, ...]    //Tuple of an Int an possibly other entries
```

The subtype relation on tuples `T1` and `T2` is a lexicographic order on the tuple entries where a required entry is always less than an optional (`?`) entry and open tuples match any suffixes of a closed tuple.

```none
[Int] <: [Any]               //true - Int <: Any
[Int] <: [Bool]              //false - Int <! Bool
[Int] <: [Int, ?:Bool]       //true - omitting optional type is ok
[Int, Bool] <: [Int, ?:Bool] //true - optional type is ok
[Int, ?:Bool] <: [Int]       //false - missing optional type
[Int] <: [Int, ...]          //true - prefix matches
[Int, Bool] <: [Int, ...]    //true - prefix matches, open covers tail
[Int, ...] <: [Int]          //false - open is not subtype of closed
```

The tuple `[...]` is a supertype of all others and `[...]` is a subtype of the special nominal type `Tuple`.

### <a name="1.2.2-Records"></a>1.2.2 Records

A record is a map of identifier names to entries where each entry provides a type and can be marked as optional. Some examples include:

```none
{f: Int, g: Bool} //Record required f and g
{f: Int, g?: Bool} //Record required f optional g
{f: Int, ...} //Record required f open other
```

The subtype relation on tuples `R1` and `R2` is a subset based order on the record entries where a required entry is always less than an optional (`?`) entry and open tuples match any suffixes of a closed tuple.

```none
{f: Int} <: {f: Any}                    //true - Int <: Any
{f: Int} <: {g: Int}                    //false - different names
{f: Int} <: {f: Bool}                   //false - Int <! Bool
{f: Int} <: {f: Any, g?: Bool}          //true - omitting optional type is ok
{f: Int, g: Bool} <: {f: Int, g?: Bool} //true - optional type is ok
{f: Int, g?: Bool} <: {f: Int}          //false - missing optional type
{f: Int} <: {f: Int, ...}               //true - subset matches
{f: Int, g: Bool] <: {f: Int, ...}      //true - subset matches, open covers rest
{f: Int, ...} <: {f: Int}               //false - open is not subtype of closed
```

The record `{...}` is a supertype of all others and `{...}` is a subtype of the special nominal type `Record`.

## <a name="1.3-Function-Types"></a>1.3 Function Types

Functions are first class values and types in the Bosque language. Functions can use _named_ arguments for bindings arguments at calls and, thus, names are part of the function type signature. The special `_` parameter name indicates a "don't care" for a parameter name. Functions also allow for optional parameters, with the `?` syntax, and _rest_ parameters using the `...` syntax. The types of the rest parameters can be specified as any of the collection types from the core library including, lists, sets, and maps. Examples function types include:

```none
fn(x: Int) -> Int          //Function required parameter named "x"
fn(_: Int) -> Int          //Function required unnamed parameter
fn(x?: Int) -> Int         //Function optional x parameter
fn(...l: List[Int]) -> Int //Function rest List parameter
```

The subtype relation on function `F1` and `F2` starts with a lexicographic order on the parameter entries (with _contravariant_ subtyping) where an optional (`?`) entry is always less than a required entry and open tuples match any suffixes of a closed tuple. The relation is _covariant_ in the return type.

```none
fn(x: Any) -> Int <: fn(x: Int) -> Int  //true - Int <: Any
fn(x: Int) -> Int <: fn(x: Bool) -> Int //false - Bool <! Int
fn(x: Int) -> Int <: fn(x: Any) -> Int  //false - Any <! Int

fn(x: Any) -> Int <: fn(y: Int) -> Int //false - name mismatch
fn(x: Any) -> Int <: fn(_: Int) -> Int //true - name ignore
fn(_: Any) -> Int <: fn(x: Int) -> Int //false - name needed

fn(x: Int, y?: Bool) <: fn(x: Int) -> Int //true - omitting optional parameter is ok
fn(y?: Bool) <: fn(y: Bool) -> Int        //true - optional parameter is subtype
fn(x: Int) <: fn(x: Int, y?: Bool) -> Int //false - missing optional type

fn(x: Any) -> Int <: fn(x: Int) -> Any //true - Int <: Any
fn(x: Any) -> Any <: fn(x: Int) -> Int //true - Any <! Int

fn(...r: List[Int]) -> Int <: fn(...r: List[Int]) -> Int   //true - prefix match
fn(x: Any, ...r: List[Int]) -> Int <: fn(x: Int) -> Int    //true - prefix match
fn(_: Int) -> Int <: fn(..._: List[Int]) -> Int            //false - rest match
fn(...r: List[Int]) -> Int <: fn(_: Int) -> Int            //true - rest covers
```

## <a name="1.4-Combination-Types"></a>1.4 Combination Types

With the base structural and nominal types Bosque also supports _noneable_ (`T1?`), _union_ (`T1 | T2`), and limited _conjunction_ (`C1 + C2`) concept types.

Example combination types include:

```none
String | None
Int | Bool
String?
Parsable + Indexable
```

The `T1 | T2`notation specifies a type may be either `T1` _or_ `T2` while the notation `T1?` is shorthand for `T1 | None`. Note that this implies that `(T1?)?` is the same type as `T1?`. The type system also admits conjunction but limits it to conjunctions of `concept` types where `C1 + C2` indicates a type must provide both `C1` and `C2`.

```none
Int | Bool <: Any         //true
Int | Bool <: Int         //false
Int | Bool <: Int | Some  //true
Int | Int <: Int          //true - algebra
Some | None <: Any        //true
Any <: Some | None        //true - special case
Int? <: Int | None        //true
Int <: Int?               //true
Int?? <: Int?             //true - algebra
None? <: None             //true - algebra
C1 + C2 <: C2             //true
C1 + C1 <: C1             //true - algebra
C1 <: C1 + C2             //false - (unless C2 <: C1)
```

As shown in the above examples several combination types reduce to simpler version based on algebraic rules.

# <a name="2-Core-Types"></a>2 Core Types

**[TODO]**

# <a name="3-Collections"></a>3 Collections

**[TODO]**

# <a name="4-Type-Checking"></a>4 Type Checking

**[TODO]**

# <a name="5-Expressions"></a>5 Expressions

The Bosque language provides a rich set of expressions that support compact data manipulation and expression of intent. A major theme of these operators is to provide simple to reason about semantics that capture common operations with the goal of improving productivity and code quality.

## <a name="5.1-Arguments"></a>5.1 Arguments

Bosque provides _named arguments_ along with _rest_ and _spread_ operators. These can be used to perform simple and powerful data manipulation as part of invocations and constructor operations. Examples of these situations include:

```none
function nsum(d: Int, ...args: List[Int]): Int {
    return args.sum(default=d);
}

function np(p1: Int, p2: Int): {x: Int, y: Int} {
    return @{x=p1, y=p2};
}

//calls with explicit arguments
var x = nsum(0, 1, 2, 3); //returns 6

var a = np(1, 2);         //returns @{x=1, y=2}
var b = np(p2=2, 1);      //also returns @{x=1, y=2}
var c = np(p2=2, p1=1);   //also returns @{x=1, y=2}

//calls with spread arguments
var t = @[1, 2, 3];
var p = nsum(0, ...t);    //returns 6 -- same as explicit call

var r = @{p1=1, p2=2};
var q = np(...r);         //returns @{x=1, y=2} -- same as explicit call
```

The first of the examples show the use of rest and named arguments in call signatures. The call to `nsum` takes an arbitrary number of arguments which are automatically converted into a List. The calls to `np` show how named parameters can be used and mixed with positional parameters.

The next set of examples show how _spread_ arguments can be used. In the first case a tuple, `@[1, 2, 3]`, is created and assigned to the variable `t`. This tuple is then spread to provide the last three arguments to `nsum`. Semantically the call `nsum(0, ...t)` is the same as `nsum(0, t[0], t[1], t[2])` and, as a result, the value in `p` is the same as the value computed for `x`. The spread operator also works for records and named parameters. In the example the call to `np(...r)` is semantically the same as `np(p1=r.p1, p2=r.p2)`. Although not shown here spread can also be used on any collection, List, Set, Map, based data values as well.

## <a name="5.2-Constants"></a>5.2 Constants

Constant value expressions include `none`, `true`, `false` _Integer_, _String_,
_TypedString_, and _TypedStringLiteral_:

```none
none
true
0
5
-1
"ok"
""
'a*b*'#Regex //String[Regex]
'5'#Int      //String[Int]
'a*b*'@Regex //Regex literal for Regex@{str="a*b*"}
```

Most of these literal expressions are familiar from other languages but Bosque introduces the concept of _Typed Strings_ ([1.1.2 Typed Strings](#1.1.2-Typed-Strings)). The constant notation includes `"..."#Type` to introduce a literal typed string and `'...'@Type` to introduce a literal object that the string represents. Semantically the expression `'...'@Type` is equivalent to the expression `Type::tryParse("..."#Type)`.

## <a name="5.3-Variable-and-Scoped-Access"></a>5.3 Variable and Scoped Access

Simple name expressions can be used to refer to local, argument, and captured variables as well as to type or globally scoped constants. Examples include:

```none
x              //Local, Argument, or Captured Variable
NSFoo::g       //Namespace scoped global
Bar::c         //Type scoped constant
Bar[Int]::c    //Generic type scoped constant
(Bar + Baz)::c //Conjunction type scoped constant
```

Names in Bosque are resolved using the lexical scope where they are used, starting from the current block, up to arguments, captured variables, type and finally namespace scoping. Shadowing is not permitted on any variables. However, arguments/locals in a lambda body can be the same as names in the enclosing declaring body (preventing the closure capture [section 5.6 Lambda Constructors](#5.6-Lambda-Constructors)).

The ability to perform conjunction scoped constant resolution works by looking up the definition of the constant using both `Bar` and `Baz`. If the constant definition is the same for both then this is well defined (and legal) otherwise it is a type error.

## <a name="5.4-Tuple-and-Record-Constructors"></a>5.4 Tuple and Record Constructors

Tuple and records are constructed via a simple literal constructor syntax where the values for each tuple or record entry can be any other expression in the language.

```none
@[]               //Empty Tuple
@[ 1 ]            //Tuple of [Int]
@[ 1, "ok" ]      //Tuple of [Int, String]
@[ 1, foo() ]     //Tuple of 1 and result of foo
@{}               //Empty Record
@{ f=1 };         //Record of {f: Int}
@{ f=1, g=true }; //Record of {f: Int, g: Bool}
@{ g=x.h, f=1 };  //Record where f is 1 and g is result of x.h

```

## <a name="5.5-Entity-Constructors"></a>5.5 Entity Constructors

To reduce the amount of boilerplate code introduced by constructors, and in particular constructors that have long argument lists that are mainly passed through to super constructors, the Bosque language uses construction via direct field initialization to construct entity (object) values. For many uses this simple direct initializer approach is sufficient and there is no need for complex constructors that compute derived values as part of the constructor execution. Examples of this syntax include:

```none
concept Bar {
    field f: Int;
}

entity Baz provides Bar {
    field g: Int;
    field h: Bool = true;
}

var y = Baz@{f=1, g=2, h=false}; //Create a Baz entity with the given field values
var x = Baz@{f=1, g=2};          //Create a Baz entity with default value for h
```

In this code snippet two `Baz` entities are allocated via the atomic initialization constructor. In the second case the omitted `h` field is set to the provided default value of true.

Sometimes it is useful to encapsulate initialization logic and, to accomplish this, Bosque provides for the definition of `factory` functions which operate similar to constructors but, in some sense, are upside down. A factory function returns a record with all the fields needed for the enclosing entity/concept. So, the `identity` factory defines `f` and `g`. When invoked with the constructor syntax this is desugared to the atomic initializer being used with expanded record result of factory function, `Baz@{...Baz::identity(1)}`, in our example.

With this design the need to pass data up through super calls is eliminated as the data can be directly inserted into the initializer or, if the super constructor has factory logic, then the super factory can be called and the result expanded directly into the atomic constructor as in `Baz@{...Bar::default(), g=2}` below.

```none
concept Bar {
    field f: Int;

    factory default(): {f: Int} {
        return @{f=1};
    }
}

entity Baz provides Bar {
    field g: Int;
    field h: Bool = true;

    factory identity(i: Int): {f: Int, g: Int} {
        return @{f=i, g=i};
    }
}

var p = Baz@identity(1);              //Factory provides all arguments for constructor
var q = Baz@{...Bar::default(), g=2}; //Use super factory + specific values in direct constructor
```

The result of this inverted constructor logic is that _only_ the arguments needed for internal computation of initialization values must be propagated while all others can be directly set in the initializer. The elimination of the constructor boilerplate code and reduction in argument passing simplifies the definition of new nominal types as well as the impact of cascading changes when a field (or constructor argument) is added/removed in a base definition.

## <a name="5.6-Lambda-Constructors"></a>5.6 Lambda Constructors

Lambda constructors in the Bosque language combine a code definition for the lambda body with a variable _copy_ semantics for closure captured variables on lambda creation. The body definition can be either an expression or a statement block. In the case of ambiguity the body is preferentially parsed as a statement block.

```none
var f = fn(): Int => { return 1; }               //No arguments statement block body
var g = fn(): Int => 1;                          //No arguments statement expression body
var h = fn(x: Int): Int => x;                    //One required argument
var k = fn(x: Int, y?: Int): Int => @{a=x, b=y}; //One required and one optional argument

var c = 1;
var fc = fn(): Int => c; //Captured variable c
var rc = fc();           //Result is 1

var! m = 1;
var fm = fn(): Int => m; //Captured variable - always copied
m = 3;
var mc = fm();           //Result is still 1 since closure capture copies
```

In the above examples the type of the lambda expression is explicitly declared via the explicit type declarations for the arguments and return value. However, in the case where the lambda is a literal argument to a invocation taking a function typed parameter we allow these types to be inferred directly.

```none
function foo(f: fn(_: Int, _: Int) -> Int, a: [Int, Int]): Int {
    return f(...a);
}

var f = (x: Int, y: Int): Int => x + y; //Types required
var fr = foo(f, [1, 2]);

var ir = foo(fn(x, y) => x + y, [1, 2]); //Types inferred
```

## <a name="5.7-Scoped-Invokes"></a>5.7 Scoped Invokes

Scoped invocations in the Bosque language include calls to global functions and
static member functions. The arguments variations in [section 5.1 Arguments](#5.1-Arguments) can be used in any of these invocations.

```none
NSFoo::f(3)                 //Namespace scoped invocation
NSFoo::g[Int](0)            //Namespace scoped invocation with generic invoke
NSFoo::k[Int, String](1)    //Namespace scoped invocation with generic invoke

Bar::f()                    //Type scoped invocation
Baz[Int]::g[Int](0)         //Static invocation with generic type and invoke
Baz[Int]::k[Int, String](5) //Static invocation with generic type and invoke
(Baz + Bar)::m(0)           //Conjunction resolved static type invocation
```

Most of these forms are familiar from other object-oriented languages but the ability to perform static invocations using conjunction types is unique. As with scoped constant resolution this works by looking up the definition of the invoke using both `Bar` and `Baz`. If the constant definition is the same for both then this is well defined (and legal) otherwise it is a type error.

## <a name="5.8-Chaining-and-None-Chaining"></a>5.8 Chaining and None-Chaining

Handling `none` values (or null, undefined, etc. in other languages) is a relatively common task that can obscure the fundamental intent of a section of code with nests of cases and conditional handling for the special case.

The definition of Bosque provides support for short-circuiting `none` values on all chainable actions, using a `?` notion.

```none
@{}.h           //none
@{}.h.k         //error
@{}.h?.k        //none
@{h={}}.h?.k    //none
@{h={k=3}}.h?.k //3
```

When combined with a chainable operator (below) the `?` operator short-circuits evaluation and returns `none` whenever the expression value is `none`.

## <a name="5.9-Tuple-Typed-Access-Operators"></a>5.9 Tuple Typed Access Operators

The tuple typed chainable operators include:

- [e] to get the value at index i in the tuple or none if the index is not defined
- @[i, ..., j], create a new tuple using the values at indices i, ..., j

Examples of these include:

```none
var t = @[ 1, 2, 3 ];

t[0]         //1
t?[0]        //1
t[101]       //none
t@[1]        //@[2]
t@[2, 0]     //@[3, 1]
t@[5, 1]     //@[none, 2]
t[5][0]      //error
t[5]@[0]     //also error
t[5]?@[0, 1] //none
```

As in most languages the `[]` operator allows access to individual elements in a tuple while the bulk algebraic `@[]` operator provides compact and simple reshaping of a tuple data value.

## <a name="5.10-Record-Typed-Access-Operators"></a>5.10 Record Typed Access Operators

The record typed chainable operators include:

- .p to get the value associated with the property or none if the property is not defined
- @{f, ..., g}, create a new record using the values at properties f, ..., g

Examples of these include:

```none
var r = @{ f=1, g=2, k=true };

r.f         //1
r?.f        //1
r.h         //none
r@{g}       //@{g=2}
r@{g, k}    //@{g=2, k=true}
r@{h, g}    //@{h=none, g=2}
r.h.f       //error
r.h@{f}     //also error
r.h?@{f, g} //none
```

As in most languages the `.` operator allows access to individual elements in a record while the bulk algebraic `@{}` operator provides compact and simple reshaping of a record data value.

## <a name="5.11-Nominal-Typed-Access-Operators"></a>5.11 Nominal Typed Access Operators

Fields in nominal types can be chain accessed in a similar manner as properties in records:

- .f to get the value associated with the field or error if the field is not defined on the type
- @{f, ..., g}, create a new _record_ using the values at fields f, ..., g

Examples of these include:

```none
entity Baz {
    field f: Int;
    field g: Int;
    field k: Bool
}

var e = Baz@{ f=1, g=2, k=true };

e.f         //1
e?.f        //1
e.h         //none
e@{g}       //@{g=2}
e@{g, k}    //@{g=2, k=true}
e@{h, g}    //@{h=none, g=2}
e.h.f       //error
e.h@{f}     //also error
e.h?@{f, g} //none
```

As in most languages the `.` operator allows access to individual elements in a entity (object) while the bulk algebraic `@{}` operator provides compact and simple reshaping of a data value. Note that the result type is a _record_.

## <a name="5.12-Typed-Projection"></a>5.12 Typed Projection

In addition to extracting new tuples/records using the `@[]` and `@{}` notation the Bosque language also supports projecting out structured data using types via the notation _Exp_`#`_Type_. This chain operator can be used on tuples, records, and nominal types:

```none
concept Bar {
    field f: Int;
}

concept T3 {
    field f: Int;
}

entity Baz provides Bar {
    field g: Int;
    field k: Bool
}

var t = @[ 1, 2, 3 ];
t#[Int];        //@[1]
t#[Bool];       //error type mismatch
t#[Int, ?:Int]; //@[1, 2]
t#[Int, Any];   //@[1, 2]

var r = @{ f=1, g=2, k=true };
r#{f: Int};          //@{f=1}
r#{f: Bool};         //error type mismatch
t#[f: Int, g?: Int]; //@{f=1, g=2}
t#[f: Int, g: Any];  //@{f=1, g=2}

var e = Baz@{ f=1, g=2, k=true };
e#Bar;       //@{f=1}
e#{f: Bool}; //error type projection requires same kinds
e#T3;         //error type mismatch
```

Note that the result type of projecting from a nominal type is a _record_.

## <a name="5.13-Difference"></a>5.13 Difference

**[Not Implemented Yet]** delete indecies `\[i, ..., j]`, properties `\{f, ..., g}`, or types `\#`_Type_.

## <a name="5.14-Update"></a>5.14 Update

In most languages updating (or creating an updated copy) is done on a field-by-field basis. However, with the bulk updates in Bosque it is possible to perform the update as an atomic operation and without manually extracting and copying fields. Bosque provides a chainable update operations for tuples (_Exp_`<~(i=e1, ... j=ek)` notation), records, and nominal types (_Exp_`<~(f=e1, ... f=ek)`).

```none
entity Baz {
    field f: Int;
    field g: Int;
    field k: Bool
}

var t = @[ 1, 2, 3 ];
t<~(1=5);      //@[1, 5, 2]
t<~(0=3, 1=5); //@[3, 5, 3]
t<~(1=5, 4=0); //@[1, 5, 3, none, 0]

var r = @{ f=1, g=2, k=true };
r<~(g=5);          //@{f=1, g=5, k=true}
r<~(g=3, k=false); //@{f=1, g=3, k=false}
r<~(g=5, h=0);     //@{f=1, g=5, k=true, h=0}

var e = Baz@{ f=1, g=2, k=true };
e<~(g=5);          //Baz@{f=1, g=5, k=true}
e<~(g=3, k=false); //Baz@{f=1, g=3, k=false}
e<~(g=5, h=0);     //error invalid field name
```

Note that for tuples updating past the end of the tuple will `none` pad the needed locations while for records it will insert the specified property. Updating a non-existent field on a nominal type is an error.

## <a name="5.15-Merge"></a>5.15 Merge

The update operations allow bulk algebraic copy-modification of values but require the literal properties/indecies/fields to be specified. To allow more programmatic operation the Bosque language also provides chainable merge operations which take pairs of tuple/tuple, record/record, or nominal/record and merge the data values using the syntax _Exp_`<+(`_Exp_`)`. The tuple/tuple operation maps to append, record/record is dictionary merge, and nominal/record is bulk update fields.

```none
entity Baz {
    field f: Int;
    field g: Int;
    field k: Bool
}

var t = @[ 1, 2, 3 ];
t<+(@[5]);       //@[1, 2, 3, 5]
t<+(@[3, 5]);    //@[1, 2, 3, 3, 5]

var r = @{ f=1, g=2, k=true };
r<+(@{g=5});          //@{f=1, g=5, k=true}
r<+(@{g=3, k=false}); //@{f=1, g=3, k=false}
r<+(@{g=5, h=0);      //@{f=1, g=5, k=true, h=0}

var e = Baz@{ f=1, g=2, k=true };
e<+(@{g=5});          //@{f=1, g=5, k=true}
e<+(@{g=3, k=false}); //@{f=1, g=3, k=false}
e<+(@{g=5, h=0);      //error field not defined
```

The ability to programmatically merge into values allows us to write concise data processing code and eliminate redundant code copying around individual values. In addition to helping prevent subtle bugs during initial coding the operators can also simplify the process of updating data representations when refactoring code by reducing the number of places where _explicit_ value deconstruction, update, and copies need to be used.

## <a name="5.16-Lambda-Apply"></a>5.16 Lambda Apply

The lambda application operator is used to invoke the method body of a lambda value with the provided arguments. As with the other chainable operators it supports none-chaining.

```none
var f = (x: Int, y: Int): Int => x + y; //Types required
var fn = none;

f(5, 3);  //8 - normal invoke
f?(5, 3); //8 - none-chain invoke
fn();     //error
fn?();    //none
```

## <a name="5.17-Invoke"></a>5.17 Invoke

The chainable invoke operator `->` can be used to invoke both member methods from nominal types and lambda values stored in properties or fields.

For member method invocation the invoke operator will handle any virtual method resolution, either from the dynamic object type or from the specified base overload when using the `->::`_Type_ syntax.

```none
concept Fizz {
    field v: Int;

    method m1(x: Int): Int {
        return this.v + x;
    }

    virtual method m3(x: Int): Int {
        return this.v + x + 3;
    }
}

entity Bar provides Fizz {
    field func: fn(this: Bar, x: Int) -> Int = fn(this: Bar, x: Int): Int => this.v + x;

    override method m3(x: Int): Int {
        return 0;
    }
}

entity Biz provides Fizz {
    method mc[T](arg: T): T? {
        return this.v != 0 ? arg : none;
    }
}

var bar = Bar@{v=10};
var biz = Biz@{v=3};

bar->m1(5); //15
biz->m1(5); //8

bar->m3(5);      //0
bar->Fiz::m3(5); //18
biz->m3(5);      //11

bar->func(2); //12
biz->func(2); //error no such field or method

bar->mc[Int](3); //error no such field or method
biz->mc[Int](3); //3

(none)->m1(5);    //error no such field or method
(none)?->m1(5);   //none

none->isNone(); //true - see core None and Any types
@{}->isSome();  //true - see core None and Any types
5->isSome();    //true - see core None and Any types
```

The Bosque type system provides a unified model for all structural, primitive, and nominal types. So, methods can be invoked on any value. See the [core types](#2-Core-Types) section for more info on what invocations are supported.

## <a name="5.18-Pipeline"></a>5.18 Pipeline

Higher-order processing of collections is a fundamental aspect of the Bosque language ([section](TODO)) but often times chaining filter/map/etc. is not a natural way to think about a particular set of operations and can result in the creation of substantial memory allocation for intermediate collection objects.
Thus, Bosque allows the use of both method chaining for calls on collections _and_ pipelining, `|>`, values through multiple steps. This allows a developer to specify a sequence of operations, each of which is applied to elements from a base collection sequence, that transform the input data into a final collection. As with other chaining we support none-coalescing operations, `|?>`, which propagates a none immediately to the output in the pipeline and, `|??>`, which short circuits the processing and drops the value. Some representative examples are shown below:

```none
var v: List[Int?] = List@{1, 2, none, 4};

//Chained - List@{1, 4, 16}
v->filter(fn(x) => x != none)->map[Int](fn(x) => x*x);

//Piped none filter - List@{1, 4, 16}
v |> filter(fn(x) => x != none) |> map[Int](fn(x) => x*x);

//Piped with noneable filter - List@{1, 4, 16}
v |??> map[Int](fn(x) => x*x);

//Piped with none to result - List@{1, 4, none, 16}
v |?> map[Int](fn(x) => x*x);
```

## <a name="5.19-Unary-Operators"></a>5.19 Unary Operators

Bosque supports the three unary prefix operators:

- `!` will negate a `Bool` value _and_ converts the value `none` into `true`
- `+` is a nop but is often useful for indicating intent
- `-` negates an integer value

Examples include:

```none
!true   //false
!false  //true
!none   //true
!"true" //error
!0      //error

+5 //5
-5 //-5
```

## <a name="5.20-Binary-Operators"></a>5.20 Binary Operators

Bosque supports a range of binary operators which can be applied to `Int` values including `+`, `-`, `*`, `/`, and `%`. Examples include:

```none
5 + 6 //11
3 - 1 //2
2 * 3 //6
3 / 2 //1
4 / 2 //2
4 / 0 //error
3 % 2 //1
4 % 2 //0
4 % 0 //error
```

## <a name="5.21-Equality-Comparison"></a>5.21 Equality Comparison

The Bosque language provides `==` and `!=` operators which work for values of the following types:

- `None` where `none` may be compared with values of any other type
- `Bool`
- `Int`
- `String` where typed strings are implicitly coerced to their untyped version
- `GUID`
- `Enum` where they types and values must be the same
- `CustomKey` where they types and values must be the same

Examples of the equality operators on primitive values include:

```none
1 == 1                     //true
"1" == ""                  //false
"1" != ""                  //true
'hello'#Foo == 'hello'#Foo //true
'hello'#Foo == "hello"     //true
@{} == none                //false
false == none              //false
```

Bosque _does not_ admit _reference equality_ in any form. A program can either use explicit comparison on a primitive type _or_ a developer can define a custom key that provides the notion of equality e.g. identity, primary key, equivalence, etc. that makes sense for their domain.

Custom keys are compared using the type of the key and the pairwise equality of each field defined in the key.

```none
ckey MyKey {
    field idx: Int;
    field category: String;
}

ckey OtherKey {
    field idx: Int;
    field category: String;
}

var a = MyKey@{1, "yes"};
var b = MyKey@{1, "yes"};
var c = MyKey@{1, "no"};

var q = OtherKey@{1, "yes"};

a == a //true
a == b //true
a == c //false - different field values (category)

a == q //false - different key types
```

Collections and operations on them are also defined to use this definition of equality and custom key valued fields ([section 3 Collections](#3-Collections)) instead of overloaded equals or compare methods.

## <a name="5.22-Order-Comparison"></a>5.22 Order Comparison

Bosque supports a range of order operators, `<`, `>`, `<=`, and `>=` which can be applied to `Int` or `String` values. For typed strings, `String[T]` the compare operator ignores the generic type and is based on the order of the underlying raw string e.g. both arguments are coerced to `String`.

```none
1 < 2                      //true
"1" < ""                   //false
"11" < "12"                //true
'hello'#Foo <= 'hello'#Foo //true
'hello'#Foo <= "hello"     //true
'hello'#Foo < "h"          //false
```

## <a name="5.23-Logic-Operators"></a>5.23 Logic Operators

Bosque provides the standard short-circuiting `&&` and `||` operators as well as a implies `==>` operator. These operators all work on `Bool` typed values and will implicitly convert `none` into false. Examples include:

```none
true || (1 / 0 == 0)  //true
false || (1 / 0 == 0) //error
none || false         //false
1 || true             //error

false && (1 / 0 == 0) //false
true && (1 / 0 == 0)  //error
none && true          //false
1 && true             //error

false ==> true        //true
false ==> false       //true
true ==> true         //true
true ==> false        //false

false ==> (1 / 0 == 0) //true
true ==> (1 / 0 == 0)  //error
true ==> none          //false
1 ==> true             //error
```

## <a name="5.24-None-Coalescing"></a>5.24 None Coalescing

Bosque provides specific none-coalescing operations, `?|` and `?&`, as opposed to truthy based coalescing that overloads the logical and/or operators.

```none
function default(x?: Int, y?: Int) : Int {
    return (x ?| 0) + (y ?| 0); //default on none
}
default(1, 1); //2
default(1);    //1
default();     //0

function check(x?: Int, y?: Int) : Int? {
    return x ?& y ?& x + y; //check none
}
default(1, 1); //2
default(1);    //none
default();     //none
```

The `?|` operator short-circuits on non-none values while the `?&` operator short-circuits on none values.

## <a name="5.25-Select"></a>5.25 Select

The select operator uses a condition which may return a `Bool` or `None` and uses this to select between to lazily evaluated alternative expressions. The `none` value is automatically coerced to `false`.

```none
true ? 1 : 2      //1
false ? 1 : 2      //2
true ? 1 : 2 / 0  //1
false ? 1 : 2 / 0 //error
none ? 1 : 2      //2
"" ? 1 : 2        //error
```

## <a name="5.26-Statement-Expressions"></a>5.26 Statement Expressions

Bosque includes _Match_, _If_, and _Block_ statements ([section 6 Statements](#6-Statements)) which can be used as both expressions and statements. It also allows these to be used in expression positions where the action blocks in If/Match are treated as expressions and, instead of `return`, a block will `yield` a result:

```none
var a = if(true) 3 else 4;    //3
var b = {var x = 3; yield x;} //3
var c = match("yes") {
    case "yes" => 5
    case "no" => {var x = 5; yield x - 3;}
    case _ => if(true) 11 else 17
} //5
```

Note that the introduction of an expression block creates a new lexical scope for any variables declared inside. Thus, these will not pollute the enclosing namespace.

The _If_ statement conditions allow `Bool` and `None` types.

The _Match_ statements support destructuring and type operations in the match just as described in [section 6.6 Match](#6.8-Match).

When block statements are used as expressions they cannot use `return` statements inside.

## <a name="5.27-Thunk-Blocks"></a>5.27 Thunk Blocks

**[Not Implemented Yet]**

## <a name="5.28-Synthesis-Blocks"></a>5.28 Synthesis Blocks

**[Not Implemented Yet]**

# <a name="6-Statements"></a>6 Statements

Given the rich set of expression primitives in Bosque there is a reduced need for a large set of statement combinators. The language includes the expected _Match_ and _If_ which can be used as both expressions and statements as well as _structured assignment_ for easy destructuring of return values. As high reliability software is a key goal, Bosque provides an `assert`, enabled only for debug builds, and a `check`, enabled on all builds, statements as first class features in the language (in addition to pre/post conditions and class invariants). We also note that there are **no looping constructs** in the language.

Local variables with block structured code is an appealing model for programming. The statements provided in the Bosque language seek to fuse functional programming with block scopes and `{...}` braces by allowing multiple assignments to a variable and scoped blocks.

## <a name="6.1-Empty"></a>6.1 Empty

The empty statement is simply the `;` which has no effect but is a legal statement.

## <a name="6.2-Variable-Declaration"></a>6.2 Variable Declaration

Variable declarations in Bosque can be declared as constant in the scope using the `var` declaration form:

Examples of these declarations are:

- `var` _Identifier_ `=` _Exp_`;`
- `var` _Identifier_`:`_Type_ `=` _Exp_`;`

If the type is omitted in the declaration it is inferred from the type of the expression used to initialize the variable.

```none
var x: Int = 3; //Int variable introduced and initialized
var y = 3;      //variable introduced and inferred to be of type Int
```

Alternatively variables can be declared as updatable in the scope using the `var!` declaration form. In the `var!` form an initializer expression can be used to set the initial value for the variable or it can be omitted to leave the variable uninitialized.

- `var!` _Identifier_`:` _Type_`;`
- `var!` _Identifier_ `=` _Exp_`;`
- `var!` _Identifier_`:`_Type_ `=` _Exp_`;`

Using the `var!` form allows for later assignment statements ([6.3 Variable Assignment](#6.3-Variable-Assignment)) to update the value of the variable. It is an error to use an uninitialized variable unless all possible paths flowing to the use _must_ have assigned it a value.

Examples of these declarations are:

```none
var! x: Int;     //uninitialized mutable variable of type Int introduced
var! x: Int = 3; //mutable variable of type Int introduced
var! x = 3;      //mutable variable of inferred type Int introduced
```

## <a name="6.3-Variable-Assignment"></a>6.3 Variable Assignment

Variables declared as mutable, using the `var!` syntax, can be modified by later assignment statements.

```none
var! x: Int;
var! y = 7;

var a = x; //error undefined use

x = 3;
y = x;     //ok x is defined now

var z = 5;
z = y;     //error z is not updatable

```

Updates can occur in different blocks of code as well:

```none
var! x = 0;
if(true) {
    x = 1;
}

var! y: Int;
if(true) {
    y = 1;
}
else {
    y = 2;
}
```

## <a name="6.4-Structured-Declaration-and-Assignment"></a>6.4 Structured Declaration and Assignment

**[Not Implemented Yet]**

## <a name="6.5-Return-and-Yield"></a>6.5 Return and Yield

Within a block of code the `return` statement exits the current invocation with the value of the expression as the result. The `yield` statement is used in an expression block ([5.26 Statement Expressions](#5.26-Statement-Expressions)) to exit the block with the value of the expression as the result.

```none
function abs(x: Int): Int {
    if(x < 0) {
        return -x;
    }
    else {
        return x;
    }
}

function absy(x?: Int): Int {
    if(x == none) {
        return 0;
    }

    return {
        var! y = x;
        if(y < 0) {
            y = -y;
        }
        yield y;
    }
}
```

Error code return checking and handling can frequently obscure the core flow of a function and result in subtle errors. To simplify the logic or return values with error codes the Bosque language provides a return with, _Exp_ `with` (`return` | `yield`) (`when` _Cond_)? (`of` _Op_), syntax.

**[Not Implemented Yet]**

## <a name="6.6-Validation"></a>6.6 Validation

For statement level validation statement the Bosque language provides the `assert` and `check` statements. The `assert` is only enabled in debug builds while `check` is enabled in all builds. If the condition provided evaluates to false both statements will raise an error.

```none
assert false; //raise error in debug
assert true;  //no effect

check false;  //raise error always
check true;   //no effect
```

The error semantics in Bosque are unique. In most languages errors are distinguishable as runtime error reporting requires the inclusion of observable information, like line numbers and error messages, to support failure analysis and debugging. However, Since Bosque execution is fully deterministic ([0.10 Determinacy](#0.10-Determinacy)) and repeatable, the language has two execution semantics: _deployed_ and _debug_. In the deployed semantics _all runtime errors_ are indistinguishable while in the debug semantics errors contain full line number, call-stack, and error metadata. When an error occurs in _deployed_ mode the runtime simply aborts, resets, and re-runs the execution in _debug_ mode to compute the precise error!

## <a name="6.7-If-Then-Else"></a>6.7 If-Then-Else

The conditional if statements in Bosque are classical conditional control flow structures.

```none
var x = 3;

//if with fall through
if(x == none) {
    return none;
}

//simple if-else
if(x < 0) {
    return -x;
}
else {
    return x;
}

//if-elif*-else form
if(x < 0) {
    return -x;
}
elif(x > 0) {
    return x;
}
else {
    return 0;
}
```

Note that dangling `elifs` must have a final `else` block.

To avoid ambiguity when _If_ statements/expressions are used the actions cannot nest naked _If_/_Match_ expressions. Instead they must be enclosed in an expression statement block.

## <a name="6.8-Match"></a>6.8 Match

**[Not Implemented Yet]**

## <a name="6.9-Block"></a>6.9 Block

Block statements in Bosque are sequences of statements. The block introduces a new lexical scope for any variables declared inside.

```none
var x = 3;
{
    var y = 5;

    var z: Int;
    if(x != 3) {
        z = 0;
    }
    else {
        z = 1;
    }
}

check z == 0; //error z is out of scope
check x > 0;  //ok x is in scope
```

# <a name="7-Invokable-Declarations"></a>7 Invokable Declarations

**[TODO]**

[TODO] discuss `ref` parameters threading

[TODO] discuss `rec` call management

# <a name="8-Concept-and-Entity-Declarations"></a>8 Concept and Entity Declarations

**[TODO]**

# <a name="9-Namespace-Declarations"></a>9 Namespace Declarations

**[TODO]**
