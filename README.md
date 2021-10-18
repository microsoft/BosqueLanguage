# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/Microsoft/BosqueLanguage/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Health](https://img.shields.io/github/workflow/status/microsoft/BosqueLanguage/nodeci)](https://github.com/microsoft/BosqueLanguage/actions) 


## The Bosque Project
The Bosque Programming Language project is a ground up language & tooling co-design effort focused on is investigating the theoretical and the practical implications of:

1. Explicitly designing a code intermediate representation language (bytecode) that enables deep automated code reasoning and the deployment of next-generation development tools, compilers, and runtime systems.
2. Leveraging the power of the intermediate representation to provide a programming language that is both easily accessible to modern developers and that provides a rich set of useful language features for developing high reliability & high performance applications.
3. Taking a cloud-development first perspective on programming to address emerging challenges as we move into a distributed cloud development model based around microservices, serverless, and RESTful architectures.

### The Role of Intermediate Representations

Compiler intermediate representations (IRs) are traditionally thought of, and designed with, a specific source language (or languages) in mind. Their historical use has mainly been an intermediate step in lowering a source language program, with all of the associated syntactic sugar, into a final executable binary. Over time they have become increasingly important in supporting program analysis and IDE tooling tasks. 
In the Bosque project we ask what happens if the IR is designed explicitly to support the rich needs of automated code reasoning, IDE tooling, etc. With this novel IR first perspective we are exploring a new way to think about and build a language intermediate representation and tools that utilize it.

### Regularized Programming

Many features that make the Bosque IR amenable for automated reasoning involve simplifying and removing sources of irregularity in the semantics. These regularizations also simplify the task of understanding and writing code for the human developer. Inspired by this idea the Bosque project is building a new regularized programming language that takes advantage of the features of the IR.

The result is a language that simultaneously supports the kind of high productivity development experience available to modern developers while also providing a resource efficient and predictable runtime, scaling from small IoT up to heavily loaded cloud services. In addition to bringing the expressive power expected from a modern language, the Bosque language also introduces several novel features like Typed Strings and API Types, that directly address challenges faced by developers working in a distributed cloud based world.

### Cloud First Development
The move into cloud based development, with architectures based around microservices, serverless functions, and RESTful APIs, brings new challenges for development. In this environment an program may interoperate with many other (remote) services which are maintained by different teams (and maybe implemented in different languages). This forces APIs to use least-common denominator types for interop and creates the need for extensive serialize/deserialize/validate logic. Further, issues like cold-service startups, 95% response times, resiliency and diagnostics, all become critical but have not been design considerations in most traditional languages.

The Bosque project takes a cloud and IoT first view of programming languages. It includes features like API Types to simplify the construction and deployment of REST style APIs. Application initialization design provides 0-cost loading for lighting fast (cold) startup. Choices like fully determinized language semantics, keys and ordering, and memory behavior result in a runtime with minimal performance variability and enable ultra-low overhead tracing.

## News
**September 2021:** Upcoming talk at Linux Foundation Open Source Summit in collaboration with folks from Morgan Stanley! [Agile and Dependable Service Development with Bosque and Morphir](https://events.linuxfoundation.org/open-source-summit-north-america/program/schedule/). 

**June 2021**
Pushing version 0.8.0 as new master -- this update obsoletes the previous prototype version and lays the ground work for an eventual stable release. Major rework was done in the language, type-checker, validator implementation, and runtime. More details will be posted soon but the headline is exciting improvements in all areas.

However, this also means many many things are broken. Fixes and tests are coming online continuously and I will be opening a number of issues that are suitable for community contributions. Looking forward to seeing Bosque move from an exciting concept and toward a practical language!

## Documentation

Small samples of code and unique Bosque tooling are below in the [Code Snippets](#Code-Snippets) and [Tooling](#Tooling) sections. A rundown of notable and/or unique features in the Bosque language is provided in the [language overview section 0](docs/language/overview.md#0-Highlight-Features).

Detailed Documentation, Tutorials, and Technical Information:
* [Language Docs](docs/language/overview.md)
* [Library Docs](docs/libraries/overview.md)
* Tutorials - _Coming Eventually!_
* [Technical Papers](docs/papers/publist.md)
* [Contribution guidelines](CONTRIBUTING.md)

## Code Snippets

**Add 2 numbers:**

```none
function add2(x: Nat, y: Nat): Nat {
    return x + y;
}

add2(2, 3)     //5
add2(x=2, y=3) //5
add2(y=2, 5)   //7
```

**All positive check using rest parameters and lambda:**

```none
function allPositive(...args: List<Int>): Bool {
    return args.allOf(fn(x) => x >= 0i);
}

allPositive(1, 3, 4) //true
```

**Tuples and Records:**

```none
function doit(tup: [Int, Bool], rec: {f: String, g: Int}): Int {
    return tup.0 + rec.g;
}

doit([1, false], {f="ok", g=3}) //4
```

**Sign (with default argument):**

```none
function sign(x?: Int=0): Int {
    var y: Int;

    if(x == 0) {
        y = 0;
    }
    else {
        y = (x > 0) ? 1 : -1;
    }

    return y;
}

sign(5)    //1
sign(-5)   //-1
sign()     //0
```

**Nominal Types Data Invariants:**

```
concept WithName {
    invariant $name != "";

    field name: String;
}

concept Greeting {
    abstract method sayHello(): String;

    virtual method sayGoodbye(): String {
        return "goodbye";
    }
}

entity GenericGreeting provides Greeting {
    const instance: GenericGreeting = GenericGreeting@{};

    override method sayHello(): String {
        return "hello world";
    }
}

entity NamedGreeting provides WithName, Greeting {
    override method sayHello(): String {
        return String::concat("hello ", this.name);
    }
}

GenericGreeting@{}.sayHello()         //"hello world"
GenericGreeting::instance.sayHello()  //"hello world"

NamedGreeting@{}.sayHello()           //type error no value provided for "name" field
NamedGreeting@{name=""}.sayHello()    //invariant error
NamedGreeting@{name="bob"}.sayHello() //"hello bob"
```

**(Algebraic Data Types)++ and Union Types**
```
typedecl BoolOp provides APIType using {
    line: Nat
} of
LConst { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
& {
    recursive method evaluate(): Bool {
        match(this) {
            LConst                  => return this.val;
            | NotOp                 => return !this.arg.evaluate[recursive]();
            | AndOp@{_, larg, rarg} => return larg.evaluate[recursive]() && rarg.evaluate[recursive]();
            | OrOp@{_, larg, rarg}  => return larg.evaluate[recursive]() || rarg.evaluate[recursive]();
        }
    } 
}

AndOp@{2, LConst@{1, true}, LConst@{1, false}}.evaluate[recursive]() //false
OrOp@{2, LConst@{1, true}, LConst@{1, false}}.evaluate[recursive]()  //true

function printType(x: Bool | Int | String | None ): String {
    return match(x) {|
        Bool     => "b"
        | Int    => "i"
        | String => "s"
        _        => "n"
    |};
}

printType(1.0f) //type error
printType(true) //"b"
printType(none) //"n"

```

**Pre/Post Conditions and Invariants**

[MAY BE OUT OF DATE]
```
entity Animal {
    invariant $says != "";

    field says: String;
}

function createAnimal(catchPhrase: String): Animal
{
    return Animal@{says=catchPhrase};
}

function createAnimalPre(catchPhrase: String): Animal
    requires catchPhrase != "";
{
    return Animal@{says=catchPhrase};
}

function createAnimalPreSafe(catchPhrase: String): Animal
    requires release catchPhrase != "";
{
    return Animal@{says=catchPhrase};
}

typedef ErrData = {msg: String, data?: Any};

entrypoint function getSays(animal: String, catchPhrase: String): Result<String, ErrData?>
    validate animal != "" or return err({ msg="Invalid animal" });
    validate catchPhrase != "" or return err({ msg="Invalid catchPhrase" });
{
    return String::concat("The ", animal, " says ", createAnimal::(catchPhrase).says);
}

createAnimal("woof woof") //ok always
createAnimal("")          //fails invariant in debug
createAnimalPre("")       //fails precondition in debug *but not* release
createAnimalPreSafe("")   //fails precondition in all build flavors

getSays("dog", "woof") //Ok<String, ErrData>@{value="The dog says woof"}
getSays("", "woof") //Err<String, ErrData>@{error={ msg="Invalid animal" }}
getSays("dog", "") //Err<String, ErrData>@{error={ msg="Invalid catchPhrase" }}
```

**Validated and Typed Strings:**
```
typedecl ZipcodeUS = /[0-9]{5}(-[0-9]{4})?/;
typedecl CSSpt = /[0-9]+pt/;

function is3pt(s1: StringOf<CSSpt>): Bool {
    return s1.value() === "3pt";
}

ZipcodeUS::accepts("98052-0000") //true
ZipcodeUS::accepts("1234")       //false

is3pt("12")              //type error not a StringOf<CSSpt>
is3pt('98052'#ZipcodeUS) //type error not a StringOf<CSSpt>

is3pt('3pt'#CSSpt) //true
is3pt('4pt'#CSSpt) //false
```

```
entity StatusCode provides Parsable {
    field code: Int;
    field name: String;

    function parse(name: String): Result<StatusCode, String> {
        return switch(name) {|
            "IO"        => ok(StatusCode@{1, name})
            | "Network" => ok(StatusCode@{2, name})
            | _         => err("Unknown code")
        |};
    }

    function accepts(name: String): Bool {
        return name === "IO" || name === "Network";
    }
}

function isIOCode(s: DataString<StatusCode>): Bool {
    return s === 'IO'#StatusCode;
}

isIOCode("IO");               //type error not a DataString<StatusCode>
isIOCode('Input'#StatusCode)  //type error not a valid StatusCode string
StatusCode::parse("Input") //runtime error not a valid StatusCode string

isIOCode('Network'#StatusCode)               //false
isIOCode('IO'#StatusCode)                    //true

let ec: StatusCode = 'IO'(StatusCode);
assert(ec.code == 1i); //true
```

**Numeric Types**

## API Types

[TODO]

## Application Validation

A unique feature of the Bosque systems is the `bsqcheck` tool. This tool combines verification and bug triggering input generation tools in a unique configuration. For each possible failure in the program it first attempts to prove that a given failure is impossible under all inputs or generate a debuggable input that will trigger the error. If it cannot do either of these, which can happen due to the computational cost of theorem proving, then it will try to prove that, under a variety of simplifying assumptions, that the error cannot occur. 

Thus, the tool will output one of the following results for each possible program failure:
- (1a) Proof that the error is infeasible in all possible executions
- (1b) Feasibility witness input that reaches target error state
- (2a) Proof that the error is infeasible on a simplified set of executions
- (2b) No witness input found before search time exhausted


The **symtest** tool implements the symbolic testing algorithm and works as follows. Given the application shown below:
```
namespace NSMain;

enum CalcOp {
    negate,
    add,
    sub
}

function main(op: CalcOp, arg1: BigInt, arg2: BigInt?): BigInt 
    //requires op !== CalcOp::negate ==> arg2 !== none;
{
    switch (op) {
        CalcOp::negate => return -arg1;
        | CalcOp::add => return arg1 + arg2.as<BigInt>();
        | CalcOp::sub => return arg1 - arg2.as<BigInt>();
    }
}
```

Assuming this code is in a file called `calc.bsq` then we can run the following command to check for errors:
```
> node bin/runtimes/bsqcheck.js --check calc.bsq
```
Which will report that errors are possible and generate a set of inputs that will trigger each error. In this case both the `CalcOp::add` and `CalcOp::sub` cases may fail on the type cast if the `arg2` argument is `none`. The output for the add case is:
```
[
    "NSMain::CalcOp::add",
    0,
    null
]
```

However, if we uncomment the requires clause, which asserts that the `arg2` parameter is only `none` if the op is `CalcOp::negate`, when we run the `bsqcheck` tool it will be able to successfully _prove_ that no runtime errors can ever occur.

More details on this checking systems can be found in our [technical report](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/BosqueIR.pdf).

Note: we recommend specifying preconditions as always checked, `requires release`, on entrypoint functions to ensure that these externally exposed API endpdoints are not misused.

## Execution

**Interpreter:** 

An interpreter is under-development. See the [icpp](https://github.com/microsoft/BosqueLanguage/tree/master/impl/src/tooling/icpp) sources in the `impl` repository.

**Evaluation with Solver:**

In addition to using symbolic solvers to prove correctness or to find bugs we can also use them to _symbolically execute_ Bosque programs. The `bsqcheck.js` script has an `--evaluate` mode that takes (small) inputs and can compute the output value.

If we take the calculator example that we previously ran validation on we can use the evaluator mode to compute the sum of 2 and 3 as follows:
```
> node bin/runtimes/bsqcheck.js --evaluate calc.bsq
```

When prompted we can enter the arguments as a JSON array:
```
["NSMain::CalcOp::add", 2, 3]
```

The solver will take these values along with the logical encoding of the program and will infer that the only valid output value is `5`.

## Using the Bosque Language

The current focus of the Bosque project is core language design. As a result there is _no_ support for packaging, deployment, lifecycle management, etc.

**Note: If you are running examples from the "Learn Bosque Programming" book please use the [LearnBosqueProgramming](https://github.com/microsoft/BosqueLanguage/tree/LearnBosqueProgramming) branch which is sync'd with the version of code used in the book.**

### Requirements

In order to build the language the following are needed:

- 64 bit Operating System
- The LTS version of [node.js](https://nodejs.org/en/download/) ( According to your OS )
- Typescript (install with: `npm i typescript -g`)
- Git and [git-lfs](https://git-lfs.github.com/) setup
- A C++ compiler -- by default `clang` on Linux/Mac and `cl.exe` on Windows

### Build & Test

The `impl` directory contains the reference implementation parser, type checker, interpreter, and command line runner. In this directory, build and test the Bosque reference implementation with:

```none
npm install && npm test
```

The Z3 theorem prover is provided as a binary dependency in the repo via git LFS. To ensure these are present you will need to have [git-lfs](https://git-lfs.github.com/) installed, run `git lfs install` to setup the needed hooks, and pull. 

### Visual Studio Code Integration

This repository provides basic [Visual Studio Code](https://code.visualstudio.com/) IDE support for the Bosque language (currently limited to syntax and brace highlighting). The installation requires manually copying the full `bosque-language-tools/` folder into your user `.vscode/extensions/` directory and restarting VSCode.

## Contribute

This project welcomes community contributions.

* [Submit bugs](https://github.com/Microsoft/BosqueLanguage/issues) and help us verify fixes.
* [Submit pull requests](https://github.com/Microsoft/BosqueLanguage/pulls) for bug fixes and features and discuss existing proposals.
* Chat about the [@BosqueLanguage](https://twitter.com/BosqueLanguage) (or [#BosqueLanguage](https://twitter.com/hashtag/BosqueLanguage)) on Twitter.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

Please refer to [Contribution Guidelines](CONTRIBUTING.md) for more details.

## License

Code licensed under the [MIT License](LICENSE.txt).
