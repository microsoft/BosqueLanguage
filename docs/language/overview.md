# Bosque Language Overview

The Bosque language is a hybrid of functional programming language semantics and an ergonomic block & assignment-based syntax. This allows developers to organize code into familiar/natural blocks and compositions while, simultaneously, benefiting from the correctness and simplicity of a functional programming model. 

# Table of Contents

[Type System](#Type-System)
  0. [Primitive Types](#Primitive-Types)
  1. [Nominal Types](#Nominal-Types)
      - [entity](#Entity)
      - [concept](#Concept)
      - [enum](#Enum)
      - [StringOf/DataString](#Typed-Strings)
      - [typedef](#Typedef)
      - [typedecl](#Typedecl)
      - [datatype](#Datatype)
  2. [Structural Types](#Structural-Types)
      - [Tuples](#Tuples)
      - [Records](#Records)
  3. [Code Block Types](#Parameter-Code-Block-Types)
  4. [Combination Types](#Combination-Types)
  5. [Ephemeral Lists](#Ephemeral-Lists)
  6. [Special Types](#Special-Types)

[Type Checking and Inference](#Type-Checking-and-Inference)

[Declarations](#Declarations)
  1. [Namespaces](#Namespaces)
      - [Constants](#Constants)
      - [Functions](#Functions)
      - [Operators](#Operators)
      - [Types](#Types)
  2. [Type Members](#Type-Members)
      - [MORE](#MORE)

[Expressions](#Expressions)
  - [5.1 Arguments](#5.1-Arguments)
  - [5.2 Constants](#5.2-Constants)
  - [5.3 Variable and Scoped Access](#5.3-Variable-and-Scoped-Access)
  - [5.4 Tuple and Record Constructors](#5.4-Tuple-and-Record-Constructors)
  - [5.5 Entity Constructors](#5.5-Entity-Constructors)
  - [5.6 PCode Constructors](#5.6-PCode-Constructors)
  - [5.7 Scoped Invokes](#5.7-Scoped-Invokes)
  - [5.8 None-Chaining](#5.8-Chaining-and-None-Chaining)
  - [5.9 Tuple Typed Access Operators](#5.9-Tuple-Typed-Access-Operators)
  - [5.10 Record Typed Access Operators](#5.10-Record-Typed-Access-Operators)
  - [5.11 Nominal Typed Access Operators](#5.11-Nominal-Typed-Access-Operators)
  - [5.12 Typed Projection](#5.12-Typed-Projection)
  - [5.13 Update](#5.13-Update)
  - [5.14 Merge](#5.14-Merge)
  - [5.15 PCode Apply](#5.15-PCode-Apply)
  3. [Function Invoke](Function-Invoke)
  3. [Method Invoke](#Method-Invoke)
  3. [Operator Invoke](#Operator-Invoke)
  - [5.17 Unary Operators](#5.17-Unary-Operators)
  - [5.18 Binary Operators](#5.18-Binary-Operators)
  - [5.19 Equality Comparison](#5.19-Equality-Comparison)
  - [5.20 Order Comparison](#5.20-Order-Comparison)
  - [5.21 Logic Operators](#5.21-Logic-Operators)
  - [5.22 None Coalescing](#5.22-None-Coalescing)
  - [5.23 Select](#5.23-Select)
  - [5.24 Statement Expressions](#5.24-Statement-Expressions)
  - [5.25 Synthesis Blocks](#5.25-Synthesis-Blocks)

[Statements](#Statements)
  - [6.1 Empty](#6.1-Empty)
  - [6.2 Variable Declaration](#6.2-Variable-Declaration)
  - [6.3 Variable Assignment](#6.3-Variable-Assignment)
  - [6.4 Structured Declaration and Assignment](#6.4-Structured-Declaration-and-Assignment)
  - [6.5 Return and Yield](#6.5-Return-and-Yield)
  - [6.6 Validation](#6.6-Validation)
  - [6.7 If-Then-Else](#6.7-If-Then-Else)
  - [6.8 Switch](#6.8-Switch)
  - [6.9 Block](#6.9-Block)
  - [6.9 Statement Calls](#6.9-Statement-Calls)


# <a name="Type-System"></a>Type System

The Bosque language supports a simple and non-opinionated type system that allows developers to use a range of structural, nominal, and combination types to best convey their intent and flexibly encode the relevant features of the problem domain. All type names **must** start with a capital letter - `MyType` is a valid type name while `myType` is not.

## <a name="Primitive-Types"></a>Primitive Types

Bosque provides a range of standard primitive types, numerics, strings, times, etc. as part of the core implementation.

- **None:** The type `None` is the special primitive _none-able_ type that has the single (unique) `none` value.
- **Nothing:** The type `Nothing` special primitive _nothing_ `Option` type that has the single (unique) `nothing` value.
- **Bool:** The type `Bool` is contains the special `true` and `false` values.
- **Nat & Int:** The `Nat` and `Int` types represent unsigned and signed (respectively) 64 bit numbers. Overflows, underflows, and div-by-0 all raise fatal errors.
- **BigNat & BigInt:** The `BigNat` and `BigInt` types represent unsigned and signed (respectively) unbounded integral numbers. Underflows and div-by-0 raise fatal errors while overflows are either limited to an implementation defined max (at least 256 bits or Out-of-Memory) and saturating operations `++`, `--`, `**` are provided (TODO).
- **Float & Decimal:** The `Float` type is a 64 bit IEEE-754 floating point number. The `Decimal` type is a 64 bit decimal floating point number.
- **Rational:** The `Rational` type is a rational representation of a number with a `BigInt` valued numerator and a `Nat` valued (non-zero) denominator. Overflow in the denominator is handled by rounding to the nearest representable value.
- **String:** The `String` type in Bosque is a utf-8 unicode string. Notably this string type does not support arbitrary indexing (which is undefined for utf-8 multibyte characters). Instead operations must use regex based slicing, extraction, etc.
- **ASCIIString:** (TODO) The `ASCIIString` type is a ASCII char based string that can be meainingfully processed using integral index operations.
- **ByteBuffer:** The `ByteBuffer` type is a 0 indexed array of uninterpreted 8 bit values.

In addition to the basic types enumerated above, Bosque also provides a range of commonly useful types for dealing with time, locations, events, and identity.

- **DateTime:** The `DateTime` type represents a _human scale_ time with minute precision (so no leap second issues). The representation is TimeZone based and does not allow naive comparision for ordering or computation of offsets as these are ill defined and non-deterministic operations (e.g. when the times are in the future a TZ meaning may change).

The 

## <a name="Nominal-Types"></a>Nominal Types

The nominal type system is a mostly standard _object-oriented_ design with parametric polymorphism provided by generics. Bosque also supports type aliasing `typedef` and wrapping of primitive types with `typedecl`.

## <a name="Entity"></a>Entity


- [entity](#Entity)
      - [concept](#Concept)
      - [enum](#Enum)
      - [StringOf/DataString](#Typed-Strings)
      - [typedef](#Typedef)
      - [typedecl](#Typedecl)
      - [datatype](#Datatype)

Users can define abstract types with `concept` declarations, which allow both abstract definitions and inheritable implementations for `const` members ([TODO]()), `function` members, `field` members, and (virtual) `method` members. Bosque `concept` types are fully abstract and can never be instantiated concretely. The `entity` types can provide concepts as well as override definitions in them and can be instantiated concretely but can never be further inherited from.

Developers can alias types or create special types ([TODO]()) using `typedef`, `enum`, and `identifier` constructs ([TODO]()).

The Bosque core library defines several unique concepts/entities. The `Any` type is an uber type which all others are a subtype of, the `None` and `Some` types are for distinguishing around the unique `none` value, and `Tuple`, `Record`, etc. exist to unify with the structural type system ([section 2](#2-Core-Types)). The language has primitives for `Bool`, `Int`, `String`, etc. as well as the expected set of parametric collection types such as `List<T>` `Map<K, V>` ([section 3](#2-Collections)).

Examples of nominal types include:

```none
MyType       //user declared concept or entity
Some         //core library declared concept
List<Int>    //core collection with generic parameter Int
```
