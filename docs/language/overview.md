# Bosque Language Overview

The Bosque language is a hybrid of functional programming language semantics and an ergonomic block & assignment-based syntax. This allows developers to organize code into familiar/natural blocks and compositions while, simultaneously, benefiting from the correctness and simplicity of a functional programming model. 

# Table of Contents

[**Type System**](#Type-System)

  0. [Primitive Types](#Primitive-Types)
  1. [Nominal Types](#Nominal-Types)
      - [entity](#Entity)
      - [concept](#Concept)
  2. [Structural Types](#Structural-Types)
      - [Tuples](#Tuples)
      - [Records](#Records)
  3. [Code Block Types](#Parameter-Code-Block-Types)
  4. [Combination Types](#Combination-Types)
  5. [Ephemeral Lists](#Ephemeral-Lists)
  6. [Containers](#Containers)

[**Type Checking and Inference**](#Type-Checking-and-Inference)

[**Declarations**](#Declarations)

  1. [Namespaces](#Namespaces)
      - [Constants](#Constants)
      - [Functions](#Functions)
      - [Operators](#Operators)
      - [Types](#Types)
  2. [Type Members](#Type-Members)
      - [MORE](#MORE)

[**Expressions**](#Expressions)

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

The Bosque language supports a simple and non-opinionated type system that allows developers to use a range of structural, nominal, and combination types to best convey their intent and flexibly encode the relevant features of the problem domain. All type names **must** start with a capital letter - `MyType` is a valid type name while `myType` is not. Template type names are single capital letters -- `T`, `V`, etc.

## <a name="Primitive-Types"></a>Primitive Types

Bosque provides a range of standard primitive types, numerics, strings, times, etc. as part of the core implementation.

- **None:** The type `None` is the special primitive _none-able_ type that has the single (unique) `none` value.
- **Nothing:** The type `Nothing` special primitive _nothing_ `Option<T>` type that has the single (unique) `nothing` value.
- **Bool:** The type `Bool` is contains the special `true` and `false` values.
- **Nat & Int:** The `Nat` and `Int` types represent unsigned and signed (respectively) 64 bit numbers. Overflows, underflows, and div-by-0 all raise fatal errors.
- **BigNat & BigInt:** The `BigNat` and `BigInt` types represent unsigned and signed (respectively) unbounded integral numbers. Underflows and div-by-0 raise fatal errors while overflows are either limited to an implementation defined max (at least 256 bits or Out-of-Memory) and saturating operations `++`, `--`, `**` are provided (TODO).
- **Float & Decimal:** The `Float` type is a 64 bit IEEE-754 floating point number. The `Decimal` type is a 64 bit decimal floating point number.
- **Rational:** The `Rational` type is a rational representation of a number with a `BigInt` valued numerator and a `Nat` valued (non-zero) denominator. Overflow in the denominator is handled by rounding to the nearest representable value.
- **String:** The `String` type in Bosque is a utf-8 unicode string. Notably this string type does not support arbitrary indexing (which is undefined for utf-8 multibyte characters). Instead operations must use regex based slicing, extraction, etc.
- **ASCIIString:** (TODO) The `ASCIIString` type is a ASCII char based string that can be meainingfully processed using integral index operations.
- **ByteBuffer:** The `ByteBuffer` type is a 0 indexed array of uninterpreted 8 bit values.
- **Regex:** the `Regex` type is the type assigned to all regex literals in the program.

In addition to the basic types enumerated above, Bosque also provides a range of commonly useful types for dealing with time, locations, events, and identity.

- **DateTime:** The `DateTime` type represents a _human scale_ time with minute precision (so no leap second issues). The representation is TimeZone based and does not allow naive comparision for ordering or computation of offsets as these are ill defined and non-deterministic operations (e.g. when the times are in the future a TZ meaning may change).
- **UTCDateTime:** The `UTCDateTime` type is a specialized version of `DateTime` that is fixed at UTC for the timezone. This allows us to do direct ordering and arithmatic on the dates.
- **CalendarDate:** The `CalendarDate` type is a _date only_ value, month, day, year, so it is free of TZ related complications and can be directly ordered and used for offset date computation.
- **TickTime:** the `TickTime` type is a 54 bit, nano-second interval, epoch based time [TAI derived](https://www.nist.gov/pml/time-and-frequency-division/nist-time-frequently-asked-questions-faq). This time is monotone and corresponds to real elapsed time.
- **LogicalTime:** the `LogicalTime` type is a logical tick based time useful for causal ordering events in a system. 
- **ISOTimeStamp:** the `ISOTimeStamp` type is a ISO 8061 timestamp with milliseconds and a timezone. It is intended to be used for legacy interop and for _human friendly_ timestamps in logs or other records. Historical values are stable but future values may be unstable as time-zone changes or leap-seconds are added.
- **UUID4 & UUID7:** the UUID types for `UUID4` and `UUID7` are natively supported in Bosque. 
- **SHAContentHash:** the `SHAContentHash` type is a SHA3 512 bit hash code. Bosque has support (TODO) for computing SHA hashes of any value and can produce a result of type `SHAContentHash` or `SHAContentHashOf<T>`.
- **LatLongCoordinate:**: the `LatLongCoordinate` is a decimal degree encoding (6 decimal digits) of a latitude and longitude value.

## <a name="Nominal-Types"></a>Nominal Types

The nominal type system is a mostly standard _object-oriented_ design with parametric polymorphism provided by generics. Bosque also supports type aliasing `typedef` and wrapping of primitive types with `typedecl`.

## <a name="Entity"></a>Entity
Entities are concrete object-oriented style (member fields, methods, etc.) types that can be created. An entity will never have another type that is a strict subtype of it! Entities are always subtypes of the special `Some` and `Any` concepts and user defined entities are always subtypes of the special `Object` concept. Entities can be declared as polymorphic with template parameters. In Bosque templates are not parametric in their instantiated types -- e.g. `List<Int>` is not a subtype of `List<Any>`.

Entity type references are simply the (scoped) name of the type such as `Foo` for a locally scoped type or `Bar::Foo`, `Bar::Baz::Foo` for a type `Baz` declared in the given scope (namespace or type scope). Entity types may also be parametric, such as `List<Int>` or `Foo<Bool, Map<Int, Int>>`.

In Bosque the `typedef` declaration can be used to create a nominal alias for any type. This alias is not a _distinct_ type and, in type checking and execution, is replaced by the underlying aliased type (see also `typedecl` below).

There are several special entity types in Bosque:
- **Enum:** Bosque supports `enum` types as nominal types. The underlying values can be any _typedeclable_ type but the enum type is always a distinct type in the program.
- **typedecl:** To create a new and distnct nominal type for any _typedeclable_ type the `typedecl` keyword can be used to create a new type that is has an identical value representation (accessable via the `value` method) to the underlying type but is a distinct type in the program.
- **StringOf&lt;T&gt; & DataString&lt;T&gt:** The `StringOf<T>` and `DataString<T>` types in the program (also `ASCIIStringOf<T>` and `ASCIIDataString<T>` types) are dsistinct string types. The StringOf flavors are parameterized by Validator regexes (the underlying string is in the specified language) while the DataString flavors are parameterized by types that provide the `Parsable` concept (i.e. they have an `accepts` function).
- **DataBuffer&lt;T&gt;:** The `DataBuffer<T>` type is similar to the `DataString<T>` type except the underlying value is a `ByteBuffer`.
- **Something&lt;T&gt;:** is the subtype of `Option<T>` that represents a value (as opposed to the special `Nothing` subtype). There is a special constructor operator `something` that can be used as a type infering constructor in addition to explict construction. 
- **Result&lt;T, E&gt;::Ok & Result&lt;T, E&gt;::Err:** Bosque provides a standard `Result<T, E>` concept with `Ok` and `Err` entities. If omitted from the type the error `E` type is assumed to be `None`. As with `Something<T>` there are special (shorthand) type infering keywords `ok` and `err` for constructing these types. 

## <a name="Concept"></a>Concept

Bosque concept types are fully abstract and can never be instantiated concretely. The entity types can provide concepts as well as override definitions in them and can be instantiated concretely but can never be further inherited from.

xxxx;