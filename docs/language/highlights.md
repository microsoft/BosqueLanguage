# Bosque Language Overview

The Bosque language is a hybrid of functional programming language semantics and a novel ergonomic block & assignment-based syntax. The language also provides a range of ergonomic features for writing high reliability code, such as Typed Strings, unit typedecls for primitives, and first-class assertions/pre-post conditions/invariants. This document highlights language features that are new (or maybe less familiar) that are available in the Bsoque langauge. 

# Table of Contents
1. [Immutable Values](#Immutable-Values)
2. [Block Scoping and Updateable Variables](#Block-Scoping)
3. [Ref/Out Parameters](#Reference-Out-Parameters)
4. [Errors and Checks](#Errors-and-Checks)
5. [Invariants and Pre/Post Conditions](#Invariants-and-Conditions)
6. [Typed Strings](#Typed-Strings)
7. [Primitive Type Specialization](#Primitive-Type-Specialization)
8. [Iterative Processing](#Iterative-Processing)
9. [Recursion](#Recursion)
10. [Determinacy](#Determinacy)
11. [Equality and Representation](#Equality-and-Representation)
12. [Atomic Constructors and Factories](#Atomic-Constructors-and-Factories)
13. [Atomic Data Operations](#Atomic-Data-Operations)
14. [Invoke Resolution](#Invoke-Resolution)


