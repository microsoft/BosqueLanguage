This page is a running index of papers published about or related to the Bosque language. The paper describing the motivation and core concepts in the language is [Regularized Programming with the Bosque Language](#Regularized-Programming).

# 2019

---

## <a name="SafeStrings"></a> SafeStrings Representing Strings as Structured Data
**Authors:**\
David Kelly, Mark Marron, David Clark, Earl T. Barr

**Files:**\
[Technical Report](https://arxiv.org/pdf/1904.11254.pdf)

**Abstract:**\
Strings are ubiquitous in code. Not all strings are created equal, some contain structure that makes them incompatible with other strings. CSS units are an obvious example. Worse, type checkers cannot see this structure: this is the latent structure problem. We introduce _SafeStrings_ to solve this problem and expose latent structure in strings. Once visible, operations can leverage this structure to efficiently manipulate it; further, SafeStrings permit the establishment of closure properties. SafeStrings harness the subtyping and inheritance mechanics of their host language to create a natural hierarchy of string subtypes. SafeStrings define an elegant programming model over strings: the front end use of a SafeString is clear and uncluttered, with complexity confined inside the definition of a particular SafeString. They are lightweight, language-agnostic and deployable, as we demonstrate by implementing SafeStrings in TypeScript. SafeStrings reduce the surface area for cross-site scripting, argument selection defects, and they can facilitate fuzzing and analysis.

---

## <a name="Regularized-Programming"></a> Regularized Programming with the Bosque Language
**Authors:**\
Mark Marron

**Files:**\
[Technical Report](https://www.microsoft.com/en-us/research/publication/regularized-programming-with-the-bosque-language/)

**Abstract:**\
The rise of _Structured Programming_ and _Abstract Data Types_ in the 1970's represented a major shift in programming languages. These methodologies represented a move away from a programming model that reflected incidental features of the underlying hardware architecture and toward a model that emphasized programmer intent more directly. This shift simultaneously made it easier and less error prone for a developer to convert their mental model of a system into code and led to a golden age of compiler and IDE tooling development. This paper takes another step on this path by further lifting the model for iterative processing away from low-level loop actions, enriching the language with algebraic data transformation operators, and further simplifying the problem of reasoning about program behavior by removing incidental ties to a particular computational substrate and indeterminate behaviors. We believe that, just as structured programming did years ago, this _regularized programming_ model will lead to massively improved developer productivity, increased software quality, and enable a second golden age of developments in compilers and developer tooling.

**This version is now slightly out-of-date with the language implementation. A updated version should be available shortly.**

---
