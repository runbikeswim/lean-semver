# An Implementation of [Semantic Versioning (SemVer)](https://semver.org/) in [Lean](https://lean-lang.org/)

## About 

[Semantic Versioning (SemVer)](https://semver.org/) defines a way to use versions, based on
* a grammar in Backus–Naur Form (BNF) for valid versions identifiers,
* a notion of precedence for version identifiers and
* rules for increasing version identifiers in case of changes.

This repository contains an implementation of Semantic Versioning in Lean in file [SemVer/Basic.lean](SemVer/Basic.lean). 

It defines
1. types that coincide with the symbols of the BNF specification,
1. functions `lt` and `decLt` for most of the types so that comparing two versions based on the precedence for two versions is possible and
1. parsers for converting strings into terms of the aforementioned types.

Thus, it can be used for
1. checking if a string complies to the syntax of versions 
1. determining if for two versions, _a_ and _b_, _a < b_ holds tue, i.e. if _a_ has lower precedence than _b_

as defined by Sematic Versioning.

## How to run it

[Install Lean](https://lean-lang.org/install/), clone this repository and then execute
```
lake exe lean-semver
```

## How to use it

The program prompts you to enter two version identifiers. Based on that, it prints some text to the console.

The expression in the last line, indicates if the version entered first is less than the second one, based on the 
precedence rules defined by semantic versioning. 

### Examples 

The following two examples show the out put of program `lean-semver` and user input 
(after `-->` for the first and after `->` for the second prompt).

#### Example 1

```
please enter the first version identifier --> 1.1.2-alpha.beta.gamma.2+2025-09-07.17-03-42.0000
please enter the second version identifier -> 1.1.2-alpha.beta.gamma.10+2025-09-07.16-23-57.0001
the term representing the first version identifier is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [PreRelIdent.alphanumIdent "alpha",
                 PreRelIdent.alphanumIdent "beta",
                 PreRelIdent.alphanumIdent "gamma",
                 PreRelIdent.numIdent "2"],
  build := some [BuildIdent.alphanumIdent "2025-09-07", BuildIdent.alphanumIdent "17-03-42", BuildIdent.digits "0000"] }
the term representing the second version identifier is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [PreRelIdent.alphanumIdent "alpha",
                 PreRelIdent.alphanumIdent "beta",
                 PreRelIdent.alphanumIdent "gamma",
                 PreRelIdent.numIdent "10"],
  build := some [BuildIdent.alphanumIdent "2025-09-07", BuildIdent.alphanumIdent "16-23-57", BuildIdent.digits "0001"] }
for the precedence of the first and second version, the following is true:
    1.1.2-alpha.beta.gamma.2+2025-09-07.17-03-42.0000 < 1.1.2-alpha.beta.gamma.10+2025-09-07.16-23-57.0001
```

#### Example 2

```
please enter the first version identifier --> 1.1.2-alpha.beta.gamma.2+2025-09-07.16-23-57.0001
please enter the second version identifier -> 1.1.2-alpha.beta.gamma.2+2025-09-07.17-03-42.0000
the term representing the first version identifier is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [PreRelIdent.alphanumIdent "alpha",
                 PreRelIdent.alphanumIdent "beta",
                 PreRelIdent.alphanumIdent "gamma",
                 PreRelIdent.numIdent "2"],
  build := some [BuildIdent.alphanumIdent "2025-09-07", BuildIdent.alphanumIdent "16-23-57", BuildIdent.digits "0001"] }
the term representing the second version identifier is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [PreRelIdent.alphanumIdent "alpha",
                 PreRelIdent.alphanumIdent "beta",
                 PreRelIdent.alphanumIdent "gamma",
                 PreRelIdent.numIdent "2"],
  build := some [BuildIdent.alphanumIdent "2025-09-07", BuildIdent.alphanumIdent "17-03-42", BuildIdent.digits "0000"] }
for the precedence of the first and second version, the following is true:
  ¬ 1.1.2-alpha.beta.gamma.2+2025-09-07.16-23-57.0001 < 1.1.2-alpha.beta.gamma.2+2025-09-07.17-03-42.0000
```

## How it is implemented

### Parsing

Based on [grammar](https://semver.org/#backusnaur-form-grammar-for-valid-semver-versions), types are defined.
Each of these types has a function `parse` that converts a `String` as input into a term of the 
respective type or, if this is not possible, returns an error.

#### Correct Version Identifiers

```
#eval Version.parse "1.0.1-alpha.0.1023.xyz"
```
results in 
```
ParserResult.success
  { toVersionCore := { major := 1, minor := 0, patch := 1 },
    preRelease := some [PreRelIdent.alphanumIdent "alpha",
                   PreRelIdent.numIdent "0",
                   PreRelIdent.numIdent "1023",
                   PreRelIdent.alphanumIdent "xyz"],
    build := none }
```

#### First Example of an Incorrect Version Identifier

```
#eval Version.parse "1.0.1.1-alpha.0.1023.xyz"
```
returns
```
ParserResult.failure
  { message := "exactly three numbers - separated by '.' - must be provided, not one more, not one less",
    position := 0 }
```

#### Second Example of an Incorrect Version Identifier

```
#eval Version.parse "1.0.1-alpha.00.1023.xyz"
```
leads to
```
ParserResult.failure
  { message := "neither alphanumeric nor numeric identifier found because \n1. alphanumeric identifier must contain a non-digit character in position 14\n2. numeric identifiers must not have leading zeros in position 12",
    position := 14 }
```

### Rendering

Each of the types implements `toString`, which renders a term of this type to a string that follows the grammar.

The following code
```
def test_to_string : IO Unit := do
  let version ← Version.doParserResult (Version.parse "2.0.0-alpha2.1234+nightly-2025-09-06.1234")
  IO.println version.toString

#eval test_to_string
```
results in 
```
2.0.0-alpha2.1234+nightly-2025-09-06.1234
```
as output. `toString` is the inverse operation of `parse`.

### Precedence 

Semantic versioning defines precedence rules for version identifiers. 
These are implemented by functions `lt` (less than) and `decLt` (decidable less than) provided by all types,
where it is required.

For terms t₁ and t₂ of the same type, it can this be determined if t₁ < t₂ or ¬ t₁ < t₂ holds true.
In particular, as terms of type `Version`, two version identifiers can be compared with each other.

The following propositions are all true:
* `1.9.0 < 1.10.0`, since the minor version 9 is less than 10 (compared as numbers not as strings) 
* `1.0.0-alpha.beta < 1.0.0-beta.11`, because the version cores are identical but the first pre-release is less than the second (as strings in lexicographical order)
* `¬ 1.0.0+20130313144700 < 1.0.0+21AF26D3----117B344092BD`, because the core versions (first three numbers) as well as the pre-releases are (both empty) are identical and the build information has no effect on precedence
