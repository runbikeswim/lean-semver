# An Implementation of [Semantic Versioning (SemVer)](https://semver.org/) in [Lean](https://github.com/leanprover/lean4)


## About 

SemVer defines a way to define version numbers, based on
* a grammar for valid SemVer versions in Backus–Naur Form (BNF)
* a notion of precedence for version and
* rules for increasing version numbers in case of changes

This repository contains an implementation of SemVer in Lean in file [Main.lean](Main.lean) with
1. types coincide with the symbols the BNF specification
1. functions for `<` and `DecidableLT` for comparing two version based on the precedence for two semantic versions
1. parsers for converting strings into terms of the aforementioned types

## How to run it

[Install Lean](https://lean-lang.org/install/), clone this repository and then execute
```
lake exe lean-semver
```

## How to use it

The program prompts you to enter two version numbers. Based on that, it prints some text to the console.

The expression in the last line, indicates if the version entered first is less than the second one, based on the 
precedence rules defined by semantic versioning. 

### Examples

#### Example 1

```
please enter the first version number --> 1.1.2-alpha1+2025-09-07.16-23-57
please enter the second version number -> 1.1.2-alpha1+2025-09-07.17-03-42
the internal representation of the first version number is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [Sum.inl "alpha1"],
  build := some [Sum.inl "2025-09-07", Sum.inl "16-23-57"] }
the internal representation of the second version number is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [Sum.inl "alpha1"],
  build := some [Sum.inl "2025-09-07", Sum.inl "17-03-42"] }
for the precedence of the first and second value, the following is true:
  ¬ 1.1.2-alpha1+2025-09-07.16-23-57 < 1.1.2-alpha1+2025-09-07.17-03-42
```

#### Example 2

```
please enter the first version number --> 1.1.2-alpha1+2025-09-07.16-23-57
please enter the second version number -> 1.1.2-alpha2+2025-09-07.17-03-42
the internal representation of the first version number is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [Sum.inl "alpha1"],
  build := some [Sum.inl "2025-09-07", Sum.inl "16-23-57"] }
the internal representation of the second version number is:
{ toVersionCore := { major := 1, minor := 1, patch := 2 },
  preRelease := some [Sum.inl "alpha2"],
  build := some [Sum.inl "2025-09-07", Sum.inl "17-03-42"] }
for the precedence of the first and second value, the following is true:
    1.1.2-alpha1+2025-09-07.16-23-57 < 1.1.2-alpha2+2025-09-07.17-03-42
```

## How it is implemented

### Parsing

#### Correct Version Number

```
#eval Version.parse "1.0.1-alpha.0.1023.xyz"
```
result in 
```
Sum.inl { toVersionCore := { major := 1, minor := 0, patch := 1 },
  preRelease := some [Sum.inl "alpha", Sum.inr "0", Sum.inr "1023", Sum.inl "xyz"],
  build := none }
```

### Incorrect Version Number

```
#eval Version.parse "1.0.1.1-alpha.0.1023.xyz"
```
returns
```
Sum.inr { message := "exactly three numbers must be provided - not one more, not one less", position := 0 }
```

### Rendering

The last `#eval` in 
```
#eval dot_sep_pre_rel_ident_0 -- [Sum.inl "alpha2", Sum.inr "1234"]
#eval dot_sep_build_ident_0 -- [Sum.inl "nightly-2025-09-06", Sum.inr "1234"]

def version_2 : Version := {
      toVersionCore := { major := 2, minor := 0, patch := 0 },
      preRelease := some dot_sep_pre_rel_ident_0,
      build := some dot_sep_build_ident_0
    }

#eval version_2.toString
```
shows 
```
"2.0.0-alpha2.1234+nightly-2025-09-06.1234"
```

### Precedence 

```
#eval version_core_0 -- { major := 1, minor := 2, patch := 3 }
def version_0 :=  Version.mk version_core_0 none none
#eval version_0 -- { toVersionCore := { major := 1, minor := 2, patch := 3 }, preRelease := none, build := none }

#eval dot_sep_pre_rel_ident_0 -- [Sum.inl "alpha2", Sum.inr "1234"]
def version_1 : Version := {
      toVersionCore := { major := 1, minor := 3, patch := 3 },
      preRelease := some dot_sep_pre_rel_ident_0,
      build := none
    }
#eval version_1

#eval dot_sep_build_ident_0 -- [Sum.inl "nightly-2025-09-06", Sum.inr "1234"]
def version_2 : Version := {
      toVersionCore := { major := 2, minor := 0, patch := 0 },
      preRelease := some dot_sep_pre_rel_ident_0,
      build := some dot_sep_build_ident_0
    }

#eval version_2 /-  { toVersionCore := { major := 2, minor := 0, patch := 0 },
                      preRelease := some [Sum.inl "alpha2", Sum.inr "1234"],
                      build := some [Sum.inl "nightly-2025-09-06", Sum.inr "1234"] } -/

def version_3 : Version := {
      toVersionCore := version_2.toVersionCore,
      preRelease := version_2.preRelease,
      build := none
    }

#eval version_3 /-  { toVersionCore := { major := 2, minor := 0, patch := 0 },
                      preRelease := some [Sum.inl "alpha2", Sum.inr "1234"],
                      build := none } -/

#eval version_0 < version_1 -- true
#eval version_1 < version_2 -- true
#eval version_0 < version_2 -- true
#eval version_2 < version_3 -- false
```

