/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

run all tests via
```sh
  lake exe tests
```

Breaking tests will cause panic due to failing `assert!`s.
-/

import SemVer

/-
Print something to stdout if silent is false
-/
def maybePrintln (s : String) (silent : Bool := false): IO Unit :=
  if !silent then
    IO.println s
  else
    IO.print ""

def expect_eq {α : Type} [Repr α] [DecidableEq α] (a b : α) (silent : Bool := false): IO Unit :=
  assert! a = b
  maybePrintln s!"+++ SUCCESS +++\n{reprStr a} = {reprStr b}" silent

def expect_not_eq {α : Type} [Repr α] [DecidableEq α] (a b : α) (silent : Bool := false) : IO Unit :=
  assert! ¬ (a = b)
  maybePrintln s!"+++ SUCCESS +++\n¬ {reprStr a} = {reprStr b}" silent

def expect_lt {α : Type} [Repr α] [LT α] [DecidableLT α] (a b : α) (silent : Bool := false) : IO Unit :=
  assert! (a < b)
  maybePrintln s!"+++ SUCCESS +++\n{reprStr a} < {reprStr b}" silent

def expect_not_lt {α : Type} [LT α] [Repr α] [DecidableLT α] (a b : α) (silent : Bool := false) : IO Unit :=
  assert! ¬ (a < b)
  maybePrintln s!"+++ SUCCESS +++\n¬ {reprStr a} < {reprStr b}" silent

def expect_failure {α : Type} (a : ParserResult α) (silent : Bool := false) : IO Unit :=
  match a with
  | .failure e =>
    match e.input with
    | some str =>
      maybePrintln s!"+++ SUCCESS +++\ncorrectly detected error '{e.message}'\nin position {e.position} of '{str}'" silent
    | none =>
      maybePrintln s!"+++ SUCCESS +++\ncorrectly detected error '{e.message}'\nin position {e.position} of the input string" silent
  | .success _ => assert! false; maybePrintln "--- FAILURE ---" silent

section Data

def sem_ver_spec: List String := [
    r#"The following text is a slightly changed version of the respective section in https://semver.org/ (2.0.0)"#,
    r#"which is made available under the [Creative Commons ― CC BY 3.0](https://creativecommons.org/licenses/by/3.0/) license."#,
    r#"          Semantic Versioning Specification (SemVer)"#,
    r#"          =========================================="#,
    r#"The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT","#,
    r#""SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this"#,
    r#"document are to be interpreted as described in"#,
    r#"[RFC 2119](https://tools.ietf.org/html/rfc2119)."#,
    r#""#,
    r#"1.  Software using Semantic Versioning MUST declare a public API. This"#,
    r#"    API could be declared in the code itself or exist strictly in"#,
    r#"    documentation. However it is done, it SHOULD be precise and"#,
    r#"    comprehensive."#,
    r#""#,
    r#"2.  A normal version number MUST take the form X.Y.Z where X, Y, and Z"#,
    r#"    are non-negative integers, and MUST NOT contain leading zeroes. X is"#,
    r#"    the major version, Y is the minor version, and Z is the patch"#,
    r#"    version. Each element MUST increase numerically."#,
    r#"    For instance: 1.9.0 -> 1.10.0 -> 1.11.0."#,
    r#""#,
    r#"3.  Once a versioned package has been released, the contents of that"#,
    r#"    version MUST NOT be modified. Any modifications MUST be released as"#,
    r#"    a new version."#,
    r#""#,
    r#"4.  Major version zero (0.y.z) is for initial development. Anything MAY"#,
    r#"    change at any time. The public API SHOULD NOT be considered stable."#,
    r#""#,
    r#"5.  Version 1.0.0 defines the public API. The way in which the version"#,
    r#"    number is incremented after this release is dependent on this public"#,
    r#"    API and how it changes."#,
    r#""#,
    r#"6.  Patch version Z (x.y.Z | x > 0) MUST be incremented if only"#,
    r#"    backward compatible bug fixes are introduced. A bug fix is defined"#,
    r#"    as an internal change that fixes incorrect behavior."#,
    r#""#,
    r#"7.  Minor version Y (x.Y.z | x > 0) MUST be incremented if new,"#,
    r#"    backward compatible functionality is introduced to the public API."#,
    r#"    It MUST be incremented if any public API functionality is marked as"#,
    r#"    deprecated. It MAY be incremented if substantial new functionality"#,
    r#"    or improvements are introduced within the private code. It MAY"#,
    r#"    include patch level changes. Patch version MUST be reset to 0 when"#,
    r#"    minor version is incremented."#,
    r#""#,
    r#"8.  Major version X (X.y.z | X > 0) MUST be incremented if any"#,
    r#"    backward incompatible changes are introduced to the public API. It"#,
    r#"    MAY also include minor and patch level changes. Patch and minor"#,
    r#"    versions MUST be reset to 0 when major version is incremented."#,
    r#""#,
    r#"9.  A pre-release version MAY be denoted by appending a hyphen and a"#,
    r#"    series of dot separated identifiers immediately following the patch"#,
    r#"    version. Identifiers MUST comprise only ASCII alphanumerics and"#,
    r#"    hyphens [0-9A-Za-z-]. Identifiers MUST NOT be empty. Numeric"#,
    r#"    identifiers MUST NOT include leading zeroes. Pre-release versions"#,
    r#"    have a lower precedence than the associated normal version. A"#,
    r#"    pre-release version indicates that the version is unstable and might"#,
    r#"    not satisfy the intended compatibility requirements as denoted by"#,
    r#"    its associated normal version. Examples: 1.0.0-alpha, 1.0.0-alpha.1,"#,
    r#"    1.0.0-0.3.7, 1.0.0-x.7.z.92, 1.0.0-x-y-z.--"#,
    r#""#,
    r#"10. Build metadata MAY be denoted by appending a plus sign and a series"#,
    r#"    of dot separated identifiers immediately following the patch or"#,
    r#"    pre-release version. Identifiers MUST comprise only ASCII"#,
    r#"    alphanumerics and hyphens [0-9A-Za-z-]. Identifiers MUST NOT be"#,
    r#"    empty. Build metadata MUST be ignored when determining version"#,
    r#"    precedence. Thus two versions that differ only in the build"#,
    r#"    metadata, have the same precedence. Examples: 1.0.0-alpha+001,"#,
    r#"    1.0.0+20130313144700, 1.0.0-beta+exp.sha.5114f85,"#,
    r#"    1.0.0+21AF26D3----117B344092BD"#,
    r#""#,
    r#"11. Precedence refers to how versions are compared to each other when"#,
    r#"    ordered."#,
    r#""#,
    r#"    1.  Precedence MUST be calculated by separating the version into"#,
    r#"        major, minor, patch and pre-release identifiers in that order"#,
    r#"        (build metadata does not figure into precedence)."#,
    r#""#,
    r#"    2.  Precedence is determined by the first difference when comparing"#,
    r#"        each of these identifiers from left to right as follows: major,"#,
    r#"        minor, and patch versions are always compared numerically."#,
    r#""#,
    r#"        Example: 1.0.0 < 2.0.0 < 2.1.0 < 2.1.1"#,
    r#""#,
    r#"    3.  When major, minor, and patch are equal, a pre-release version"#,
    r#"        has lower precedence than a normal version:"#,
    r#""#,
    r#"        Example: 1.0.0-alpha < 1.0.0"#,
    r#""#,
    r#"    4.  Precedence for two pre-release versions with the same major,"#,
    r#"        minor, and patch version MUST be determined by comparing each"#,
    r#"        dot separated identifier from left to right until a difference"#,
    r#"        is found as follows:"#,
    r#""#,
    r#"        1.  Identifiers consisting of only digits are compared"#,
    r#"            numerically."#,
    r#""#,
    r#"        2.  Identifiers with letters or hyphens are compared lexically"#,
    r#"            in ASCII sort order."#,
    r#""#,
    r#"        3.  Numeric identifiers always have lower precedence than"#,
    r#"            non-numeric identifiers."#,
    r#""#,
    r#"        4.  A larger set of pre-release fields has a higher precedence"#,
    r#"            than a smaller set, if all of the preceding identifiers are"#,
    r#"            equal."#,
    r#""#,
    r#"        Example: 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta <"#,
    r#"        1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 <"#,
    r#"        1.0.0"#,
    r#""#
  ]

def version_strings_in_sem_ver_spec := [
    "2.0.0",
    "1.9.0", "1.10.0", "1.0.0", "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-0.3.7",
    "1.0.0-x.7.z.92", "1.0.0-x-y-z.--", "1.0.0-alpha+001", "1.0.0+20130313144700",
    "1.0.0-beta+exp.sha.5114f85", "1.0.0+21AF26D3----117B344092BD",
    "1.0.0", "2.0.0", "2.1.0", "2.1.1", "1.0.0-alpha",
    "1.0.0", "1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta",
    "1.0.0-beta", "1.0.0-beta.2", "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"
  ]

/-
Strings representing valid semantic versions, copied from https://regex101.com/r/Ly7O1x/3/
-/
def valid_version_strings := [
    "0.0.4", "1.2.3", "10.20.30", "1.1.2-prerelease+meta", "1.1.2+meta", "1.1.2+meta-valid", "1.0.0-alpha",
    "1.0.0-beta", "1.0.0-alpha.beta", "1.0.0-alpha.beta.1", "1.0.0-alpha.1", "1.0.0-alpha0.valid",
    "1.0.0-alpha.0valid", "1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay",
    "1.0.0-rc.1+build.1", "2.0.0-rc.1+build.123", "1.2.3-beta", "10.2.3-DEV-SNAPSHOT", "1.2.3-SNAPSHOT-123",
    "1.0.0", "2.0.0", "1.1.7", "2.0.0+build.1848", "2.0.1-alpha.1227", "1.0.0-alpha+beta",
    "1.2.3----RC-SNAPSHOT.12.9.1--.12+788", "1.2.3----R-S.12.9.1--.12+meta",
    "1.2.3----RC-SNAPSHOT.12.9.1--.12", "1.0.0+0.build.1-rc.10000aaa-kk-0.1",
    "99999999999999999999999.999999999999999999.99999999999999999", "1.0.0-0A.is.legal"
  ]

def invalid_version_strings := [
    "1", "1.2", "1.2.3-0123", "1.2.3-0123.0123", "1.1.2+.123", "+invalid", "-invalid",
    "-invalid+invalid", "-invalid.01", "alpha", "alpha.beta", "alpha.beta.1", "alpha.1",
    "alpha+beta", "alpha_beta", "alpha.", "alpha..", "beta", "1.0.0-alpha_beta", "-alpha.",
    "1.0.0-alpha..", "1.0.0-alpha..1", "1.0.0-alpha...1", "1.0.0-alpha....1",
    "1.0.0-alpha.....1", "1.0.0-alpha......1", "1.0.0-alpha.......1", "01.1.1", "1.01.1",
    "1.1.01", "1.2", "1.2.3.DEV", "1.2-SNAPSHOT", "1.2.31.2.3----RC-SNAPSHOT.12.09.1--..12+788",
    "1.2-RC-SNAPSHOT", "-1.0.3-gamma+b7718", "+justmeta", "9.8.7+meta+meta", "9.8.7-whatever+meta+meta",
    "99999999999999999999999.999999999999999999.99999999999999999----RC-SNAPSHOT.12.09.1--------------------------------..12"
  ]

end Data

section Tests

#print "running tests ..."

/- this will cause panic
#eval (Version.parse "1.101").to!
-/

def in_01 := "1.2.3"
def tst_01 : Version :=
  { toVersionCore := { major := 1, minor := 2, patch := 3 }, preRelease := none, build := none }
#eval expect_eq (Version.parse in_01).to! tst_01 true

def in_02 := "1.3.3"
#eval expect_lt (Version.parse in_01).to! (Version.parse in_02).to! true

def in_03 := "1.3.3-alpha.0+build.00001"
def pre_03 : DotSepPreRelIdents :=
  ⟨[PreRelIdent.alphanumIdent ⟨⟨⟨"alpha", rfl⟩, rfl⟩, rfl⟩, PreRelIdent.numIdent ⟨⟨⟨"0", rfl⟩, rfl⟩, rfl⟩], rfl⟩
def bld_03 : DotSepBuildIdents :=
  ⟨[BuildIdent.alphanumIdent ⟨⟨⟨"build", rfl⟩, rfl⟩, rfl⟩, BuildIdent.digits ⟨⟨"00001", rfl⟩, rfl⟩], rfl⟩
def tst_03 : Version := {
    toVersionCore := { major := 1, minor := 3, patch := 3 },
    preRelease := some pre_03,
    build := some bld_03
  }
#eval expect_eq (Version.parse in_03).to! tst_03 true

#eval expect_failure (Version.parse "1.03.3") true
#eval expect_failure (Version.parse "1.3.3-alpha.01") true
#eval expect_failure (Version.parse "1.3.3-alpha.0-build.00001") true
#eval expect_failure (Version.parse "1.3.3+alpha.0+build.00001") true
#eval expect_failure (Version.parse "1.3.3-alpha.01+build.00001") true
#eval expect_failure (Version.parse "1.3-alpha.0-build.1") true
#eval expect_failure (Version.parse "1.0.0-x-y-z.--.") true

def _04 := (List.flatten (List.filter (fun l : List Version => !l.isEmpty) (sem_ver_spec.map extractVersions)))
#eval expect_eq version_strings_in_sem_ver_spec (_04.map fun v : Version => v.toString) true

def _05 := version_strings_in_sem_ver_spec.map fun s: String => Version.parse s
#eval expect_eq _04 (_05.map fun p => p.to!) true

def _06 := valid_version_strings.map fun s: String => Version.parse s
#eval expect_eq valid_version_strings (_06.map fun p => p.to!.toString) true

def _07 := invalid_version_strings.map fun s: String => Version.parse s
#eval expect_eq (_07.foldl (fun b => fun r => b && !r.isSuccess) true) true true

#eval expect_lt (Version.parse "0.10.0").to! (Version.parse "1.0.0-alpha").to! true
#eval expect_lt (Version.parse "1.0.0-alpha").to! (Version.parse "1.0.0-alpha.1").to! true
#eval expect_lt (Version.parse "1.0.0-alpha.1").to! (Version.parse "1.0.0-alpha.beta").to! true
#eval expect_lt (Version.parse "1.0.0-alpha.beta").to! (Version.parse "1.0.0-beta").to! true
#eval expect_lt (Version.parse "1.0.0-beta").to! (Version.parse "1.0.0-beta.2").to! true
#eval expect_lt (Version.parse "1.0.0-beta.2").to! (Version.parse "1.0.0-beta.11").to! true
#eval expect_lt (Version.parse "1.0.0-beta.11").to! (Version.parse "1.0.0-rc.1").to! true
#eval expect_lt (Version.parse "1.0.0-rc.1").to! (Version.parse "1.0.0").to! true

#eval expect_eq (Version.parse "0.10.0").to!.nextMajor (Version.parse "1.0.0").to! true
#eval expect_eq (Version.parse "0.10.0-alpha1").to!.nextMinor (Version.parse "0.11.0").to! true
#eval expect_eq (Version.parse "0.10.1-alpha1+build17").to!.nextPatch (Version.parse "0.10.2").to! true
#eval expect_eq ((Version.parse "0.10.1-alpha1+build17").to!.subsequentPreRelease? "alpha2") (Version.parse "0.10.1-alpha2").to? true

#eval expect_eq ((Version.parse "0.10.1-alpha1+build17").to!.setPreRelease? "alpha2") (Version.parse "0.10.1-alpha2").to? true
#eval expect_eq ((Version.parse "0.10.1-alpha1+build17").to!.setBuild? "build18") (Version.parse "0.10.1-alpha1+build18").to! true

#eval expect_eq (Version.parse "0.10.1-alpha1+build17").to!.isStable false true
#eval expect_eq (Version.parse "0.10.1").to!.isStable false true
#eval expect_eq (Version.parse "1.10.1-alpha1+build.00.11.22").to!.isStable false true
#eval expect_eq (Version.parse "1.10.1").to!.isStable true true

#print "... all tests passed!"

end Tests

def main : IO Unit := do
  IO.println "Good Bye!"
