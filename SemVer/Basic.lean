/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

section ParserErrors

/--
A parser error is a structure that contains the error message and a number that
is the position at which the interpretation of the input string was not
possible anymore.
-/
structure ParserError where
  message : String
  position : Nat
  input: Option String
deriving Repr, BEq

namespace ParserError

/--
Return a formatted string that contains the error message and position.
-/
def toString (e : ParserError) : String :=
  match e.input with
  | some str => s!"error in position {e.position} of '{str}': {e.message}"
  | none => s!"error in position {e.position}: {e.message}"

instance : ToString ParserError := ⟨toString⟩

instance : Inhabited ParserError := ⟨{message := "unknown error", position := 42, input := none}⟩

end ParserError
end ParserErrors

section ParserResults

/--
A parser result holds either the value of the given type, if parsing was
successful or a parser error in case of failure.
-/
inductive ParserResult (α : Type) where
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α
deriving Repr, BEq

/--
Define a failure with "unknown error" as message an implausible position
as default value for parser result.
-/
instance {α : Type} : Inhabited (ParserResult α) := ⟨.failure default⟩

namespace ParserResult

def isSuccess {α : Type} (res : ParserResult α) : Bool :=
  match res with
  | .success _ => true
  | .failure _ => false

/--
`to?` converts a parser result into an optional value.
-/
def to? {α : Type} (res : ParserResult α) : Option α :=
  match res with
  | .success s => s
  | .failure _ => none

/--
`to!` unwraps the value from a `.success` parser result and
panics if a `.failure` is provided.
-/
def to! {α : Type} [Inhabited α] (res : ParserResult α) : α :=
  match res with
  | .success s => s
  | .failure e => panic s!"no parser result due to {e}"

/--
For convenience, `toIO!` converts the value from a `.success` parser result
into an term of `IO α` and throws an error, if a `.failure` is provided.
-/
def toIO! {α : Type} (res : ParserResult α) : IO α := do
  match res with
  | .success s => return s
  | .failure e => throw (IO.userError e.toString)

end ParserResult
end ParserResults

section NonEmptyLists

/--
Non-empty lists are used to ensure that the list-like identifiers
`dot-separated pre-release identifiers` and `dot-separated build identifiers`
are not empty.
-/
def NonEmptyList (α : Type) : Type := {l: List α // !l.isEmpty}

instance (α : Type) [DecidableEq α] : DecidableEq (NonEmptyList α) :=
  Subtype.instDecidableEq

namespace NonEmptyList

/--
`lt` (less than) is the basis for implementing the precedence of versions as defined under
[item #11 in semver.org](https://semver.org/#spec-item-11).

[`List.lt`](https://lean-lang.org/doc/api/Init/Data/List/Basic.html#List.lt)
can be used directly for implementing the required behavior.
-/
def lt {α: Type} [LT α] (a b : NonEmptyList α) : Prop := a.val.lt b.val

instance (α : Type) [LT α] : LT (NonEmptyList α) := ⟨lt⟩

/--
The following theorem ensures that the canonical injection
```
fun {α : Type} (a : NonEmptyList α) => a.val
```
is strictly monotone under the respective less-then relations.
Based on this, the theorem `List.lt_trans` can be _carried over_ from `List` to
`NonEmptyList`.
-/
theorem inj_mono {α: Type} [LT α] (a b : NonEmptyList α) : a.lt b → a.val.lt b.val := by
  intro h
  unfold lt at h
  exact h

theorem inj_mono' {α: Type} [LT α] (a b : NonEmptyList α) : a < b → a.val < b.val := inj_mono a b

theorem lt_trans {α: Type} [LT α] (a b c: NonEmptyList α) (h1 : a < b) (h2 : b < c) : a < c := by
  sorry

/--
`decLt` is the decidable `<`-relation for non-empty lists.
-/
def decLt {α: Type} [DecidableEq α] [LT α] [DecidableLT α] (a b : NonEmptyList α) :
  Decidable (a < b) := List.decidableLT a.val b.val

instance (α : Type) [DecidableEq α] [LT α] [DecidableLT α] :
  DecidableLT (NonEmptyList α) := decLt

/--
Provide an implementation of `repr` so that `#eval` can be used on non-empty lists.
-/
def repr {α : Type} [Repr α] (a : NonEmptyList α) (n : Nat) : Std.Format := List.repr a.val n

instance (α : Type) [Repr α] : Repr (NonEmptyList α) := ⟨repr⟩

/--
Render a non-empty list as string with its elements separated by ".".

For instance,
```lean
#eval toDotSeparatedString (⟨[0, 1, 2, 3, 4], rfl⟩ : NonEmptyList Nat)
```
results in `"0.1.2.3.4"`.
-/
def toDotSeparatedString {α : Type} [ToString α] (a : NonEmptyList α) : String :=
  String.intercalate "." (a.val.map (fun a => ToString.toString a))

/--
Parse the given string and, if possible, return a result containing
a non-empty list of terms of type α.
-/
def parse {α : Type} (str : String) (parseElement : String → ParserResult α) (sep : Char) :
  ParserResult (NonEmptyList α) :=

  let rec helper (lstr : List String) (parseElement : String → ParserResult α) :
    ParserResult (List α) :=
    match lstr with
    | str::tail =>
      match parseElement str with
      | .success res =>
        match helper tail parseElement with
        | .success lres => .success (res::lres)
        | .failure e =>
          .failure {
            message := e.message,
            position := e.position + str.length + 1, -- 1 for sep
            input := none
          }
      | .failure e => .failure e
    | [] => .success []

  match helper (str.split (· == sep)) parseElement with
  | .success res =>
    if h : !res.isEmpty then
      .success ⟨res, h⟩
    else
      .failure default
  | .failure e =>
    .failure {
      message := e.message,
      position := e.position,
      input := str
    }

end NonEmptyList
end NonEmptyLists

section NonEmptyStrings

/--
Non-empty strings are the _base type_ for the different kinds of identifiers.
They ensure that the requirement "Identifiers MUST NOT be empty." that is stated as
[item #9 in semver.org](https://semver.org/#spec-item-9) is fulfilled.
-/
def NonEmptyString : Type := { s : String // !s.isEmpty }

deriving instance DecidableEq, BEq, ToString, Repr for NonEmptyString

namespace NonEmptyString

/--
`lt` is for comparing two non-empty strings as in
```
#check lt (⟨"abc", rfl⟩ : NonEmptyString) (⟨"bcd", rfl⟩ : NonEmptyString)
```
-/
def lt (a b : NonEmptyString) : Prop := a.val < b.val

instance : LT NonEmptyString := ⟨lt⟩

/--
`decLt` is the decidable `<`-relation for non-empty strings, which
allows for comparing two non-empty strings as in
```
#eval decLt (⟨"abc", rfl⟩ : NonEmptyString) (⟨"bcd", rfl⟩ : NonEmptyString)
```
-/
def decLt (a b : NonEmptyString) : Decidable (a < b) :=
  String.decidableLT a.val b.val

instance decidableLT (a b : NonEmptyString) : Decidable (a < b) := decLt a b

/--
Parse a given string and return a result containing a non-empty string if possible.
-/
def parse (str : String) : ParserResult NonEmptyString :=
  if h: !str.isEmpty then
    .success ⟨str, h⟩
  else
    .failure {
      message := "string must not be empty",
      position := 0,
      input := str
    }

end NonEmptyString
end NonEmptyStrings

section Digits

/--
Return `(true, s.length)` if the given non-empty string `s` only contains digits and
`(false, p)`otherwise, if `s` contains a non-digit character in position `p`.
-/
def NonEmptyString.containsOnlyDigits (s: NonEmptyString) : Bool × Nat :=

  let rec helper : (List Char) → Nat → Bool × Nat
    | chr::tail, pos => if chr.isDigit then helper tail (pos + 1) else (false, pos)
    | _, pos => (true, pos)

  helper s.val.data 0

/--
Digits are non-empty strings that only contain digits as characters as in
```
#eval (⟨⟨ "01234", rfl⟩, rfl⟩ : Digits)
```
-/
def Digits : Type := { s : NonEmptyString // s.containsOnlyDigits.fst = true }

deriving instance DecidableEq, BEq, ToString, Repr for Digits

namespace Digits

/--
Convert string of digits `Nat`.
-/
def toNat (d : Digits) : Nat := d.val.val.toNat!

/--
Less-then for digits, which is based on `Nat` (and not `String`)
as defined in https://semver.org/ under 4.1: Identifiers
consisting of only digits are compared numerically.
-/
def lt (a b : Digits) := a.toNat < b.toNat

instance : LT Digits := ⟨lt⟩

/--
Decidable less-then for digits, which allows for evaluations like
the ones at the end of of this example
```
def nes0 : NonEmptyString := ⟨"01234", rfl⟩
def nes1 : NonEmptyString := ⟨"002234", rfl⟩

#eval nes0 < nes1 -- false
#eval nes1 < nes0 -- true

def d0 : Digits := ⟨nes0, rfl⟩
def d1 : Digits := ⟨nes1, rfl⟩

#eval d0 < d1 -- true
#eval d1 < d0 -- false
```
-/
instance decidableLT (a b : Digits) : Decidable (a < b) :=
  if h: a.toNat < b.toNat then
    have g : lt a b := by unfold lt; exact h
    isTrue g
  else
    have g : ¬ lt a b := by unfold lt; exact h
    isFalse g

/--
Parse the given string and return a `ParserResult` containing
term of type `Digits` if possible.

Example:
```
#eval parse "001234" 0 -- ParserResult.success "001234"
```
-/
def parse (str : String) : ParserResult Digits :=
  match NonEmptyString.parse str with
  | .success b =>
    let c := b.containsOnlyDigits
    match g : c.fst with
    | true => .success ⟨b,g⟩
    | false => .failure {
        message := "digits expected, but non-digit character found",
        position := c.snd,
        input := str
      }
  | .failure e => .failure e

end Digits
end Digits

section NumericIdentifiers

/--
Detect if a given term of type `Digits` has leading zeros.
https://semver.org/ forbids leading zeros for both, numbers
in the version _core_ and numeric identifiers.
-/
def Digits.hasNoLeadingZeros (d: Digits) : Bool × Nat :=
  let helper : (List Char) → Nat → Bool × Nat
  | [], pos => (true, pos)
  | [_], pos => (true, pos)
  | chr::_, pos => (chr != '0', pos)

  helper d.val.val.data 0

/--
Numeric identifiers are sequences of digits without leading
zeros.

Examples: Strings `"1234"` and `"0"` are valid numeric identifiers
while `"01"` is not.
-/
def NumIdent : Type := { d: Digits // d.hasNoLeadingZeros.fst}

deriving instance DecidableEq, BEq, ToString, Repr for NumIdent

namespace NumIdent

/--
Convert a numeric identifier to a natural number.
-/
def toNat (n : NumIdent) : Nat := n.val.toNat

/--
Less-then for numerical identifiers, which is based
on their value as natural number.

TODO: Explain
```
def a : NumIdent := ⟨⟨⟨"13", rfl⟩, rfl⟩, rfl⟩
def b : NumIdent := ⟨⟨⟨"123", rfl⟩, rfl⟩, rfl⟩
#eval a < b
#eval a.val < b.val
#eval b.val.val < a.val.val
```
-/
def lt (a b : NumIdent) : Prop := a.toNat < b.toNat
instance : LT NumIdent := ⟨lt⟩

instance decidableLT (a b : NumIdent) : Decidable (a < b) :=
  Digits.decidableLT a.val b.val



def parse (str : String) : ParserResult NumIdent  :=
  match Digits.parse str with
  | .success dig =>
    let lz := dig.hasNoLeadingZeros
    match g : lz.fst with
    | true => .success ⟨dig,g⟩
    | false => .failure {
        message := "numeric identifiers must not have leading zeros",
        position := lz.snd,
        input := str
      }
  | .failure e => .failure e

end NumIdent
end NumericIdentifiers

section Identifiers

/--
Fundamental base type for the different kinds of identifiers to ensure
"Identifiers MUST comprise only ASCII alphanumerics and hyphens [0-9A-Za-z-]."
(see 9. in https://semver.org/).
-/

def NonEmptyString.isIdent (s: NonEmptyString) : Bool × Nat :=
  let rec helper : (List Char) → Nat → Bool × Nat
  | chr::tail, pos => if chr.isAlphanum || chr = '-' then helper tail (pos + 1) else (false, pos)
  | [], pos => (true, pos)

  helper s.val.data 0

def Ident : Type := { s: NonEmptyString // s.isIdent.fst }

deriving instance DecidableEq, BEq, ToString, Repr for Ident

namespace Ident

def lt (a b : Ident) : Prop := a.val < b.val

instance : LT Ident := ⟨lt⟩

instance decidableLT (a b : Ident) : Decidable (a < b) :=
  NonEmptyString.decLt a.val b.val

def parse (str : String) : ParserResult Ident :=
  match NonEmptyString.parse str  with
  | .failure e => .failure e
  | .success nes =>
    let isi := nes.isIdent
    match g : isi.fst with
    | true => .success ⟨nes, g⟩
    | false => .failure {
        message := "character is not in [0-9A-Za-z-]",
        position := isi.snd,
        input := str
      }

end Ident
end Identifiers

section AlphaNumericIdentifiers

def Ident.hasNonDigit (i: Ident) : Bool × Nat:=
  let rec helper : (List Char) → Nat →  Bool × Nat
    | chr::tail, pos => if chr.isAlpha || chr = '-' then (true, pos) else helper tail (pos + 1)
    | [], pos => (false, pos)
  helper i.val.val.data 0

def AlphanumIdent : Type := { i : Ident // i.hasNonDigit.fst }

instance : DecidableEq AlphanumIdent :=
    Subtype.instDecidableEq

deriving instance BEq, ToString, Repr for AlphanumIdent

namespace AlphanumIdent

def lt (a b : AlphanumIdent) : Prop := a.val < b.val

instance : LT AlphanumIdent := ⟨lt⟩

instance decidableLT (a b : AlphanumIdent) : Decidable (a < b) :=
  Ident.decidableLT a.val b.val

def parse (str : String) : ParserResult AlphanumIdent :=
  match Ident.parse str with
  | .success id =>
    let cnd := id.hasNonDigit
    match g : cnd.fst with
    | true => .success ⟨id,g⟩
    | false => .failure {
        message := "alphanumeric identifier must contain a non-digit character",
        position := cnd.snd,
        input := str
      }
  | .failure e => .failure e

end AlphanumIdent
end AlphaNumericIdentifiers

section BuildIdentifiers

inductive BuildIdent where
  | alphanumIdent (val : AlphanumIdent) : BuildIdent
  | digits (val : Digits) : BuildIdent

deriving instance DecidableEq, BEq, Repr for BuildIdent

namespace BuildIdent

def toString : BuildIdent → String
  | alphanumIdent val => (ToString.toString val)
  | digits val => (ToString.toString val)

instance : ToString BuildIdent := ⟨toString⟩

def parse (str : String) : ParserResult BuildIdent :=
  match AlphanumIdent.parse str with
  | .success ani => .success (alphanumIdent ani)
  | .failure e1 =>
    match Digits.parse str with
    | .success dig => .success (digits dig)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric identifier nor digits found because\n1. {e1.message}\n2. {e2.message}"
        position := Nat.max e1.position e2.position,
        input := str
      }

end BuildIdent

def DotSepBuildIdents : Type := NonEmptyList BuildIdent

deriving instance DecidableEq, BEq, Repr for DotSepBuildIdents
instance : Inhabited DotSepBuildIdents := ⟨[(BuildIdent.digits ⟨⟨"0", rfl⟩, rfl⟩)], rfl⟩

namespace DotSepBuildIdents

def toString : DotSepBuildIdents → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSepBuildIdents := ⟨toString⟩

def parse (str : String) : ParserResult DotSepBuildIdents :=
  NonEmptyList.parse str BuildIdent.parse '.'

end DotSepBuildIdents

end BuildIdentifiers

section PreReleaseIdentifiers

inductive PreRelIdent where
  | alphanumIdent (val : AlphanumIdent) : PreRelIdent
  | numIdent (val : NumIdent) : PreRelIdent

deriving instance DecidableEq, BEq, Repr for PreRelIdent

namespace PreRelIdent

/- numeric identifiers always have lower precedence than alphanumeric identifiers -/
def lt (a b : PreRelIdent) : Prop :=
  match a, b with
  | alphanumIdent _, numIdent _ => False
  | numIdent _, alphanumIdent _ => True
  | alphanumIdent s, alphanumIdent t | numIdent s, numIdent t => s < t

instance : LT PreRelIdent := ⟨lt⟩

def decLt (a b : PreRelIdent) : Decidable (a < b) :=
    match ha: a, hb: b with
  | alphanumIdent s, alphanumIdent t
  | numIdent s, numIdent t =>
      if h: s < t then isTrue h else isFalse h
  | alphanumIdent _, numIdent _ =>
      have h : ¬ a.lt b := by unfold lt; simp [ha, hb]
      isFalse (by rw [ha, hb] at h; exact h)
  | numIdent _, alphanumIdent _ =>
      have h : a.lt b := by unfold lt; simp [ha, hb]
      isTrue (by rw [ha, hb] at h; exact h)

instance : DecidableLT PreRelIdent := decLt

def toString : PreRelIdent → String
  | alphanumIdent val => (ToString.toString val)
  | numIdent val => (ToString.toString val)

instance : ToString PreRelIdent := ⟨toString⟩

def parse (str : String) : ParserResult PreRelIdent  :=
  match AlphanumIdent.parse str  with
  | .success val => .success (alphanumIdent val)
  | .failure e1 =>
    match NumIdent.parse str with
    | .success val => .success (numIdent val)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric nor numeric identifier found because \n1. {e1.message}\n2. {e2.message}"
        position := Nat.max e1.position e2.position
        input := str
      }

end PreRelIdent

def DotSepPreRelIdents : Type := NonEmptyList PreRelIdent

deriving instance DecidableEq, BEq, Repr for DotSepPreRelIdents
instance : Inhabited DotSepPreRelIdents := ⟨[(PreRelIdent.numIdent ⟨⟨⟨"0", rfl⟩, rfl⟩, rfl⟩)], rfl⟩

namespace DotSepPreRelIdents

def repr (a : DotSepPreRelIdents) (n: Nat) : Std.Format :=
  List.repr a.val n

instance : Repr DotSepPreRelIdents := ⟨repr⟩

def lt (a b : DotSepPreRelIdents) : Prop := NonEmptyList.lt a b
instance : LT DotSepPreRelIdents := ⟨lt⟩

def toString : DotSepPreRelIdents → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSepPreRelIdents := ⟨toString⟩

def parse (str : String) : ParserResult DotSepPreRelIdents  :=
  NonEmptyList.parse str PreRelIdent.parse '.'

end DotSepPreRelIdents

end PreReleaseIdentifiers

section VersionCores

structure VersionCore where
  major : Nat := 1
  minor : Nat := 0
  patch : Nat := 0
deriving DecidableEq, BEq, Repr, Inhabited

namespace VersionCore

def toString (a : VersionCore) : String := s!"{a.major}.{a.minor}.{a.patch}"

instance : ToString VersionCore := ⟨toString⟩

def toList (v : VersionCore) : List Nat := [v.major, v.minor, v.patch]

def fromList (l : List Nat) (h : l.length == 3) : VersionCore :=
  match l with
  | [m,n,p] => {major := m, minor := n, patch := p}

def lt (v w : VersionCore) : Prop := v.toList < w.toList

instance : LT VersionCore := ⟨lt⟩

def decLt (v w : VersionCore) : Decidable (v < w) := v.toList.decidableLT w.toList

instance : DecidableLT VersionCore := decLt

def parse (str : String) : ParserResult VersionCore  :=
  match NonEmptyList.parse str NumIdent.parse '.' with
  | .success l =>
      let nums := l.val.map NumIdent.toNat
      if h : nums.length == 3 then
        .success (fromList nums h)
      else
        .failure {
          message := "exactly three numbers - separated by '.' - must be provided, not one more, not one less",
          position := 0,
          input := str
        }
  | .failure e => .failure e

end VersionCore
end VersionCores

section Versions

structure Version extends VersionCore where
  preRelease  : Option DotSepPreRelIdents := none
  build       : Option DotSepBuildIdents := none
deriving DecidableEq, BEq, Repr, Inhabited

namespace Version

def toString (a : Version) : String :=
    match a.preRelease, a.build with
    | none, none => s!"{a.toVersionCore}"
    | some r, none => s!"{a.toVersionCore}-{r}"
    | none, some b => s!"{a.toVersionCore}+{b}"
    | some r, some b => s!"{a.toVersionCore}-{r}+{b}"

instance : ToString Version := ⟨toString⟩

private def ltPreRelease (a b : Version) : Bool :=
  match a.preRelease, b.preRelease with
  | some _, none => true
  | some s, some t => (s.decLt t).decide
  | none, none | none, some _ => false

def lt (v w : Version) : Prop :=
  (v.toVersionCore < w.toVersionCore) ∨
  (v.toVersionCore = w.toVersionCore ∧ (v.ltPreRelease w = true))

instance : LT Version := ⟨lt⟩

def decLt (v w : Version) : Decidable (v < w) :=
  match v.toVersionCore.decLt w.toVersionCore with
  | isTrue h1 =>
    have h2 : v.lt w := by unfold lt; simp [h1]
    isTrue h2
  | isFalse h1 =>
    if h2 : v.toVersionCore = w.toVersionCore then
      if h3: v.ltPreRelease w then
        have h4 : lt v w := by unfold lt; simp [h2, h3]
        isTrue h4
      else
        have h4 : ¬ lt v w := by unfold lt; simp [h1]; simp[h2, h3]
        isFalse h4
    else
       have h3 : ¬ lt v w := by unfold lt; simp [h1, h2]
       isFalse h3

instance : DecidableLT Version := decLt

def parseCorePreRel (str : String) :
  ParserResult (VersionCore × Option DotSepPreRelIdents) :=
  match str.split (· == '-') with
  | [] => panic "internal error - split returns empty list"
  | core_str::tail =>
    let pre_rel_str := String.intercalate "-" tail
    let core_res := VersionCore.parse core_str
    match core_res with
    | .failure e => .failure e
    | .success core =>
      if pre_rel_str.isEmpty then
        .success (core, none)
      else
        match DotSepPreRelIdents.parse pre_rel_str with
        | .success pre_rel => .success (core, pre_rel)
        | .failure e =>
          .failure {
            message := e.message,
            position := e.position + core_str.length + 1
            input := str
          }

def parse (str : String) : ParserResult Version :=
  match str.split (· == '+') with
  | [] => panic "internal error - split returns empty list"
  | [core_pre_rel_str] =>
      match parseCorePreRel core_pre_rel_str  with
      | .failure e => .failure e
      | .success core_pre_rel_res =>
          .success {
            toVersionCore := core_pre_rel_res.fst,
            preRelease := core_pre_rel_res.snd,
            build := none
          }
  | [core_pre_rel_str, build_str] =>
    match parseCorePreRel core_pre_rel_str with
    | .failure e => .failure e
    | .success core_pre_rel_res =>
      match DotSepBuildIdents.parse build_str with
      | .success build_res =>
          .success {
            toVersionCore := core_pre_rel_res.fst,
            preRelease := core_pre_rel_res.snd,
            build := build_res
          }
      | .failure e =>
        .failure {
          message := e.message,
          position := e.position + core_pre_rel_str.length + 1,
          input := str
        }
  | head1::(head2::_) =>
    .failure  {
      message := "versions cannot contain more than one plus-sign",
      position := head1.length + head2.length + 1,
      input := str
    }

def isStable (v: Version) : Bool :=
  match v with
  | { major := 0, minor := _, patch := _, preRelease := _, build := _ }
  | { major := _, minor := _, patch := _, preRelease := some _, build := _ }
      => false
  | _ => true

def nextMajor (v : Version) : Version := {major := v.major + 1}
def nextMinor (v : Version) : Version := {major := v.major, minor := v.minor + 1}
def nextPatch (v : Version) : Version := {major := v.major, minor := v.minor, patch := v.patch + 1}

def subsequentPreRelease? (v : Version) (str : String) : Option Version :=
  match parse s!"{v.toVersionCore}-{str}" with
  | .success w => if v < w then w else none
  | .failure _ => none

def setPreRelease? (v: Version) (str : String) : Option Version :=
  match v with
  | { toVersionCore := c, preRelease := _ , build := _ } =>
    (parse s!"{c}-{str}").to?

def setBuild? (v: Version) (str : String) : Option Version :=
  match v with
  | { toVersionCore := c, preRelease := none, build := _ } =>
    (parse s!"{c}+{str}").to?
  | { toVersionCore := c, preRelease := some p, build := _ } =>
    (parse s!"{c}-{p}+{str}").to?

def isPossibleStart : (Option Char) → Char → Bool
  | none, d => d.isDigit
  | some c, d => (!c.isDigit) && (d.isDigit)

def charIsValid (c : Char ) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '+'

end Version

namespace VersionCore

def addPreRelease? (c : VersionCore) (suffix : String) : Option Version :=
  (Version.parse s!"{c}-{suffix}").to?

end VersionCore

end Versions

section Extraction

def cutOffPrefix (ch : Option Char) (str: String) : String :=

  let rec helper : (Option Char) → (List Char) → (List Char)
    | _, [] => []
    | c, d::t =>
      if (Version.isPossibleStart c) d then
        d::t
      else
        helper d t

  String.mk ((helper ch) str.data)

def extractVersions (str: String) : List Version :=

  let rec helper : List String → List Version
    | [] => []
    | text::tail =>
      let withoutPrefix := cutOffPrefix none text
      match Version.parse withoutPrefix with
      | .success v => v::(helper tail)
      | .failure _ => helper tail

  helper (str.split (!Version.charIsValid ·))

end Extraction
