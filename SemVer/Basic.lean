/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
section ParserErrors

structure ParserError where
  message : String
  position : Nat
deriving Repr

namespace ParserError

def toString (e : ParserError) : String :=
  s!"error in position {e.position}: {e.message}"

instance : ToString ParserError := ⟨toString⟩

end ParserError
end ParserErrors

section ParserResults

inductive ParserResult (α : Type) where
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α

instance {α : Type} : Inhabited (ParserResult α) :=
  ⟨.failure {message := "unknown error", position := 2 ^ 16}⟩

end ParserResults

section NonEmptyLists

def NonEmptyList (α : Type) : Type := {l: List α // !l.isEmpty}

instance (α : Type) [DecidableEq α] : DecidableEq (NonEmptyList α) :=
  Subtype.instDecidableEq

namespace NonEmptyList

/-
List.lt (https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.lt)
provides the implementation the is required to fulfill https://semver.org/#spec-item-11
-/
def lt {α: Type} [LT α] (a b : NonEmptyList α) : Prop := a.val < b.val

instance (α : Type) [LT α] : LT (NonEmptyList α) := ⟨lt⟩

def decLt {α: Type} [DecidableEq α] [LT α] [DecidableLT α] (a b : NonEmptyList α) :
  Decidable (a < b) := List.decidableLT a.val b.val

instance (α : Type) [DecidableEq α] [LT α] [DecidableLT α] :
  DecidableLT (NonEmptyList α) := decLt

def repr {α : Type} [Repr α] (a : NonEmptyList α) (n : Nat) : Std.Format := List.repr a.val n

instance (α : Type) [Repr α] : Repr (NonEmptyList α) := ⟨repr⟩

def toDotSeparatedString {α : Type} [ToString α] (a : NonEmptyList α) : String :=
  String.intercalate "." (a.val.map (fun a => ToString.toString a))

def parse {α : Type} (str : String) (pos: Nat) (parseElement : String → Nat →  ParserResult α) (sep : Char) :
  ParserResult (NonEmptyList α) :=

  let rec helper (lstr : List String) (pos: Nat) (parseElement : String → Nat → ParserResult α) :
    ParserResult (List α) :=
    match lstr with
    | chr::tail =>
      match parseElement chr pos with
      | .success res =>
        match helper tail (pos + chr.length +1) parseElement with
        | .success lres => .success (res::lres)
        | .failure e => .failure e
      | .failure e => .failure e
    | [] => .success []

  match helper (str.split (· == sep)) pos parseElement with
  | .success res =>
    if h : !res.isEmpty then
      .success ⟨res, h⟩
    else .failure {
            message := s!"list of strings separated by '{sep}' must not be empty",
            position := pos
          }
  | .failure e => .failure e

end NonEmptyList
end NonEmptyLists

section NonEmptyStrings
/-!
Base type for the different kinds of identifiers to ensure "Identifiers MUST NOT be empty."
(see 9. in https://semver.org/).
-/

def NonEmptyString : Type := { s : String // !s.isEmpty }

deriving instance DecidableEq for NonEmptyString
deriving instance ToString for NonEmptyString
deriving instance Repr for NonEmptyString

namespace NonEmptyString

def lt (a b : NonEmptyString) : Prop := a.val < b.val

instance : LT NonEmptyString := ⟨lt⟩

instance decidableLT (a b : NonEmptyString) :
  Decidable (a < b) := String.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult NonEmptyString :=
  if h: !str.isEmpty then
    .success ⟨str, h⟩
  else
    .failure {
      message := "string must not be empty",
      position := pos : ParserError
    }

end NonEmptyString
end NonEmptyStrings

section Digits

def NonEmptyString.containsOnlyDigits (s: NonEmptyString) : Bool × Nat:=
  let rec helper : (List Char) → Nat → Bool × Nat
    | chr::tail, pos => if chr.isDigit then helper tail (pos + 1) else (false, pos)
    | _, pos => (true, pos)

  helper s.val.data 0

def Digits : Type := { s : NonEmptyString // s.containsOnlyDigits.fst = true }

/-
Beware: = and DecidableEq are based on String
but < and decidableLT on Nat - see lt below
-/
deriving instance DecidableEq for Digits
deriving instance ToString for Digits
deriving instance Repr for Digits

namespace Digits

def toNat (d : Digits) : Nat := d.val.val.toNat!

/- compare as numbers -/
def lt (a b : Digits) : Prop := a.toNat < b.toNat

instance : LT Digits := ⟨lt⟩

instance decidableLT (a b : Digits) : Decidable (a < b) :=
  if h: a.toNat < b.toNat then
    have g : lt a b := by unfold lt; exact h
    isTrue g
  else
    have g : ¬ lt a b := by unfold lt; exact h
    isFalse g

def parse (str : String) (pos : Nat) : ParserResult Digits :=
  match NonEmptyString.parse str pos with
  | .success b =>
    let c := b.containsOnlyDigits
    match g : c.fst with
    | true => .success ⟨b,g⟩
    | false => .failure {
        message := "digits expected, but non-digit character found",
        position := pos + c.snd : ParserError
      }
  | .failure e => .failure e

end Digits
end Digits

section NumericIdentifiers

def Digits.hasNoLeadingZeros (d: Digits) : Bool × Nat :=
  let helper : (List Char) → Nat → Bool × Nat
  | [], pos => (true, pos)
  | [_], pos => (true, pos)
  | chr::_, pos => (chr != '0', pos)

  helper d.val.val.data 0

def NumIdent : Type := { d: Digits // d.hasNoLeadingZeros.fst}

deriving instance DecidableEq for NumIdent
deriving instance ToString for NumIdent
deriving instance Repr for NumIdent

namespace NumIdent

def toNat (n : NumIdent) : Nat := n.val.toNat

def lt (a b : NumIdent) : Prop := a.toNat < b.toNat

instance : LT NumIdent := ⟨lt⟩

instance decidableLT (a b : NumIdent) : Decidable (a < b) :=
  Digits.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult NumIdent  :=
  match Digits.parse str pos with
  | .success dig =>
    let lz := dig.hasNoLeadingZeros
    match g : lz.fst with
    | true => .success ⟨dig,g⟩
    | false => .failure {
        message := "numeric identifiers must not have leading zeros",
        position := pos + lz.snd : ParserError
      }
  | .failure e => .failure e

end NumIdent
end NumericIdentifiers

section Identifiers
/-!
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

deriving instance DecidableEq for Ident
deriving instance ToString for Ident
deriving instance Repr for Ident

namespace Ident

def lt (a b : Ident) : Prop := a.val < b.val

instance : LT Ident := ⟨lt⟩

instance decidableLT (a b : Ident) : Decidable (a < b) :=
  NonEmptyString.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult Ident :=
  match NonEmptyString.parse str pos with
  | .failure e => .failure e
  | .success nes =>
    let isi := nes.isIdent
    match g : isi.fst with
    | true => .success ⟨nes, g⟩
    | false => .failure {
        message := "character is not in [0-9A-Za-z-]",
        position := pos + isi.snd : ParserError
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

deriving instance ToString for AlphanumIdent
deriving instance Repr for AlphanumIdent

instance : DecidableEq AlphanumIdent :=
    Subtype.instDecidableEq

namespace AlphanumIdent

def lt (a b : AlphanumIdent) : Prop := a.val < b.val

instance : LT AlphanumIdent := ⟨lt⟩

instance decidableLT (a b : AlphanumIdent) : Decidable (a < b) :=
  Ident.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult AlphanumIdent :=
  match Ident.parse str pos with
  | .success id =>
    let cnd := id.hasNonDigit
    match g : cnd.fst with
    | true => .success ⟨id,g⟩
    | false => .failure {
        message := "alphanumeric identifier must contain a non-digit character",
        position := pos + cnd.snd
      }
  | .failure e => .failure e

end AlphanumIdent
end AlphaNumericIdentifiers

section BuildIdentifiers

inductive BuildIdent where
  | alphanumIdent (val : AlphanumIdent) : BuildIdent
  | digits (val : Digits) : BuildIdent

deriving instance Repr for BuildIdent
deriving instance DecidableEq for BuildIdent

namespace BuildIdent

def toString : BuildIdent → String
  | alphanumIdent val => (ToString.toString val)
  | .digits val => (ToString.toString val)

instance : ToString BuildIdent := ⟨toString⟩

def parse (str : String) (pos : Nat) : ParserResult BuildIdent :=
  match AlphanumIdent.parse str pos with
  | .success ani => .success (alphanumIdent ani)
  | .failure e1 =>
    match Digits.parse str pos with
    | .success dig => .success (.digits dig)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric identifier nor digits found because\n1. {e1.message} in position {e1.position}\n2. {e2.message} in position {e2.position}"
        position := Nat.max e1.position e2.position
      }

end BuildIdent

def DotSepBuildIdents : Type := NonEmptyList BuildIdent

deriving instance Repr for DotSepBuildIdents

namespace DotSepBuildIdents

def toString : DotSepBuildIdents → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSepBuildIdents := ⟨toString⟩

def parse (str : String) (pos : Nat) : ParserResult DotSepBuildIdents :=
  NonEmptyList.parse str pos BuildIdent.parse '.'

end DotSepBuildIdents

end BuildIdentifiers

section PreReleaseIdentifiers

inductive PreRelIdent where
  | alphanumIdent (val : AlphanumIdent) : PreRelIdent
  | numIdent (val : NumIdent) : PreRelIdent

deriving instance Repr for PreRelIdent
deriving instance DecidableEq for PreRelIdent

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
      if h: s < t then isTrue  h else isFalse h
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

def parse (str : String) (pos : Nat) : ParserResult PreRelIdent  :=
  match AlphanumIdent.parse str pos with
  | .success val => .success (alphanumIdent val)
  | .failure e1 =>
    match NumIdent.parse str pos with
    | .success val => .success (numIdent val)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric nor numeric identifier found because \n1. {e1.message} in position {e1.position}\n2. {e2.message} in position {e2.position}"
        position := Nat.max e1.position e2.position
      }

end PreRelIdent

def DotSepPreRelIdents : Type := NonEmptyList PreRelIdent

namespace DotSepPreRelIdents

def repr (a : DotSepPreRelIdents) (n: Nat) : Std.Format :=
  List.repr a.val n

instance : Repr DotSepPreRelIdents := ⟨repr⟩

def lt (a b : DotSepPreRelIdents) : Prop := NonEmptyList.lt a b
instance : LT DotSepPreRelIdents := ⟨lt⟩

def toString : DotSepPreRelIdents → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSepPreRelIdents := ⟨toString⟩

def parse (a : String) (pos : Nat) : ParserResult DotSepPreRelIdents  :=
  NonEmptyList.parse a pos PreRelIdent.parse '.'

end DotSepPreRelIdents

end PreReleaseIdentifiers

section VersionCores

structure VersionCore where
  major : Nat := 1
  minor : Nat := 0
  patch : Nat := 0
deriving DecidableEq, Repr, Inhabited

namespace VersionCore

def toString (a : VersionCore) : String := s!"{a.major}.{a.minor}.{a.patch}"

instance : ToString VersionCore := ⟨toString⟩

def toList (v : VersionCore) : List Nat := [v.major, v.minor, v.patch]

def fromList (l : List Nat) (h : l.length = 3) : VersionCore :=
  match l with
  | [m,n,p] => {major := m, minor := n, patch := p}

def lt (v w : VersionCore) : Prop := v.toList < w.toList

instance : LT VersionCore := ⟨lt⟩

def decLt (v w : VersionCore) : Decidable (v < w) := v.toList.decidableLT w.toList

instance : DecidableLT VersionCore := decLt

def parse (str : String) : ParserResult VersionCore  :=

  let rec helper : (List String) → Nat → ParserResult (List Nat)
    | [], _ => .success []
    | chr::tail, pos =>
      match chr.toNat? with
      | some num =>
        match helper tail (pos + chr.length + 1) with
        | .success lnum => .success (num::lnum)
        | .failure e => .failure e
      | none =>
        .failure {
          message := "must be natural number",
          position := pos
        }

  match helper (str.split (· == '.')) 0 with
  | .failure e => .failure e
  | .success vcr =>
    if h : vcr.length = 3 then
      .success (fromList vcr h)
    else
      .failure {
        message := "exactly three numbers - separated by '.' - must be provided, not one more, not one less",
        position := 0
      }

end VersionCore
end VersionCores

section Versions

structure Version extends VersionCore where
  preRelease  : Option DotSepPreRelIdents := none
  build       : Option DotSepBuildIdents := none
deriving Repr, Inhabited

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
      if pre_rel_str == "" then
        .success (core, none)
      else
        match DotSepPreRelIdents.parse pre_rel_str (core_str.length + 1) with
        | .success pre_rel => .success (core, some pre_rel)
        | .failure e => .failure e

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
      match DotSepBuildIdents.parse build_str (core_pre_rel_str.length + 1) with
      | .failure e => .failure e
      | .success build_res =>
          .success {
            toVersionCore := core_pre_rel_res.fst,
            preRelease := core_pre_rel_res.snd,
            build := some build_res
          }
  | head::_ => .failure  {
                    message := "versions cannot contain more than one plus-sign",
                    position := head.length + 1
                  }

def doParserResult (res : ParserResult Version) : IO Version := do
  match res with
  | .success version => return version
  | .failure e => throw (IO.userError e.toString)

def isStable (v: Version) : Bool :=
  match v with
  | { major := 0, minor := _, patch := _, preRelease := _, build := _ }
  | { major := _, minor := _, patch := _, preRelease := some _, build := _ }
      => false
  | _ => true

end Version
end Versions
