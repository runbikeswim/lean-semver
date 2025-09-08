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

inductive ParserResult (α : Type)
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α

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

def NumericIdentifier : Type := { d: Digits // d.hasNoLeadingZeros.fst}

deriving instance DecidableEq for NumericIdentifier
deriving instance ToString for NumericIdentifier
deriving instance Repr for NumericIdentifier

namespace NumericIdentifier

def toNat (n : NumericIdentifier) : Nat := n.val.toNat

def lt (a b : NumericIdentifier) : Prop := a.toNat < b.toNat

instance : LT NumericIdentifier := ⟨lt⟩

instance decidableLT (a b : NumericIdentifier) : Decidable (a < b) :=
  Digits.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult NumericIdentifier  :=
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

end NumericIdentifier
end NumericIdentifiers

section Identifiers
/-!
Fundamental base type for the different kinds of identifiers to ensure
"Identifiers MUST comprise only ASCII alphanumerics and hyphens [0-9A-Za-z-]."
(see 9. in https://semver.org/).
-/

def NonEmptyString.isIdentifier (s: NonEmptyString) : Bool × Nat :=
  let rec helper : (List Char) → Nat → Bool × Nat
  | chr::tail, pos => if chr.isAlphanum || chr = '-' then helper tail (pos + 1) else (false, pos)
  | [], pos => (true, pos)

  helper s.val.data 0

def Identifier : Type := { s: NonEmptyString // s.isIdentifier.fst }

deriving instance DecidableEq for Identifier
deriving instance ToString for Identifier
deriving instance Repr for Identifier

namespace Identifier

def lt (a b : Identifier) : Prop := a.val < b.val

instance : LT Identifier := ⟨lt⟩

instance decidableLT (a b : Identifier) : Decidable (a < b) :=
  NonEmptyString.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult Identifier :=
  match NonEmptyString.parse str pos with
  | .failure e => .failure e
  | .success nes =>
    let isi := nes.isIdentifier
    match g : isi.fst with
    | true => .success ⟨nes, g⟩
    | false => .failure {
        message := "character is not in [0-9A-Za-z-]",
        position := pos + isi.snd : ParserError
      }

end Identifier
end Identifiers

section AlphaNumericIdentifiers

def Identifier.containsNonDigit (i: Identifier) : Bool × Nat:=
  let rec helper : (List Char) → Nat →  Bool × Nat
    | chr::tail, pos => if chr.isAlpha || chr = '-' then (true, pos) else helper tail (pos + 1)
    | [], pos => (false, pos)
  helper i.val.val.data 0

def AlphanumericIdentifier : Type := { i : Identifier // i.containsNonDigit.fst }

namespace AlphanumericIdentifier

deriving instance ToString for AlphanumericIdentifier
deriving instance Repr for AlphanumericIdentifier

instance : DecidableEq AlphanumericIdentifier :=
    Subtype.instDecidableEq

def lt (a b : AlphanumericIdentifier) : Prop := a.val < b.val

instance : LT AlphanumericIdentifier := ⟨lt⟩

instance decidableLT (a b : AlphanumericIdentifier) : Decidable (a < b) :=
  Identifier.decidableLT a.val b.val

def parse (str : String) (pos : Nat) : ParserResult AlphanumericIdentifier :=
  match Identifier.parse str pos with
  | .success id =>
    let cnd := id.containsNonDigit
    match g : cnd.fst with
    | true => .success ⟨id,g⟩
    | false => .failure {
        message := "alphanumeric identifier must contain a non-digit character",
        position := pos + cnd.snd
      }
  | .failure e => .failure e

end AlphanumericIdentifier
end AlphaNumericIdentifiers

section DecOrderedSums

def DecOrderedSum (α β : Type)
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β] :
  Type := α ⊕ β

instance {α β : Type}
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [Repr α] [Repr β]
  [ToString α] [ToString β] :
  Repr (DecOrderedSum α β) where reprPrec :=
    fun (a : DecOrderedSum α β) (n : Nat) => (a : Sum α β).repr n

namespace DecOrderedSum

theorem inl_eq (α β : Type) (s t : α) :
  (.inl s : α ⊕ β) = (.inl t : α ⊕ β) ↔ s = t := by
  constructor <;> simp

theorem inr_eq (α β : Type) (s t : β) :
  (.inr s : α ⊕ β) = (.inr t : α ⊕ β) ↔ s = t := by
  constructor <;> simp

def decEq {α β : Type}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]
  (a b : DecOrderedSum α β) : Decidable (a = b) :=
  match ha: a, hb: b with
  | .inl s, .inl t =>
    if h: s = t then
      isTrue (by rw [h])
    else
      isFalse (by rw [inl_eq]; exact h)
  | .inr s, .inr t =>
    if h: s = t then
      isTrue (by rw [h])
    else
      isFalse (by rw [inr_eq]; exact h)
  | .inl s, .inr t
  | .inr s, .inl t => isFalse (by simp)

instance {α β : Type}
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β]:
  DecidableEq (DecOrderedSum α β) := decEq

def lt {α β : Type}
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β]
  (a b : DecOrderedSum α β) : Prop :=
  match a, b with
  | .inl s, .inl t
  | .inr s, .inr t => s < t
  | .inl _, .inr _ => False -- ¬ α < β
  | .inr _, .inl _ => True -- β < α

instance (α β : Type)
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β]:
  LT (DecOrderedSum α β) := ⟨lt⟩

def decLt {α β : Type}
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β]
  (a b : DecOrderedSum α β) : Decidable (a < b) :=
  match ha: a, hb: b with
  | .inl s, .inl t
  | .inr s, .inr t => if h: s < t then isTrue h else isFalse h
  | .inr s, .inl t =>
      have g: lt (Sum.inr s) (Sum.inl t) := by unfold lt; simp
      isTrue g
  | .inl s, .inr t =>
      have g: ¬ lt (Sum.inl s) (Sum.inr t) := by unfold lt; simp
      isFalse g

instance (α β : Type)
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β] :
  DecidableLT (DecOrderedSum α β) := decLt

def toString {α β : Type}
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β]
  (a : DecOrderedSum α β) : String :=
  match a with
  | .inl s | .inr s => ToString.toString s

instance (α β : Type)
  [DecidableEq α] [DecidableEq β] [LT α] [LT β]
  [DecidableLT α] [DecidableLT β] [ToString α] [ToString β] :
  ToString (DecOrderedSum α β) := ⟨toString⟩

end DecOrderedSum

end DecOrderedSums

section BuildIdentifiers

/- Numeric identifiers always have lower precedence than non-numeric identifiers -/
def BuildIdentifier : Type := DecOrderedSum AlphanumericIdentifier Digits

deriving instance Repr for BuildIdentifier
deriving instance DecidableEq for BuildIdentifier
deriving instance LT for BuildIdentifier

namespace BuildIdentifier

def lt (a b : BuildIdentifier) : Prop := DecOrderedSum.lt a b

instance : LT BuildIdentifier := ⟨lt⟩

def decLt (a b : BuildIdentifier) : Decidable (a < b) := DecOrderedSum.decLt a b

instance : DecidableLT BuildIdentifier := decLt

def toString (a : BuildIdentifier) := DecOrderedSum.toString a
instance : ToString BuildIdentifier := ⟨toString⟩

def parse (str : String) (pos : Nat) : ParserResult BuildIdentifier :=
  match AlphanumericIdentifier.parse str pos with
  | .success ani => .success (.inl ani)
  | .failure e1 =>
    match Digits.parse str pos with
    | .success dig => .success (.inr dig)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric identifier nor digits found because\n1. {e1.message} in position {e1.position}\n2. {e2.message} in position {e2.position}"
        position := Nat.max e1.position e2.position
      }

end BuildIdentifier

def DotSeparatedBuildIdentifiers : Type := NonEmptyList BuildIdentifier

deriving instance Repr for DotSeparatedBuildIdentifiers

namespace DotSeparatedBuildIdentifiers

def toString : DotSeparatedBuildIdentifiers → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSeparatedBuildIdentifiers := ⟨toString⟩

def parse (str : String) (pos : Nat) : ParserResult DotSeparatedBuildIdentifiers :=
  NonEmptyList.parse str pos BuildIdentifier.parse '.'

end DotSeparatedBuildIdentifiers

end BuildIdentifiers

section PreReleaseIdentifiers

def PreReleaseIdentifier : Type := DecOrderedSum AlphanumericIdentifier NumericIdentifier

deriving instance Repr for PreReleaseIdentifier
deriving instance DecidableEq for PreReleaseIdentifier
deriving instance LT for PreReleaseIdentifier

namespace PreReleaseIdentifier

def decLt (a b : PreReleaseIdentifier) := DecOrderedSum.decLt a b
instance : DecidableLT PreReleaseIdentifier := decLt

def toString (a : PreReleaseIdentifier) := DecOrderedSum.toString a
instance : ToString PreReleaseIdentifier := ⟨toString⟩

def parse (str : String) (pos : Nat) : ParserResult PreReleaseIdentifier  :=
  match AlphanumericIdentifier.parse str pos with
  | .success ani => .success (.inl ani)
  | .failure e1 =>
    match NumericIdentifier.parse str pos with
    | .success ni => .success (.inr ni)
    | .failure e2 => .failure {
        message := s!"neither alphanumeric nor numeric identifier found because \n1. {e1.message} in position {e1.position}\n2. {e2.message} in position {e2.position}"
        position := Nat.max e1.position e2.position
      }

end PreReleaseIdentifier

def DotSeparatedPreReleaseIdentifiers : Type := NonEmptyList PreReleaseIdentifier

namespace DotSeparatedPreReleaseIdentifiers

def repr (a : DotSeparatedPreReleaseIdentifiers) (n: Nat) : Std.Format :=
  List.repr a.val n

instance : Repr DotSeparatedPreReleaseIdentifiers := ⟨repr⟩

def lt (a b : DotSeparatedPreReleaseIdentifiers) : Prop := NonEmptyList.lt a b
instance : LT DotSeparatedPreReleaseIdentifiers := ⟨lt⟩

def toString : DotSeparatedPreReleaseIdentifiers → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSeparatedPreReleaseIdentifiers := ⟨toString⟩

def parse (a : String) (pos : Nat) : ParserResult DotSeparatedPreReleaseIdentifiers  :=
  NonEmptyList.parse a pos PreReleaseIdentifier.parse '.'

end DotSeparatedPreReleaseIdentifiers

end PreReleaseIdentifiers

section VersionCores

structure VersionCore where
  major : Nat
  minor : Nat
  patch : Nat
deriving DecidableEq, Repr

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
  preRelease  : Option DotSeparatedPreReleaseIdentifiers
  build       : Option DotSeparatedBuildIdentifiers
deriving Repr

instance : Inhabited Version :=
  ⟨{major := 1, minor := 0, patch := 0, preRelease := none, build := none}⟩

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
  ParserResult (VersionCore × Option DotSeparatedPreReleaseIdentifiers) :=
  match str.split (· == '-') with
  | [] => .failure {
            message := "internal error - split returns empty list",
            position := 0
          }
  | core_str::tail =>
    let pre_rel_str := String.intercalate "-" tail
    let core_res := VersionCore.parse core_str
    match core_res with
    | .failure e => .failure e
    | .success core =>
      if pre_rel_str == "" then
        .success (core, none)
      else
        match DotSeparatedPreReleaseIdentifiers.parse pre_rel_str (core_str.length + 1) with
        | .success pre_rel => .success (core, some pre_rel)
        | .failure e => .failure e

def parse (str : String) : ParserResult Version :=
  match str.split (· == '+') with
  | [] => .failure {
            message := "internal error - split returns empty list",
            position := 0
          }
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
      match DotSeparatedBuildIdentifiers.parse build_str (core_pre_rel_str.length + 1) with
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

end Version
end Versions

open Version

def getVersion : IO Version := do

  let input ← (← IO.getStdin).getLine
  let version ← doParserResult (parse input.trim)
  return version

def main : IO Unit := do

  try
    IO.print "please enter the first version identifier --> "
    let version_0 ← getVersion

    IO.print "please enter the second version identifier -> "
    let version_1 ← getVersion

    IO.println "the internal representation of the first version identifier is:"
    IO.println ((repr version_0).pretty 80 0)

    IO.println "the internal representation of the second version identifier is:"
    IO.println ((repr version_1).pretty 80 0)

    IO.println "for the precedence of the first and second version, the following is true:"
    if version_0 < version_1 then
      IO.println s!"    {version_0} < {version_1}"
    else
      IO.println s!"  ¬ {version_0} < {version_1}"

  catch e =>
    IO.println e
