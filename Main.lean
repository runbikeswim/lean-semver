section ParserErrors

structure ParserError where
  message : String
  position : Nat
deriving Repr

namespace ParserError

def toString (e : ParserError) : String :=
  s!"Error in position {e.position}: {e.message}"

instance : ToString ParserError := ⟨toString⟩

end ParserError

end ParserErrors

section ParserResults

inductive ParserResult (α : Type)
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α

end ParserResults

section NonEmptyLists
/-!
for all rules of type
```
  <items> ::= <item>
            | <item> <separator> <items>
```
for non-empty lists of items
-/

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

private def _parse {α : Type}
  (lstr : List String) (pos: Nat) (parseElement : String → Nat → ParserResult α) :
  ParserResult (List α) :=
  match lstr with
  | chr::tail =>
    match parseElement chr pos with
    | .success res =>
      match _parse tail (pos + chr.length +1) parseElement with
      | .success lres => .success (res::lres)
      | .failure e => .failure e
    | .failure e => .failure e
  | [] => .success []

def parse {α : Type}
  (str : String) (pos: Nat) (parseElement : String → Nat →  ParserResult α) (sep : Char) :
  ParserResult (NonEmptyList α) :=

  match _parse (str.split (· == sep)) pos parseElement with
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
/-!
```
<digits> ::= <digit>
           | <digit> <digits>
```
i.e. arbitrary sequences of digits
-/

def NonEmptyString.containsOnlyDigits (s: NonEmptyString) : Bool × Nat:=
  let rec helper : (List Char) → Nat → Bool × Nat
    | chr::tail, pos => if chr.isDigit then helper tail (pos + 1) else (false, pos)
    | _, pos => (true, pos)
  helper s.val.data 0

def Digits : Type := { s : NonEmptyString // s.containsOnlyDigits.fst = true }

/-
Beware: = and DecidableEq are based on String
but < and decidableLT on Nat - see below
-/
deriving instance DecidableEq for Digits
deriving instance ToString for Digits
deriving instance Repr for Digits

namespace Digits

def toNat (d : Digits) : Nat := d.val.val.toNat!

-- compare as numbers
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
/-!
```
<numeric identifier> ::= "0"
                       | <positive digit>
                       | <positive digit> <digits>
```
i.e. digits without leading zeros
-/

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
  | .success nes =>
    let isi := nes.isIdentifier
    match g : isi.fst with
    | true => .success ⟨nes, g⟩
    | false => .failure {
        message := "character is not in [0-9A-Za-z-]",
        position := pos + isi.snd : ParserError
      }
  | .failure e => .failure e

end Identifier

end Identifiers

section AlphaNumericIdentifiers
/-!
```
<alphanumeric identifier> ::= <non-digit>
                            | <non-digit> <identifier characters>
                            | <identifier characters> <non-digit>
                            | <identifier characters> <non-digit> <identifier characters>

<non-digit> ::= <letter>
              | "-"

<identifier characters> ::= <identifier character>
                          | <identifier character> <identifier characters>

<identifier character> ::= <digit>
                         | <non-digit>
```
i.e. any identifier that contains at list one non-digit
(upper/lower-case ASCII-letter or hyphen)
-/

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
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β] : Type := α ⊕ β

instance {α β : Type}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [Repr α] [Repr β]
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
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]:
  DecidableEq (DecOrderedSum α β) := decEq

def lt {α β : Type}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]
  (a b : DecOrderedSum α β) : Prop :=
  match a, b with
  | .inl s, .inl t
  | .inr s, .inr t => s < t
  | .inl _, .inr _ => False -- ¬ α < β
  | .inr _, .inl _ => True -- β < α

instance (α β : Type)
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]:
  LT (DecOrderedSum α β) := ⟨lt⟩

def decLt {α β : Type}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]
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
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β] :
  DecidableLT (DecOrderedSum α β) := decLt

def toString {α β : Type}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β]
  (a : DecOrderedSum α β) : String :=
  match a with
  | .inl s | .inr s => ToString.toString s

instance (α β : Type)
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [DecidableLT α] [DecidableLT β]
  [ToString α] [ToString β] :
  ToString (DecOrderedSum α β) := ⟨toString⟩

end DecOrderedSum

end DecOrderedSums

section BuildIdentifiers
/-!
```
<build identifier> ::= <alphanumeric identifier>
                     | <digits>
```
-/

-- Numeric identifiers always have lower precedence than non-numeric identifiers
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
        message := "neither alphanumeric identifier nor digits found"
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
/-!
```
<pre-release identifier> ::= <alphanumeric identifier>
                           | <numeric identifier>
```
-/

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
        message := "neither alphanumeric nor numeric identifier found"
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

def parse (str : String) (pos : Nat) : ParserResult VersionCore  :=
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

  match helper (str.split (· == '.')) pos with
  | .success vcr =>
    if h : vcr.length = 3 then
      .success (fromList vcr h)
    else
      .failure {
        message := "exactly three numbers - separated by '.' - must be provided, not one more, not one less",
        position := pos
      }
  | .failure e => .failure e

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
  | some s, some t => (s.decLt t).decide
  | some _, none => true
  | none, none
  | none, some _ => false

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

private def _parseTail (str : String) (pos : Nat) (sep : Char) :
  ParserResult (Option DotSeparatedPreReleaseIdentifiers × Option DotSeparatedBuildIdentifiers) :=
  match str with
  | "" => .success (none, none)
  | ne_str =>
    match sep with
    | '+' =>
      match DotSeparatedBuildIdentifiers.parse str pos with
      | .success build => .success (none, some build)
      | .failure e => .failure e
    | '-' =>
      match ne_str.split (· == '+') with
      | pre_rel_str::tail =>
        match DotSeparatedPreReleaseIdentifiers.parse pre_rel_str pos with
        | .success pre_rel =>
          match tail with
          | [build_str] =>
            match DotSeparatedBuildIdentifiers.parse build_str (pos + 1 + pre_rel_str.length) with
            | .success build => .success (some pre_rel, some build)
            | .failure e => .failure e
          | [] => .success (some pre_rel, none)
          | _ => .failure {
                    message := "versions cannot contain more than one plus-sign",
                    position := pos + 1 + pre_rel_str.length
                  }
        | .failure e => .failure e
      | [] => .failure {
                message := "internal error - split returns empty list",
                position := 0
              }
    | x => .failure {
                message := s!"internal error - separator '{x}' found, where '+' or '-' are expected",
                position := 0
            }

def parse (a : String) : ParserResult Version :=
  match a.split (fun c : Char => c == '-' || c == '+') with
  | core_str::_ =>
    match VersionCore.parse core_str 0 with
    | .success core =>
        let pos := core_str.length + 1
        match _parseTail (a.extract ⟨pos⟩ ⟨a.length + 1⟩) (pos) (a.get ⟨core_str.length⟩) with
        | .success (pre_rel, build) =>
            .success {
              major := core.major, minor := core.minor, patch := core.patch,
              preRelease := pre_rel, build := build
            }
        | .failure e => .failure e
    | .failure e => .failure e
  | [] => .failure {
      message := "internal error - split returns empty list",
      position := 0
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
  let trimmed := input.trim

  if trimmed == "" then
    throw (IO.userError "no data entered")

  let version ← doParserResult (parse trimmed)

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
