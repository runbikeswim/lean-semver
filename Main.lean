section ParserErrors

structure ParserError where
  message : String
  position : Nat
deriving Repr

namespace ParserError

def toString (a : ParserError) : String :=
  s!"Error in position {a.position}: {a.message}"

instance : ToString ParserError := ⟨toString⟩

end ParserError

section Examples

def parser_error_0 :=  { message := "example" , position := 42 : ParserError}

end Examples

end ParserErrors

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
  (a : List String) (pos: Nat) (parseElement : String → Nat → α ⊕ ParserError) :
  (List α) ⊕ ParserError :=
  match a with
  | c::t =>
    match parseElement c pos with
    | .inl d =>
      match _parse t (pos + c.length +1) parseElement with
      | .inl s => .inl (d::s)
      | .inr e => .inr e
    | .inr e => .inr e
  | [] => .inl []

protected def parse {α : Type}
  (a : String) (pos: Nat) (parseElement : String → Nat → α ⊕ ParserError) (sep : Char):
  (NonEmptyList α) ⊕ ParserError :=

  match _parse (a.split (· == sep)) pos parseElement with
  | .inl s =>
    if h : !s.isEmpty then
      .inl ⟨s,h⟩
    else .inr {
        message := s!"list of strings separated by '{sep}' must not be empty",
        position := pos
      }
  | .inr e => .inr e

end NonEmptyList

end NonEmptyLists

section NonEmptyStrings
/-!
Base type for the different kinds of identifiers to ensure "Identifiers MUST NOT be empty."
(see 9. in https://semver.org/).
-/

def NonEmptyString : Type := { s: String // !s.isEmpty }

deriving instance DecidableEq for NonEmptyString
deriving instance ToString for NonEmptyString
deriving instance Repr for NonEmptyString

namespace NonEmptyString

def lt (a b : NonEmptyString) : Prop := a.val < b.val

instance : LT NonEmptyString := ⟨lt⟩

instance decidableLT (a b : NonEmptyString) :
  Decidable (a < b) := String.decidableLT a.val b.val

def parse (a : String) (pos : Nat) : NonEmptyString ⊕ ParserError :=
  if h: !a.isEmpty then
    .inl ⟨a, h⟩
  else
    .inr {
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
    | c::t, p => if c.isDigit then helper t (p + 1) else (false, p)
    | _, p => (true, p)
  helper s.val.data 0

def Digits : Type := {s : NonEmptyString // s.containsOnlyDigits.fst = true}

/-
Beware: = and DecidableEq are based on String
but < and decidableLT on Nat - see below
-/
deriving instance DecidableEq for Digits
deriving instance ToString for Digits
deriving instance Repr for Digits

namespace Digits

def toNat (a : Digits) : Nat := a.val.val.toNat!

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

def parse (a : String) (pos : Nat) : Digits ⊕ ParserError :=
  match NonEmptyString.parse a pos with
  | .inl b =>
    let c := b.containsOnlyDigits
    match g : c.fst with
    | true => .inl ⟨b,g⟩
    | false => .inr {
        message := "digits expected, but non-digit character found",
        position := pos + c.snd : ParserError
      }
  | .inr e => .inr e

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

def Digits.hasNoLeadingZeros (s: Digits) : Bool × Nat :=
  let helper : (List Char) → Nat → Bool × Nat
  | [], p => (true, p)
  | [_], p => (true, p)
  | c::_, p => (c != '0', p)

  helper s.val.val.data 0

def NumericIdentifier : Type := { d: Digits // d.hasNoLeadingZeros.fst}

deriving instance DecidableEq for NumericIdentifier
deriving instance ToString for NumericIdentifier
deriving instance Repr for NumericIdentifier

namespace NumericIdentifier

def toNat (a : NumericIdentifier) : Nat := a.val.toNat

def lt (a b : NumericIdentifier) : Prop := a.toNat < b.toNat

instance : LT NumericIdentifier := ⟨lt⟩

instance decidableLT (a b : NumericIdentifier) : Decidable (a < b) :=
  Digits.decidableLT a.val b.val

def parse (a : String) (pos : Nat) : NumericIdentifier ⊕ ParserError :=
  match Digits.parse a pos with
  | .inl b =>
    let c := b.hasNoLeadingZeros
    match g : c.fst with
    | true => .inl ⟨b,g⟩
    | false => .inr {
        message := "numeric identifiers must not have leading zeros",
        position := pos + c.snd : ParserError
      }
  | .inr e => .inr e

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
  | c::t, p => if c.isAlphanum || c = '-' then helper t (p + 1) else (false, p)
  | [], p => (true, p)

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

def parse (a : String) (pos : Nat) : Identifier ⊕ ParserError :=
  match NonEmptyString.parse a pos with
  | .inl b =>
    let c := b.isIdentifier
    match g : c.fst with
    | true => .inl ⟨b, g⟩
    | false => .inr {
        message := "character is not in [0-9A-Za-z-]",
        position := pos + c.snd : ParserError
      }
  | .inr e => .inr e

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
    | c::t, p => if c.isAlpha || c = '-' then (true, p) else helper t (p + 1)
    | [], p => (false, p)
  helper i.val.val.data 0

def AlphanumericIdentifier : Type := {i : Identifier // i.containsNonDigit.fst}

namespace AlphanumericIdentifier

deriving instance ToString for AlphanumericIdentifier
deriving instance Repr for AlphanumericIdentifier

instance : DecidableEq AlphanumericIdentifier :=
    Subtype.instDecidableEq

def lt (a b : AlphanumericIdentifier) : Prop := a.val < b.val

instance : LT AlphanumericIdentifier := ⟨lt⟩

instance decidableLT (a b : AlphanumericIdentifier) : Decidable (a < b) :=
  Identifier.decidableLT a.val b.val

def parse (a : String) (pos : Nat) : AlphanumericIdentifier ⊕ ParserError :=
  match Identifier.parse a pos with
  | .inl b =>
    let c := b.containsNonDigit
    match g : c.fst with
    | true => .inl ⟨b,g⟩
    | false => .inr {
        message := "alphanumeric identifier must contain a non-digit character",
        position := pos + c.snd
      }
  | .inr e => .inr e

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

def parse (a : String) (pos : Nat) : BuildIdentifier ⊕ ParserError :=
  match AlphanumericIdentifier.parse a pos with
  | .inl ba => .inl (.inl ba)
  | .inr ea =>
    match Digits.parse a pos with
    | .inl bd => .inl (.inr bd)
    | .inr ed => .inr {
        message := "neither alphanumeric identifier nor digits found"
        position := Nat.max ea.position ed.position
      }

end BuildIdentifier

def DotSeparatedBuildIdentifiers : Type := NonEmptyList BuildIdentifier

deriving instance Repr for DotSeparatedBuildIdentifiers

namespace DotSeparatedBuildIdentifiers

def toString : DotSeparatedBuildIdentifiers → String := NonEmptyList.toDotSeparatedString

instance : ToString DotSeparatedBuildIdentifiers := ⟨toString⟩

def parse (a : String) (pos : Nat) : DotSeparatedBuildIdentifiers ⊕ ParserError :=
  NonEmptyList.parse a pos BuildIdentifier.parse '.'

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

def parse (a : String) (pos : Nat) : PreReleaseIdentifier ⊕ ParserError :=
  match AlphanumericIdentifier.parse a pos with
  | .inl ba => .inl (.inl ba)
  | .inr ea =>
    match NumericIdentifier.parse a pos with
    | .inl bd => .inl (.inr bd)
    | .inr ed => .inr {
        message := "neither alphanumeric nor numeric identifier found"
        position := Nat.max ea.position ed.position
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

def parse (a : String) (pos : Nat) : DotSeparatedPreReleaseIdentifiers ⊕ ParserError :=
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

def parse (a : String) (pos : Nat) : VersionCore ⊕ ParserError :=

  let rec helper : (List String) → Nat → (List Nat) ⊕ ParserError
    | [], _ => .inl []
    | c::t, p =>
      match c.toNat? with
      | some d =>
        match helper t (p + c.length + 1) with
        | .inl s => .inl (d::s)
        | .inr e => .inr e
      | none =>
        .inr {
          message := "must be natural number",
          position := p
        }

  match helper (a.split (· == '.')) pos with
  | .inl b =>
    if h : b.length = 3 then
      .inl (fromList b h)
    else
      .inr {
        message := "exactly three numbers - separated by '.' - must be provided - not one more, not one less",
        position := pos
      }
  | .inr e => .inr e

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

private def _parseTail (a : String) (pos : Nat) (sep : Char) :
  (Option DotSeparatedPreReleaseIdentifiers × Option DotSeparatedBuildIdentifiers) ⊕ ParserError :=
  match a with
  | "" => .inl (none, none)
  | b =>
    match sep with
    | '+' =>
      match DotSeparatedBuildIdentifiers.parse a pos with
      | .inl bs => .inl (none, some bs)
      | .inr e => .inr e
    | '-' =>
      match b.split (· == '+') with
      | ps::t =>
        match DotSeparatedPreReleaseIdentifiers.parse ps pos with
        | .inl pps =>
          match t with
          | [bs] =>
            match DotSeparatedBuildIdentifiers.parse bs (pos + 1 + ps.length) with
            | .inl pbs => .inl (some pps, some pbs)
            | .inr e => .inr e
          | [] => .inl (some pps, none)
          | _ => .inr {
                    message := "versions cannot contain more than one plus-sign",
                    position := pos + 1 + ps.length
                  }
        | .inr e => .inr e
      | [] => .inr {
                message := "internal error - split returns empty list",
                position := 0
              }
    | x => .inr {
                message := s!"internal error - separator '{x}' found, where '+' or '-' are expected",
                position := 0
            }

def parse (a : String) : Version ⊕ ParserError :=
  match a.split (fun c : Char => c == '-' || c == '+') with
  | c::_ =>
    match VersionCore.parse c 0 with
    | .inl d =>
        let pos := c.length + 1
        match _parseTail (a.extract ⟨pos⟩ ⟨a.length + 1⟩) (pos) (a.get ⟨c.length⟩) with
        | .inl (p, b) => .inl {
                              major := d.major, minor := d.minor, patch := d.patch,
                              preRelease := p, build := b
                          }
        | .inr e => .inr e
    | .inr e => .inr e
  | [] => .inr {
      message := "internal error - split returns empty list",
      position := 0
    }

def doParserResult (p : Version ⊕ ParserError) : IO Version := do
  match p with
  | .inl v => return v
  | .inr e => throw (IO.userError e.toString)

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
    IO.print "please enter the first version number --> "
    let version_0 ← getVersion

    IO.print "please enter the second version number -> "
    let version_1 ← getVersion

    IO.println "the internal representation of the first version number is:"
    IO.println ((repr version_0).pretty 80 0)

    IO.println "the internal representation of the second version number is:"
    IO.println ((repr version_1).pretty 80 0)

    IO.println "for the precedence of the first and second value, the following is true:"
    if version_0 < version_1 then
      IO.println s!"    {version_0} < {version_1}"
    else
      IO.println s!"  ¬ {version_0} < {version_1}"

  catch e =>
    IO.println e
