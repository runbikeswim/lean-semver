/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SemVer.Basic

section NonEmptyLists
namespace NonEmptyList

/--
Ensures that the _canonical injection_
```
fun {α} a ↦ a.val : {α : Type} → NonEmptyList α → List α
```
is strictly increasing under the respective `<`-relations.
-/
@[simp]
theorem inj_incr {α: Type} [LT α] (a b : NonEmptyList α) : a < b ↔ a.val < b.val := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Asserts that `<` is a transitive relation in`NonEmptyList α` if the
underlying `<` on `α` has the same property.
-/
@[simp]
theorem lt_trans {α: Type} [LT α]
  [g : Trans (· < · : α → α → Prop) (· < ·) (· < ·)]
  {a b c: NonEmptyList α} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [inj_incr]
  rw [inj_incr] at h1 h2
  apply List.lt_trans h1 h2

instance {α: Type} [LT α] [Trans (· < · : α → α → Prop) (· < ·) (· < ·)] :
  Trans (· < · : NonEmptyList α → NonEmptyList α → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end NonEmptyList
end NonEmptyLists

section NonEmptyStrings
namespace NonEmptyString

/--
Assert that the _canonical injection_
```
fun a ↦ a.val : NonEmptyString → String
```
is a strictly increasing function under the respective `<`-relations.
-/
@[simp]
theorem inj_incr (a b : NonEmptyString) : a < b ↔ a.val < b.val := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
Asserts that `<` is transitive on `NonEmptyString`.
-/
@[simp]
theorem lt_trans {a b c: NonEmptyString} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [inj_incr]
  rw [inj_incr] at h1 h2
  exact String.lt_trans h1 h2

instance : Trans (· < · : NonEmptyString → NonEmptyString → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end NonEmptyString
end NonEmptyStrings

section Digits

namespace Digits
/--
Asserts that `<` is transitive on `Digits`.
-/
@[simp]
theorem lt_trans {a b c: Digits} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2

instance : Trans (· < · : Digits → Digits → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end Digits
end Digits

section NumericIdentifiers
namespace NumIdent

/--
Ensures that `<` is transitive on `NumIdent`.
-/
@[simp]
theorem lt_trans {a b c: NumIdent} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2

instance : Trans (· < · : NumIdent → NumIdent → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end NumIdent
end NumericIdentifiers

section Identifiers
namespace Ident

/--
Ensures that `<` is transitive on `Ident`.
-/
@[simp]
theorem lt_trans {a b c: Ident} (h1 : a < b) (h2 : b < c) : a < c := NonEmptyString.lt_trans h1 h2

instance : Trans (· < · : Ident → Ident → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end Ident
end Identifiers

section AlphaNumericIdentifiers
namespace AlphanumIdent

/--
Ensures that `<` is transitive on `AlphanumIdent`.
-/
@[simp]
theorem lt_trans {a b c: AlphanumIdent} (h1 : a < b) (h2 : b < c) : a < c := NonEmptyString.lt_trans h1 h2

instance : Trans (· < · : AlphanumIdent → AlphanumIdent → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end AlphanumIdent
end AlphaNumericIdentifiers

section PreReleaseIdentifiers
namespace PreRelIdent

/--
Ensures that `<` is transitive on `PreRelIdent`.
-/
@[simp]
theorem lt_trans {a b c: PreRelIdent} (h1 : a < b) (h2 : b < c) : a < c := by
  match ga: a with
  | alphanumIdent va =>
      match gb: b with
      | alphanumIdent vb =>
        match gc: c with
        | alphanumIdent vc => exact AlphanumIdent.lt_trans h1 h2
        | numIdent vc => contradiction
      | numIdent vb => contradiction
  | numIdent va =>
    match gb: b with
    | alphanumIdent vb =>
      match gc: c with
      | alphanumIdent vc => assumption
      | numIdent vc => contradiction
    | numIdent vb =>
      match gc: c with
      | alphanumIdent vc => assumption
      | numIdent vc => exact NumIdent.lt_trans h1 h2

instance : Trans (· < · : PreRelIdent → PreRelIdent → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end PreRelIdent

namespace DotSepPreRelIdents

/--
Ensures that `<` is transitive on `DotSepPreRelIdents`.
-/
@[simp]
theorem lt_trans {a b c: DotSepPreRelIdents} (h1 : a < b) (h2 : b < c) : a < c := NonEmptyList.lt_trans h1 h2

instance : Trans (· < · : DotSepPreRelIdents → DotSepPreRelIdents → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end DotSepPreRelIdents
end PreReleaseIdentifiers

section VersionCores
namespace VersionCore

/--
Ensures that `<` is transitive on `VersionCore`.
-/
@[simp]
theorem lt_trans {a b c: VersionCore} (h1 : a < b) (h2 : b < c) : a < c := List.lt_trans h1 h2

instance : Trans (· < · : VersionCore → VersionCore → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end VersionCore
end VersionCores

section Versions
namespace Version

/--
Lemma asserting that `Version.ltPreRelease` is transitive.
-/
@[simp]
theorem ltPreRelease_trans {a b c : Version} (h1: a.ltPreRelease b) (h2 : b.ltPreRelease c) :
  (a.ltPreRelease c) := by
  unfold ltPreRelease
  unfold ltPreRelease at h1 h2
  cases ha: a.preRelease with
  | none =>
    cases hb: b.preRelease with
    | none =>
      cases hc: c.preRelease with
      | none => simp [ha, hb] at h1
      | some _ => simp [ha, hb] at h1
    | some _ =>
      cases hc: c.preRelease with
      | none => simp [ha, hb] at h1
      | some _ => simp [ha, hb] at h1
  | some ap =>
    cases hb: b.preRelease with
    | none =>
      cases hc: c.preRelease with
      | none => simp [hb, hc] at h2
      | some _ => simp [hb, hc] at h2
    | some bp =>
      cases hc: c.preRelease with
      | none => simp
      | some cp =>
        simp
        simp [ha, hb] at h1
        simp [hb, hc] at h2
        exact DotSepPreRelIdents.lt_trans h1 h2

/--
Ensures that `<` is transitive on `Version`.
-/
@[simp]
theorem lt_trans {a b c: Version} (h1 : a < b) (h2 : b < c) : a < c := by
  cases h1 with
  | inl h1l =>
    cases h2 with
    | inl h2l =>
      have g: a.toVersionCore < c.toVersionCore := VersionCore.lt_trans h1l h2l
      exact Or.inl g
    | inr h2r =>
      have ⟨h2rl,h2rr⟩ := h2r
      have g: a.toVersionCore < c.toVersionCore := by rw [← h2rl]; exact h1l
      exact Or.inl g
  | inr h1r =>
    cases h2 with
    | inl h2l =>
      have ⟨h1rl,h1rr⟩ := h1r
      have g: a.toVersionCore < c.toVersionCore := by rw [h1rl]; exact h2l
      exact Or.inl g
    | inr h2r =>
      right
      have ⟨h1rl,h1rr⟩ := h1r
      have ⟨h2rl,h2rr⟩ := h2r
      have g : a.toVersionCore = c.toVersionCore := by rw [h1rl]; exact h2rl
      have i : a.ltPreRelease c := ltPreRelease_trans h1rr h2rr
      exact And.intro g i

instance : Trans (· < · : Version → Version → Prop) (· < ·) (· < ·) where
  trans a b := lt_trans a b

end Version
