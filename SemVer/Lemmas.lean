/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SemVer.Basic

/-
def a : Digits := ⟨⟨"02", rfl⟩, rfl⟩
def b : Digits := ⟨⟨"1", rfl⟩, rfl⟩

#eval a.val < b.val
#eval b < a

theorem inj_not_incr : ∃ a b : Digits, a.val < b.val ∧ b < a := by
  let a : Digits := ⟨⟨"02", rfl⟩, rfl⟩
  let b : Digits := ⟨⟨"1", rfl⟩, rfl⟩
  have h1 : a.val < b.val := by simp [a,b]; decide
  have na : 2 = a.toNat := by simp [a]; unfold toNat; simp; sorry
  sorry
-/

/-
TODO: Remove if not needed
-/
namespace Char

def parseForNatBase10 : Char → ParserResult Nat
  | '0' => .success 0
  | '1' => .success 1
  | '2' => .success 2
  | '3' => .success 3
  | '4' => .success 4
  | '5' => .success 5
  | '6' => .success 6
  | '7' => .success 7
  | '8' => .success 8
  | '9' => .success 9
  |  c  => .failure {message := s!"{c} is no digit", position := 0}

def isDigitBase10 (chr : Char) : Bool := chr.parseForNatBase10.isSuccess

def decIsDigitBase10 (chr : Char) : Decidable (chr.isDigitBase10) :=
  if h: chr.parseForNatBase10.isSuccess then
    isTrue (by simp [isDigitBase10, h])
  else
    isFalse (by simp [isDigitBase10, h])

end Char

/-
TODO: Remove if not needed
-/
namespace String

def parseForNatBase10 (str : String) : ParserResult Nat :=

  let rec listToNatBase10Helper : (List Char) → Nat → Nat → ParserResult Nat
  | [], acc, _ => .success acc
  | c::cs, acc, pos =>
    match c.parseForNatBase10 with
    | .success n => listToNatBase10Helper cs (acc * 10 + n) (pos + 1)
    | .failure e => .failure {message := e.message, position := e.position}

  match str with
  | "" =>
    .failure {
      message := "input must not be empty"
      position := 0,
      input := str
    }
  | s  =>
    match listToNatBase10Helper s.data 0 0 with
    | .success n => .success n
    | .failure e => .failure {message := e.message, position := e.position, input := str}

def hasOnlyDigitsBase10 (str : String) : Bool := str.parseForNatBase10.isSuccess

theorem lemma_parse_for_nat_base10 {str : String} :
  str.hasOnlyDigitsBase10 → str.parseForNatBase10.isSuccess := by
  intro h
  unfold hasOnlyDigitsBase10 at h
  exact h

def parseForNatBase10Guarded (str : String) (g : str.hasOnlyDigitsBase10): Nat :=
  match h: str.parseForNatBase10 with
  | .success n => n
  | .failure _ => by
      have i : str.parseForNatBase10.isSuccess := by apply lemma_parse_for_nat_base10 g
      simp [ParserResult.isSuccess] at i
      grind only

end String
