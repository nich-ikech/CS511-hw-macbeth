import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/-
# Important tactics and lemmas:

# Tactics
mod_cases
interval_cases
numbers (to reach a contradiction)
contradiction

# Lemmas
Int.ModEq.add
Int.ModEq.sub
Int.ModEq.neg
Int.ModEq.mul
Int.ModEq.pow
Int.ModEq.refl
Int.ModEq.symm
Int.ModEq.trans
Nat.pos_of_dvd_of_pos
eq_or_lt_of_le
Nat.le_of_dvd
Nat.not_dvd_of_exists_lt_and_lt
Int.even_iff_modEq
Int.odd_iff_modEq
Int.even_or_odd
prime_test
 -/

example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases  hx : x % 3
  calc
    x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 0 := by ring
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 1 ^ 3 [ZMOD3 ] := by rel [hx]
    _ = 1 := by ring
    _ ≡ x [ZMOD 3] := by rel [hx]
  calc
    x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel [hx]
    _ = 2 + 3 * 2 := by ring
    _ ≡ 2 [ZMOD 3] := by extra
    _ ≡ x [ZMOD 3] := by rel [hx]

example : Prime 5 := by
  apply prime_test
  · numbers
  · intros m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 2
      constructor <;> numbers
    . use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intros h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc
      0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h
  · intros h
    obtain h1 | h2 := Int.even_or_odd n
    · exact h1
    · contradiction


theorem no_int_even_and_odd : ¬∃x, Int.Even x ∧ Int.Odd x := by
  intros h
  obtain ⟨x,hEven, hOdd⟩ := h
  rw [Int.even_iff_modEq] at hEven
  rw [Int.odd_iff_modEq] at hOdd
  apply Int.ModEq.symm  at hEven
  have contra : 0 ≡ 1 [ZMOD 2] := by apply Int.ModEq.trans hEven hOdd
  numbers at contra


example : ¬ Int.Even 7 := by
  intros hEven
  have hOdd : Int.Odd 7 := by
    rw [Int.odd_iff_modEq]
    use 3
    ring
  apply no_int_even_and_odd
  use 7
  constructor
  · apply hEven
  · apply hOdd
