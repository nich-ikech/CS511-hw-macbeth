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
  sorry

example : Prime 5 := by
  sorry

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  sorry

theorem no_int_even_and_odd : ¬∃x, Int.Even x ∧ Int.Odd x := by
  sorry

example : ¬ Int.Even 7 := by
  sorry
