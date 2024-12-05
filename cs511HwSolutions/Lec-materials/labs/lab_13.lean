import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust
import Mathlib.Tactic.GCongr

math2001_init

open Set Function Nat

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  sorry

namespace Nat
theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  sorry
end Nat

example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · right; left; apply h
    · right; right; apply h
  · intro h
    obtain h | h | h := h
    · left; left; apply h
    · left; right; apply h
    · right; right; apply h

example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  sorry

example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  sorry

example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  sorry

namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  sorry
end Int

example (x : ℤ) : x ∉ ∅ := by
  sorry

example (U : Set ℤ) : ∅ ⊆ U := by
  sorry

example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  sorry

example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  sorry
