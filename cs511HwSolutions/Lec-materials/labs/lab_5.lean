import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--Exists examples
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  sorry

--For All example
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

--Needs real numbers, but automatically gives integers
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  sorry

--Divisibility examples
example : (11 : ℕ) ∣ 88 := by
  sorry


example : (-2 : ℤ) ∣ 6 := by
  sorry

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  sorry
