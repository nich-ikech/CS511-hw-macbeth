import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # CS 511 Lab 2
# September 11, 2024 -/

/- # Potential problems to solve together in lab.  Solve as many as you like. -/

/- # Exercises 1.3.1 through 1.3.6 -/

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by sorry

example {a b : ℤ} (h : a - b = 0) : a = b := by sorry

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by sorry

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by sorry

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by sorry

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by sorry

/- # Examples from Section 1.4 -/

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  sorry

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by sorry
    _ ≤ A * B + A * B + A * v := by sorry
    _ ≤ A * B + A * B + 1 * v := by sorry
    _ ≤ A * B + A * B + B * v := by sorry
    _ < A * B + A * B + B * A := by sorry
    _ = 3 * A * B := by sorry

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by sorry
    _ ≥ 10 * t - 3 * t - 17 := by sorry
    _ = 7 * t - 17 := by sorry
    _ ≥ 7 * 10 - 17 := by sorry
    _ ≥ 5 := by sorry

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  sorry

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]

-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by sorry
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ < 3 := by sorry

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by sorry
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by sorry
    _ ≤ 2 * (8 * b) + 8 * a + a := by sorry
    _ = 7 * b + 9 * (a + b) := by sorry
    _ ≤ 7 * b + 9 * 8 := by sorry
    _ = 7 * b + 72 := by sorry

/- # Work through first Lean 4 exercise together? -/

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by sorry
