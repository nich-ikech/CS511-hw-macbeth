import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

-- /-2 points-/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  · calc
      x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [h1]
      _ = 0 := by ring
  · calc
      x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [h2]
      _ = 0 := by ring

-- /-2 points-/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  · calc
      t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h1]
      _ = 0 := by ring
  · calc
      t ^ 2 - t - 6 = 3 ^ 2 - 3 - 6 := by rw [h2]
      _ = 0 := by ring

-- /-2 points-/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  · calc
      x * y + 2 * x = 2 * y + 2 * 2 := by rw [hx]
      _ = 2 * y + 4 := by ring
  · calc
      x * y + 2 * x = x * (-2) + 2 * x := by rw [hy]
      _ = -2 * x + 2 * x := by ring
      _ = 0 := by ring
      _ = 2 * (-2) + 4 := by ring
      _ = 2 * y + 4 := by rw [hy]





-- # Exercise 4
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
sorry

/-2 points-/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + (a + b) := by rel [h1]
    _ ≤ 1 + 3 := by rel [h2]
    _ = 4 := by ring

/-2 points-/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hy : y = 2 := by
    calc
      y = (x + 2 * y) - (x + y) := by ring
      _ = 7 - 5 := by rw [h2, h1]
      _ = 2 := by ring
  have hx : x = 3 := by
    calc
      x = (x + y) - y := by ring
      _ = 5 - 2 := by rw [h1, hy]
      _ = 3 := by ring
  constructor
  · exact hx
  · exact hy

-- # Problem 2


theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : t ^ 2 * (t - 1) = 0 := by
    calc
      t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
      _ = t ^ 2 - t ^ 2 := by rw [ht]
      _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3 | h4 := h2
  · right
    exact sq_eq_zero_iff.mp h3
  · left
    exact h4

theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  intro h
  have h1 : (m + 2) ^ 2 = 50 := by
    calc
      (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
      _ = 46 + 4 := by rw [h]
      _ = 50 := by ring
  have h2 : m + 2 = 5 ∨ m + 2 = -5 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [h1]
    ring
  obtain h3 | h4 := h2
  · have h5 : m = 3 := by addarith [h3]
    have h6 : 3 ^ 2 + 4 * 3 = 21 := by ring
    have h7 : 21 = 46 := by
      calc
        21 = 3 ^ 2 + 4 * 3 := by ring
        _ = m ^ 2 + 4 * m := by rw [h5]
        _ = 46 := by rw [h]
    numbers at h7
  · have h5 : m = -7 := by addarith [h4]
    have h6 : m ≥ 0 := by extra
    contradiction

theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : a = b := by
    calc
      a = a * b := by rw [h1]
      _ = b := by rw [h2]
  have h4 : a * a = a := by
    calc
      a * a = a * b := by rw [h3]
      _ = a := by rw [h1]
  have h5 : a * (a - 1) = 0 := by
    calc
      a * (a - 1) = a * a - a := by ring
      _ = a - a := by rw [h4]
      _ = 0 := by ring
  have h6 := eq_zero_or_eq_zero_of_mul_eq_zero h5
  obtain h7 | h8 := h6
  · left
    constructor
    · exact h7
    · rw [← h3, h7]
  · right
    constructor
    · exact h8
    · rw [← h3, h8]
