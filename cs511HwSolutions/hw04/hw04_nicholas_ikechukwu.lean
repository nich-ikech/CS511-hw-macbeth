import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

--Example 2.5.5
@[autograded 2]
theorem exercise3a : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  ring

--Example 2.5.6
@[autograded 2]
theorem exercise3b (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

--Example 2.5.7
@[autograded 2]
theorem exercise3c {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · linarith
  · linarith








--Exercise 3.1.10.3
@[autograded 2]
theorem exercise4a {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even] at *
  obtain ⟨k, hk⟩ := hm
  obtain ⟨l, hl⟩ := hn
  use k + l
  ring


--Exercise 4.1.10.1
@[autograded 2]
theorem exercise4b {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  have h1 := h 2
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by rel [h1]
    _ = 1 := by ring

--Example 4.1.3
@[autograded 2]
theorem exercise4c {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  by_contra h1
  push_neg at h1
  have h2 := h ((a + b) / 2)
  obtain h3 | h4 := h2
  · linarith
  · linarith

--Exercise 3.2.9.2
@[autograded 2]
theorem problem2a : ¬(3 : ℤ) ∣ -10 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have h1 : 3 ∣ 9 := by use 3; ring
  have h2 : 3 ∣ 9 + (-10) := by
    apply Int.dvd_add h1 h
  have h3 : 3 ∣ -1 := by
    convert h2
    ring
  have h4 : 3 ≤ |-1| := Int.le_abs_self 3
  have h5 : |-1| = 1 := by norm_num
  linarith

--Exercise 3.2.9.5
@[autograded 2]
theorem problem2b {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use 2 * k ^ 3 - k ^ 2 + 3 * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hk]
    _ = a * (2 * k ^ 3 - k ^ 2 + 3 * k) := by ring

--Exercise 3.2.9.6
@[autograded 2]
theorem problem2c {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x ^ 3 * y
  calc
    m = l ^ 3 * y := by rw [hy]
    _ = (k * x) ^ 3 * y := by rw [hx]
    _ = k ^ 3 * (x ^ 3 * y) := by ring
