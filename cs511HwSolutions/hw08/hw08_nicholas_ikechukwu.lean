import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true




-- # Exercise 3 (first part)

--Slides 18, Page 25

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  intros x y
  obtain ⟨a, ha⟩ := h
  have h1 := ha x
  have h2 := ha y
  apply Eq.trans
  · exact h1.symm
  · exact h2




--Slides 29 Part III, Page 8

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intros h v w
  obtain ⟨x, hx⟩ := h
  have h1 := hx v
  have h2 := hx w
  apply Eq.trans
  · exact h1.symm
  · exact h2


--# Exercise 4




--Exercise 5.3.6.9

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_contra h2
  push_neg at h2
  obtain ⟨h3, h4⟩ := h2
  have : 5 ≤ 4 := by
    calc
      5 ≤ t := h4
      _ ≤ 4 := h3
  have : 4 < 4 := by
    calc
      4 < 5 := by numbers
      _ ≤ 4 := this
  numbers at this



--Example 6.1.2

example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · left
    use 0
    ring
  · obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw [hx]
      ring
    · left
      use x + 1
      rw [hx]
      ring





--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + (2 * 4) := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra



--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use (2 * a ^ 2)
  calc
    2 * a ^ 3 < 2 * a ^ 3 + 7 := by extra
    _ = (2 * a ^ 2) * a + 7 := by ring



--Exercise 6.1.7.2 (Bernoulli's inequality)
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · -- base case
    calc
      (1 + a) ^ 0 = 1 := by ring
      _ = 1 + 0 * a := by ring
  · -- inductive step
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + a + k * a + k * a ^ 2 := by ring
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra


--Exercise 6.1.7.3
example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    ring
  · -- inductive step
    obtain IH | IH := IH
    · right
      obtain ⟨m, hm⟩ := IH
      use 5 * m
      have hk : 5 ^ k = 8 * m + 1:= by addarith [hm]
      calc
        5 ^ (k + 1) - 5 = 5 * (5 ^ k) - 5 := by ring
        _ = 5 * (8 * m + 1) - 5 := by rw [hk]
        _ = 8 * (5 * m) := by ring
    · left
      obtain ⟨m, hm⟩ := IH
      use 5 * m + 3
      have hk : 5 ^ k = 8 * m + 5:= by addarith [hm]
      calc
        5 ^ (k + 1) - 1 = 5 * 5 ^ k - 1 := by ring
        _ = 5 * (8 * m + 5) - 1 := by rw [hk]
        _ = 8 * (5 * m + 3) := by ring
