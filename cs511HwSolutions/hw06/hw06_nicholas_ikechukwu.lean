import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib

math2001_init
--# Exercise 3.4.5.6

@[autograded 3]
theorem exercise_3a (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  rel [Int.ModEq.refl]

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  have h : x ^ 5 - x = x * (x ^ 4 - 1) := by ring
  have h' : x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) := by ring
  have h'' : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [h, h', h'']
  apply Int.ModEq.mul_right
  apply Int.ModEq.mul
  · apply Int.modEq_zero_fac
  · apply Int.modEq_zero_fac

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  have h : (n - 2) * (n - 3) ≡ 0 [ZMOD 5] := by
    calc (n - 2) * (n - 3)
      ≡ n ^ 2 - 5 * n + 6 [ZMOD 5] := by rel [Int.ModEq.refl]
      ≡ 4 - 0 + 1 [ZMOD 5] := by rel [hn, Int.ModEq.refl]
      ≡ 0 [ZMOD 5] := by rel [Int.ModEq.refl]
  obtain ⟨k, hk⟩ := h
  have : n - 2 ≡ 0 [ZMOD 5] ∨ n - 3 ≡ 0 [ZMOD 5] := by
    apply Int.ModEq.mul_eq_zero hk
  cases this with
  | inl h => right; rel [h]
  | inr h => left; rel [h]

--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intros m hm1 hm2
    interval_cases m
    all_goals numbers

--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h_even : Int.Even (n ^ 2) := by
    use 1
    rw [hn]
    ring
  have h_odd : Int.Odd n ∨ Int.Even n := Int.odd_or_even n
  cases h_odd with
  | inl h_odd => exact no_int_even_and_odd ⟨n ^ 2, h_even, Int.odd_sq h_odd⟩
  | inr h_even => exact no_int_even_and_odd ⟨2, by { rw [← hn]; exact Int.even_sq h_even }, by use 1; ring⟩

--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2; exact no_int_even_and_odd ⟨n, h2, h1⟩
  · intro h
    cases Int.even_or_odd n with
    | inl h1 => contradiction
    | inr h2 => exact h2

--# Example 4.5.6

@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  have : n ^ 2 ≡ n [ZMOD 3] := by
    calc n ^ 2 ≡ n * n [ZMOD 3] := by rel [Int.ModEq.refl]
               ≡ n [ZMOD 3] := by apply Int.ModEq.mul_right; apply Int.modEq_add_fac_self_symm''
  have : n ≡ 2 [ZMOD 3] := by
    calc n ≡ n ^ 2 [ZMOD 3] := by rel [this.symm]
           ≡ 2 [ZMOD 3] := by rel [h]
  have : 2 ≡ 2 ^ 2 [ZMOD 3] := by
    calc 2 ≡ n [ZMOD 3] := by rel [this.symm]
           ≡ n ^ 2 [ZMOD 3] := by rel [this]
           ≡ 2 [ZMOD 3] := by rel [h]
  numbers at this
