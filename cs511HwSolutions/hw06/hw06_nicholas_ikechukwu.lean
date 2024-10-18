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
  calc
    5 * n ^ 2 + 3 * n + 7 ≡ n ^ 2 + n + 1 [ZMOD 2] := by rel [Int.ModEq.mul_left, Int.ModEq.add_left]
    _ ≡ 1 [ZMOD 2] := by rel [Int.ModEq.add_sq_self_add_one]

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  apply Int.ModEq.pow_five_eq

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  have h : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] ∨ n ≡ -2 [ZMOD 5] := Int.ModEq.sqrt_four hn
  cases h with
  | inl h1 => left; exact h1
  | inr h2 =>
    cases h2 with
    | inl h3 => right; exact h3
    | inr h4 => left; rw [Int.ModEq.neg_two_eq_three]; exact h4

--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intros m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor
    · exact hm1
    · calc
        7 < m * 2 := by rel [hm1, hm2]
        _ ≤ m * m := by gcongr; rel [hm1]

--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  rcases h with ⟨n, hn⟩
  have h_even : Even (n ^ 2) := by
    use 1
    rw [hn]
    ring
  have h_odd_or_even : Odd n ∨ Even n := Int.odd_or_even n
  cases h_odd_or_even with
  | inl h_odd =>
    have h_odd_sq : Odd (n ^ 2) := Odd.pow h_odd 2
    apply Int.no_even_and_odd (n ^ 2)
    constructor
    · exact h_even
    · exact h_odd_sq
  | inr h_even =>
    have h_even_sq : Even (n ^ 2) := Even.pow h_even 2
    have h : (n ^ 2) / 2 = 1 := by
      rw [hn]
      norm_num
    have h_contra : ¬(Even 1) := by
      intro h_even_1
      have h_odd_1 : Odd 1 := by use 0; ring
      apply Int.no_even_and_odd 1
      constructor
      · exact h_even_1
      · exact h_odd_1
    apply h_contra
    rw [← h]
    exact Even.div_two h_even_sq

--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    apply Int.no_even_and_odd n
    constructor
    · exact h2
    · exact h1
  · intro h
    cases Int.even_or_odd n with
    | inl h_even => contradiction
    | inr h_odd => exact h_odd

--# Example 4.5.6

@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h :=
    calc (1:ℤ) = 2 ^ 2 [ZMOD 3] := by norm_num
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
