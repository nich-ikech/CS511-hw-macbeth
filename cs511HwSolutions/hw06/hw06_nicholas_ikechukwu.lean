import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib

math2001_init

--# Exercise 3.4.5.6

@[autograded 3]
theorem exercise_3a (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡  1 [ZMOD 2] := by
  calc
    5 * n ^ 2 + 3 * n + 7 ≡ n ^ 2 + n + 1 [ZMOD 2] := by rel []
    _ = n * (n + 1) + 1 := by ring
    _ ≡ 0 + 1 [ZMOD 2] := by rel [Int.modEq_zero_fac']
    _ = 1 := by ring

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡  x [ZMOD 5] := by
  mod_cases hx : x % 5
  all_goals
    calc
      x ^ 5 ≡ (x % 5) ^ 5 [ZMOD 5] := by rel [hx]
      _ = x % 5 := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases hn' : n % 5
  · have h := calc
      0 ≡ n [ZMOD 5] := by rel [hn']
      _ ^ 2 ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h
  · have h := calc
      1 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [hn']
      _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h
  · right
    exact hn'
  · left
    exact hn'
  · have h := calc
      4 ^ 2 ≡ n ^ 2 [ZMOD 5] := by rel [hn']
      _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at h

--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intros m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    all_goals
      use 1
      constructor <;> numbers

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
  | inl h_odd =>
    have h_odd_sq : Int.Odd (n ^ 2) := by
      apply Int.odd_sq
      exact h_odd
    apply no_int_even_and_odd
    use n ^ 2
    constructor
    · exact h_even
    · exact h_odd_sq
  | inr h_even =>
    have h_even_sq : Int.Even (n ^ 2) := by
      apply Int.even_sq
      exact h_even
    have h_even_2 : Int.Even 2 := by
      rw [← hn]
      exact h_even_sq
    have h_odd_2 : Int.Odd 2 := by
      use 1
      ring
    apply no_int_even_and_odd
    use 2
    constructor
    · exact h_even_2
    · exact h_odd_2

--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intros h1 h2
    apply no_int_even_and_odd
    use n
    constructor
    · exact h2
    · exact h1
  · intro h
    cases Int.even_or_odd n with
    | inl h1 => contradiction
    | inr h2 => exact h2

--# Example 4.5.6

@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡  2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
