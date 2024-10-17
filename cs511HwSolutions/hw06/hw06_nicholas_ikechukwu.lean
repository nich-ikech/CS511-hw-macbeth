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
    5 * n ^ 2 + 3 * n + 7 ≡ n ^ 2 + n + 1 [ZMOD 2] := by
      rel [Int.ModEq.mul_left, Int.ModEq.add_left]
    _ ≡ n ^ 2 + n + 1 [ZMOD 2] := by rfl
    _ ≡ 1 [ZMOD 2] := by rel [Int.ModEq.add_sq_self_add_one]

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  all_goals
    calc
      x ^ 5 ≡ hx ^ 5 [ZMOD 5] := by rel [hx]
      _ ≡ hx [ZMOD 5] := by apply Int.ModEq.pow_five
      _ ≡ x [ZMOD 5] := by rel [hx]

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases hn' : n % 5
  · have h := calc
      4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
      _ ≡ 0 ^ 2 [ZMOD 5] := by rel [hn']
      _ = 0 := by ring
    numbers at h
  · have h := calc
      4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
      _ ≡ 1 ^ 2 [ZMOD 5] := by rel [hn']
      _ = 1 := by ring
    numbers at h
  · right
    exact hn'
  · left
    exact hn'
  · have h := calc
      4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
      _ ≡ 4 ^ 2 [ZMOD 5] := by rel [hn']
      _ ≡ 1 [ZMOD 5] := by norm_num
    numbers at h

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
        7 < m * 2 := by
          have : 3 < m := by exact Nat.lt_of_succ_le (Nat.succ_le_of_lt hm1)
          exact Nat.lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul_right 2 this)
        _ ≤ m * m := by gcongr; exact Nat.succ_le_of_lt hm1

--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h_even : Even (n ^ 2) := by
    use 1
    rw [hn]
    ring
  have h_odd_or_even : Odd n ∨ Even n := by exact Int.odd_or_even n
  cases h_odd_or_even with
  | inl h_odd =>
    have h_odd_sq : Odd (n ^ 2) := by exact Odd.pow_two h_odd
    apply Int.even_and_odd_absurd
    use n ^ 2
    constructor
    · exact h_even
    · exact h_odd_sq
  | inr h_even =>
    have h_even_sq : Even (n ^ 2) := by exact Even.pow_two h_even
    have h : (n ^ 2) / 2 = 1 := by
      rw [hn]
      norm_num
    have h_contra : ¬(Even 1) := by
      intro h_even_1
      have h_odd_1 : Odd 1 := by use 0; ring
      apply Int.even_and_odd_absurd
      use 1
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
  · intros h1 h2
    apply Int.even_and_odd_absurd
    use n
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
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 2 ^ 2 [ZMOD 3] := by norm_num
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
