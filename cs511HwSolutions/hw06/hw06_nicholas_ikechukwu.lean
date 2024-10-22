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
  mod_cases hn : n % 2
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^ 2 + 3 * 0 + 7 [ZMOD 2] := by rel [hn]
      _ = 1 + 2 * 3 := by numbers
      _ ≡ 1 [ZMOD 2] := by extra
  · calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by rel [hn]
      _ = 1 + 2 * 7 := by ring
      _ ≡ 1 [ZMOD 2] := by extra


--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  · calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 0 := by ring
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 1 := by ring
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 2 + 6 * 5 := by numbers
      _ ≡ 2 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 3 + 48 * 5 := by numbers
      _ ≡ 3 [ZMOD 5] := by extra
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 4 + 204 * 5 := by numbers
      _ ≡ 4 [ZMOD 5] := by extra
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
  · left
    exact hn'
  · right
    exact hn'
  · have h := calc
      4 ≡ n ^ 2 [ZMOD 5] := by rel [hn]
      _ ≡ 4 ^ 2 [ZMOD 5] := by rel [hn']
      _ = 1 + 5 * 3 := by ring
      _ ≡ 1 [ZMOD 5] := by extra
    numbers at h




--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intros m hm1 hm2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers
    · use 2
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers
    · use 1
      constructor <;> numbers






--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  by_contra h
  obtain ⟨n, hn⟩ := h
  have h1 := le_or_gt n 1
  cases h1 with
  | inl h1 =>
    have : 2 ≤ 1 := by
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≤ 1 ^ 2 := by rel [h1]
        _ = 1 := by ring
    numbers at this
  | inr h1 =>
    have : 2 ≥ 4 := by
      calc
        2 = n ^ 2 := by rw [hn]
        _ ≥ 2 ^ 2 := by rel [h1]
        _ = 4 := by ring
    numbers at this

-- hint to follow:
-- suppose that some integer n satisfied n2 = 2

-- case 1, n<= 1: then
--  2 = n^2
-- <= 1^2,

-- case 2, n>= 2: then
--  2 = n^2
-- >=  2^2,



--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h :=
    calc 1 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · exact h2



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
      calc
        (1:ℤ) ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ = 2 ^ 2 := by norm_num
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
