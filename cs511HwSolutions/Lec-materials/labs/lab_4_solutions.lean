import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- # Lab 4 -/

/-
Or:
  In the context:  split the premise into cases
    E.g., obtain h1 | h2 := h
  In the goal:  choose which case you want to prove
    using the tactics left and right
And:
  In the context:  split the premise into 2 separate premises
    E.g., obtain ⟨h1,h2⟩ := h
  In the goal:  use the tactic constructor to split the proof into cases;
    one for each clause of the ∧
-/

/- If we have an implication f : p -> q,
in Lean 4, it works essentially like a function.
That is, if we have x : p, then if we write f x, its type is q.
In other words, if we apply a proof of p to a proof that p -> q,
we get a proof of q. -/

--Example 2.3.4
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  · left; addarith [h2]
  · right; addarith [h2]

--Exercise 2.3.6.1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h | h := h
  · rw [h]; numbers
  · rw [h]; numbers

--Exercise 2.3.6.7
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    x < x + 1/2 := by extra
    _ = (2*x + 1)/2 := by ring
    _ = y/2 := by rw [h]

--Exercise 2.4.5.2
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1,h2⟩ := H
  calc
    2*r = r + s + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1,h2]
    _ = 6 := by numbers

--Exercise 2.4.5.3
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1,h2⟩ := H
  have h3 : m + 5 ≤ 8 := by
    calc
      m + 5 ≤ n := by rel [h2]
      _ ≤ 8 := by rel [h1]
  addarith[h3]

--Exercise 2.4.5.4
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h : p ≥ 7 := by addarith[hp]
  constructor
  · calc
      p^2 = p*p := by ring
      _ ≥ 7*p := by rel [h]
      _ ≥ 7*7 := by rel [h]
  · apply h

--Exercise 2.4.5.5
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  constructor
  · addarith [h]
  · calc
      3*a = 3*(a - 1) + 3 := by ring
      _ ≥ 3*5 + 3 := by rel [h]
      _ ≥ 10 := by numbers
