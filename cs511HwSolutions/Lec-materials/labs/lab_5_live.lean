import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--Exists examples
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3; --you can use a semicolon if you're writing multiple statements on same line
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2 -- actual values that solve it
  ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2 --existential in a goal we employ 'use'
  constructor --since we have an 'and'
  . numbers
  . numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1/2
  have h1 : (x + 1/2)^2 = x^2 + x + 1/4 := by ring
  rw[h1]
  have h2 : x^2 + 1/4 > 0 := by extra --b/c it's just a square and a positive quantity
  addarith [h2]

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  -- we'll use new terms here
  --dsimp means ...
  dsimp [Odd] at *
  dsimp [Even] at *
  obtain ⟨x, hx⟩ := hp --existential in a statement we employ obtain
  obtain ⟨y, hy⟩ := hq
  use x - y - 2
  rw [hx,hy]
  ring



--For All example
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0 -- 0 is in Natural numbers
  -- intro does the box creating (like in natural deduction on paper)
  intros m -- you can use 'intro' for a single variable
  extra

--Needs real numbers, but automatically gives integers
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -4
  intros x y h
  have h1 : (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by exact
  have h2 : (x + y)^2 + (x - y)^2 = 2*(x^2 + y^2) := by ring
  sorry

--Divisibility examples
example : (11 : ℕ) ∣ 88 := by
  dsimp [(.∣.)]
  use 8
  ring



example : (-2 : ℤ) ∣ 6 := by
  use -3
  ring

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  dsimp [(.∣.)] at hab
  obtain ⟨k,hk⟩ := hab
  rw [hk] at hb
  cancel k at hb
