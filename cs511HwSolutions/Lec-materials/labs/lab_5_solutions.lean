import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--Exists examples
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  · numbers
  · numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use (1/2)*x + 1
  have h1 : (1/4)*x^2 + 1 > 0 := by extra
  have h2 : ((1/2)*x + 1)^2 = (1/4)*x^2 + x + 1 := by ring
  rw [h2]
  addarith [h1]

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd] at hp
  dsimp [Even] at hq
  dsimp [Odd]
  obtain ⟨x,hx⟩ := hp
  obtain ⟨y,hy⟩ := hq
  use x - y - 2
  rw [hx,hy]
  ring

--For All example
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intros m
  extra

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intros x y h
  have h1 : (x + y)^2 ≤ 3^2 := by
    calc
      (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
      _ = 2*(x^2 + y^2) := by ring
      _ ≤ 2 * 4 := by rel [h]
      _ ≤ 3^2 := by numbers
  apply abs_le_of_sq_le_sq' at h1
  have h2 : (0 : ℝ) ≤ (3 : ℝ) := by numbers --application below needs real numbers
  have h3 := h1 h2                           --but they are naturals by default
  obtain ⟨h3,h4⟩ := h3
  exact h3

--Divisibility examples
example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  dsimp [(· ∣ ·)]
  use -3
  numbers

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  dsimp [(· ∣ ·)] at hab
  obtain ⟨c,hc⟩ := hab
  have hac : 0 < a * c := by
    calc
      0 < b := by rel [hb]
      _ = a * c := by rw [hc]
  cancel c at hac
