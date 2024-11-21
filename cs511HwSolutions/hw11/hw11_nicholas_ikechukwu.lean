import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · -- Prove that v ∘ u = id
    funext x -- Introduce x and apply function extensionality
    dsimp [u, v]
    calc
      v (u x) = ((5 * x + 1) - 1) / 5 := by rfl
      _       = (5 * x) / 5           := by ring
      _       = x                     := by ring
  · -- Prove that u ∘ v = id
    funext y -- Introduce y and apply function extensionality
    dsimp [u, v]
    calc
      u (v y) = 5 * ((y - 1) / 5) + 1 := by rfl
      _       = (y - 1) + 1           := by ring
      _       = y                     := by field_simp  --or ring


--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  intros a b h
  apply hf
  apply hg
  exact h

--Exercise 8.3.10.4


example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  -- Since g is surjective, there exists y such that g(y) = z
  obtain ⟨y, hy⟩ := hg z
  -- Since f is surjective, there exists x such that f(x) = y
  obtain ⟨x, hx⟩ := hf y
  -- Use x as the preimage for z under g ∘ f
  use x
  -- Show that (g ∘ f)(x) = z by substituting hx and hy
  rw [Function.comp_apply, hx, hy]





/-# Exercise 4-/

-- example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
--   rw [bijective_iff_exists_inverse]
--   sorry

-- --Exercise 8.4.10.2.1

-- example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
--   sorry

-- --Exercise 8.4.10.2.2

-- example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
--  sorry





-- /-# Problem 2-/

-- --Exercise 8.3.10.5

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  choose g hg using hf
  use g
  ext y
  exact hg y

-- --Exercise 8.3.10.7

-- example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
--     g1 = g2 := by
--   ext y
--   calc
--     g1 y = g1 (f (g2 y)) := by rw [h2.left_inverse]
--       _ = g2 y          := by rw [h1.left_inverse]
