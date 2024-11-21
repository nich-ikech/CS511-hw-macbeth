import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 1, 2
  constructor
  · numbers
  · numbers

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros x1 x2 hx
  have mid : 3 * x1 = 3 * x2 := by addarith [hx]
  cancel 3 at mid

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  · intros inj x1 x2 hx contra
    dsimp [Injective] at inj
    have contra' := inj contra
    contradiction
  · intros H
    dsimp [Injective]
    intros a1 a2 ha
    have H' := H a1 a2
    by_cases h : a1 = a2
    · apply h
    · have := H' h
      contradiction

example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · dsimp [Injective]
    intros a1 a2 ha
    have : 3 * a1 = 3 * a2 := by addarith [ha]
    cancel 3 at this
  · dsimp [Surjective]
    intro b
    use (4-b)/3
    ring

example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry


example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use -2,0
  constructor
  · ring
  · numbers

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  constructor
  · dsimp [Injective]
    intros a1 a2 ha
    cases a1 <;> cases a2 <;> exhaust
  · dsimp [Surjective]
    intros b
    cases b
    · use earth; exhaust
    · use air; exhaust
    · use fire; exhaust
    · use water; exhaust

example : ¬ Bijective e := by
  sorry
