import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function


--injective : ∀x∀y fx = fy -> x = y
--x ≠ y -> fx ≠ fy
--for every y value, there's only one assoc x value (one in domain, one in co domain)

--surjective ∀y, ∃x fx = y
--has to do with onto** sur**

--bijective == injective an surjective


example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 4, 5
  constructor <;> numbers


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros a1 a2 ha
  have : 3 * a1 = 3 * a2 := by addarith [ha]
  cancel 3 at this

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  · intros inj x1 x2 hx
    dsimp [Injective] at inj
    intros contra
    have this := inj contra
    contradiction
  · intros H
    dsimp [Injective]
    intros a1 a2 ha
    by_cases h: a1 = a2
    · exact h
    · have contra := H a1 a2 h
      contradiction


example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  · dsimp [Injective]
    intros a1 a2 ha
    have : 3 * a1 =3 * a2 := by addarith [ha]
    cancel 3 at this
  · dsimp [Surjective]
    intros b
    use (4 - b)/3
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
  use -2, 0
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
    cases a1 <;> cases a2 <;> exhaust -- dsimp [e] at ha <;> try contradiction-- exhaust or trivial --do all cases and solve by exhausting
  · dsimp [Surjective]
    intros b
    cases b
    · use earth; exhaust
    . use air; exhaust
    · use fire; exhaust
    · use water; exhaust


example : ¬ Bijective e := by
  sorry


#eval Lean.versionString
