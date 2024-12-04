import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Mathlib.Algebra.Group.Defs

math2001_init
set_option pp.funBinderTypes true

open Function

-- apply? to get a possible answer
-- exact?

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨inj,surj⟩ := hf
  dsimp [Surjective] at surj
  choose g hg using surj
  use g
  dsimp [Inverse]
  constructor
  · ext x
    dsimp [Injective] at inj
    apply inj
    dsimp
    apply hg
  · ext y
    apply hg

theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Bijective]
  dsimp [Inverse] at h
  obtain ⟨gof,fog⟩ := h
  constructor
  · dsimp [Injective]
    intros a1 a2 h
    calc
      a1 = id a1 := by rfl
      _ = ⟨g ∘ f⟩ a1 := by rw [gof]
      _ = g ⟨f a1⟩ := by rfl
      _ = g ⟨f a1⟩ := by rw [h]
      _ = ⟨g ∘ f⟩ a2 := by rfl
      _ = id a2 := by rw [gof]
      _ = a1 := by rfl
  · dsimp [Surjective]
    intro b
    use ⟨g b⟩
    calc
      f ⟨g b⟩ = ⟨f ∘ g⟩ b := by rfl
      _ = id b := by rw [fog]
      _ = b := by rfl

theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  · apply exists_inverse_of_bijective
  ·

inductive Humour
  | melancholic
  | choleric
  | phlegmatic
  | sanguine
  deriving DecidableEq

open Humour

def a : Humour → Humour
  | melancholic => sanguine
  | choleric => choleric
  | phlegmatic => phlegmatic
  | sanguine => melancholic

def b : Humour → Humour
  | melancholic => phlegmatic
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => sanguine

def c : Humour → Humour
  | melancholic => sanguine
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => phlegmatic

example : b ∘ a = c := by
  ext x
  cases x <;> exhaust

example {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  obtain ⟨gof,fog⟩ := h
  constructor
  · apply fog
  · apply gof



example : Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m + 2 * n)) := by
  rw [bijective_iff_exists_inverse]
  use fun ⟨a,b⟩ ↦ (2 * a - b, b - a)
  dsimp [Inverse]
  constructor
  · ext ⟨m,n⟩
    dsimp
    ring
  · ext ⟨a,b⟩
    dsimp
    ring

example : Bijective (fun ((m, n) : ℝ × ℝ) ↦ (m + n, m - n)) := by
  rw [bijective_iff_exists_inverse]
  use fun ⟨a,b⟩ ↦ ((a+b)/2,(a-b)/2)
  dsimp [Inverse]
  constructor <;> ext ⟨m,n⟩ <;> dsimp <;> ring

example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  sorry


example : Reflexive ((·:ℕ) ∣ ·) := by
 intro n
 use 1
 rw [one_mul]
