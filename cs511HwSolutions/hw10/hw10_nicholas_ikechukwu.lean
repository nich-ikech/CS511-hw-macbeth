import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int

/- # Exercise 3 -/

--Exercise 8.1.13.2
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 4, 5
  constructor <;> numbers

--Exercise 8.1.13.3
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros a1 a2 ha
  have : 3 * a1 = 3 * a2 := by addarith [ha]
  cancel 3 at this

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry

--Exercise 8.1.13.5
--# Prove one-------------------------------------------------------

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro y
  use y / 2
  field_simp
  ring

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

--# -----------------------------------------------------------------

/- # Exercise 4 -/

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

--Exercise 8.1.13.8
--# Prove one-------------------------------------------------------

example : Injective h := by
  sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor
  · rfl
  · exhaust

--Exercise 8.1.13.9
--# Prove one-------------------------------------------------------

example : Surjective h := by
  dsimp [Surjective]
  intro y
  cases y
  · use porthos; rfl
  · use athos; rfl

example : ¬ Surjective h := by
  sorry

--# ----------------------------------------------------------------

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

--Exercise 8.1.13.11
--# Prove one-------------------------------------------------------

example : Surjective l := by
  sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

--# ----------------------------------------------------------------

/- # Problem 2 -/

--Exercise 8.1.13.13
--# Prove one-------------------------------------------------------

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intros f hf
  dsimp [Injective] at *
  intros x y h
  apply hf
  addarith [h]

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry

--Exercise 8.1.13.14
--# Prove one-------------------------------------------------------


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  intros f h_inj x y h_eq
  have : f x = f y := by
    calc
      f x = (f x + x) - x := by ring
      _   = (f y + y) - x := by rw [h_eq]
      _   = f y + (y - x) := by ring
  exact h_inj this


example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

--Exercise 8.1.13.16
--# Prove one-------------------------------------------------------

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  apply ne_of_lt
  calc
    0 * x = 0 := by ring
    _ < 1 := by numbers
