import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-# Extra Problems from Chapter 5-/

example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  sorry

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  sorry

example (P : Prop) : ¬(P ∧ ¬ P) := by
  sorry

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  sorry

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  sorry

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  sorry

/-# Problems from Homework 5-/

theorem dne {p : Prop} (h : ¬¬p) : p :=
  sorry

example {x y : ℕ} (h : y = 0 ∧ y = x) : 0 = x := by
  sorry

example {t1 t2 t : ℕ} (h : t1 = t2) : (t + t1) = (t + t2) := by
  sorry

example {S : Prop} {Q : Type → Prop} (h : ∃x, (S → Q x)) : S → ∃x , Q x := by
  sorry

example {x : Type} {S : Prop} {P : Type → Prop} (h : ∀x, P x → S) : ∃x, (P x → S) := by
  sorry

/-# Problems from Homework 7-/

example {P : Type → Type → Prop} (h1 : ∀x, ∀y, ∀z, P x y ∧ P y z → P x z)
  (h2 : ∀x, ∀y, P x y → P y x) : ∀x, ∀y, ∀z, P x y ∧ P z y → P x z := by
  sorry

example {Q : Type → Type → Type → Prop} {s : Type → Type} {a : Type} (h1 : ∀x, Q a x x)
  (h2 : ∀x, ∀y, ∀z, Q x y z → Q x (s y) (s z)) (h3 : ∀x, ∀y, ∀z, Q x y z → Q y x z)
  : ∃x : Type, Q (s (s a)) (s (s (s a))) x := by
  sorry
