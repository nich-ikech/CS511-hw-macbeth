import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-# Extra Problems from Chapter 5-/

example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨p,q⟩ := h
  left
  apply p

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1 h3
  · apply h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intros h
  obtain ⟨p,notP⟩ := h
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨pNotQ,notQP⟩ := h1
  intros p
  have notQ : ¬Q := pNotQ p
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain h1 | h1 := h1
  · exact h1
  · exact h2 h1

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intros x
  exact (h1 x) (h2 x)

/-# Problems from Homework 5-/

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (Classical.em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example {x y : ℕ} (h : y = 0 ∧ y = x) : 0 = x := by
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact h2

example {t1 t2 t : ℕ} (h : t1 = t2) : (t + t1) = (t + t2) := by
  have h' : (t + t1) = (t + t1) := by rfl
  conv =>       -- | (t + t1) = (t + t1)
    lhs         -- | (t + t1)
    rw [h]      -- | (t + t2)

example {S : Prop} {Q : Type → Prop} (h : ∃x, (S → Q x)) : S → ∃x , Q x := by
  intros s
  obtain ⟨x,hx⟩ := h
  have qx : Q x := hx s
  use x
  exact qx

example {x : Type} {S : Prop} {P : Type → Prop} (h : ∀x, P x → S) : ∃x, (P x → S) := by
  have h' : P x → S := h x
  use x
  apply h'

/-# Problems from Homework 7-/

example {P : Type → Type → Prop} (h1 : ∀x, ∀y, ∀z, P x y ∧ P y z → P x z)
  (h2 : ∀x, ∀y, P x y → P y x) : ∀x, ∀y, ∀z, P x y ∧ P z y → P x z := by
  intros a b c H
  obtain ⟨h3,h4⟩ := H
  obtain h5 := h2 c b h4
  exact h1 a b c ⟨h3,h5⟩

example {Q : Type → Type → Type → Prop} {s : Type → Type} {a : Type} (h1 : ∀x, Q a x x)
  (h2 : ∀x, ∀y, ∀z, Q x y z → Q x (s y) (s z)) (h3 : ∀x, ∀y, ∀z, Q x y z → Q y x z)
  : ∃x : Type, Q (s (s a)) (s (s (s a))) x := by
  use (s (s (s (s (s a)))))
  have h4 := h1 a
  have h5 := h2 a a a h4
  have h6 := h2 a (s a) (s a) h5
  have h7 := h3 a (s (s a)) (s (s a)) h6
  have h8 := h2 (s (s a)) a (s (s a)) h7
  have h9 := h2 (s (s a)) (s a) (s (s (s a))) h8
  have h10 := h2 (s (s a)) (s (s a)) (s (s (s (s a)))) h9
  exact h10
