import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true



--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro h1
    obtain ⟨hp, hr⟩ := h1
    obtain ⟨pq, qp⟩ := h
    constructor
    · exact pq hp
    · exact hr
  · intro h1
    obtain ⟨hq, hr⟩ := h1
    obtain ⟨pq, qp⟩ := h
    constructor
    · exact qp hq
    · exact hr




--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    obtain h | h := h
    · right; exact h
    · left; exact h
  · intro h
    obtain h | h := h
    · right; exact h
    · left; exact h



--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro p
      apply h
      left
      exact p
    · intro q
      apply h
      right
      exact q
  · intro h
    obtain ⟨hp, hq⟩ := h
    intro hpq
    obtain hpq | hpq := hpq
    · contradiction
    · contradiction




--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h1
    obtain ⟨x, hx⟩ := h1
    use x
    obtain ⟨pq, qp⟩ := h x
    exact pq hx
  · intro h1
    obtain ⟨x, hx⟩ := h1
    use x
    obtain ⟨pq, qp⟩ := h x
    exact qp hx




--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := h
    use y, x
    exact hxy
  · intro h
    obtain ⟨y, x, hxy⟩ := h
    use x, y
    exact hxy



--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h y x
    exact h x y
  · intro h x y
    exact h y x



--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x, hx⟩ := h1
    use x
    constructor
    · exact hx
    · exact h2
  · intro h
    obtain ⟨x, hpx, hq⟩ := h
    constructor
    · use x; exact hpx
    · exact hq




--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h hq
    by_contra hp
    have hnq : ¬Q := h hp
    contradiction
  · intro h hnp hq
    have hp : P := h hq
    contradiction
