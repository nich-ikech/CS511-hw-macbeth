import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init





/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

-- not reflexive holds
example : ¬ Reflexive (· ∼ ·) := by
  -- unfold the definition of reflexivity
  dsimp[Reflexive]
  push_neg
  -- choose 0 as the counterexample
  use 0
  -- unfold the definitions
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  -- introduce a coefficient k for the modular equivalence
  intro k
  -- split the proof into two cases: k ≥ 0 and k < 0
  by_cases h : k>-1
  -- case 1: k ≥ 0
  · apply ne_of_lt
    -- prove 0 ≤ k
    have hh : 0 <= k := by addarith[h]
    calc
      0 - (0 + 1) = -1 := by ring
      _ < 5 * 0 := by numbers
      _ <= 5 * k := by rel[hh]

  -- case 2: k < 0
  · apply ne_of_gt
    -- convert k > -1 to k ≤ -1
    have h := le_of_not_gt h
    calc
      5 * k <= 5 * (-1) := by rel[h]
      _ < -1 := by numbers
      _ = 0 - (0 + 1) := by ring



example : Symmetric (· ∼ ·) := by
  sorry

-- not Symmetric holds
example : ¬ Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  push_neg
  -- choose specific counterexample values
  use 0
  use 1
  -- first part: 1 is related to 0 under the relation
  constructor
  dsimp[Int.ModEq]
  use 0
  ring
  -- second part: 0 is not related to 1 under the relation
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro k
  by_cases h : k>-1
  -- case 1: k ≥ 0
  · apply ne_of_lt
    have hh : 0 <= k := by addarith[h]
    calc
      0 - (1 + 1) = -2 := by ring
      _ < 5 * 0 := by numbers
      _ <= 5 * k := by rel[hh]
  -- case 2: k < 0
  · apply ne_of_gt
    have h := le_of_not_gt h
    calc
      5 * k <= 5 * (-1) := by rel[h]
      _ < -2 := by numbers
      _ = 0 - (1 + 1) := by ring



-- AntiSymmetric holds
example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  intro h1 h2
  have h3 := by apply Int.ModEq.add h1 h2
  have h4 : (x + y) - (y + x) ≡ (x + y) - (x + 1 + (y + 1)) [ZMOD 5] := Int.ModEq.sub_left h3
  have rw1 : x + y - (y + x) = 0 := by ring
  rw[rw1] at h4
  have rw2 : x + y - (x + 1 + (y + 1)) = -2 := by ring
  rw[rw2] at h4
  -- propose contradiction
  have contra : ¬ 0 ≡ -2 [ZMOD 5] := by {
    dsimp[Int.ModEq]
    dsimp[Int.instDvdInt]
    push_neg
    intro k
    by_cases h : k > 0
    --apply not equal of less than
    apply ne_of_lt
    have hh : 1 <= k := by addarith[h]
    --calc step
    calc
      0 - (-2) = 2 := by ring
      _ < 5 * 1 := by numbers
      _ <= 5 * k := by rel[hh]
    --apply not equal of greater than
    apply ne_of_gt
    have h := le_of_not_gt h
    calc
      5 * k <= 5 * (0) := by rel[h]
      _ < 2 := by numbers
      _ = 0 - (-2) := by ring

  }
  contradiction


example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry




example : Transitive (· ∼ ·) := by
  sorry

-- not Transitive holds
example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use 0
  use 1
  use 2
  constructor
  use 0
  ring
  constructor
  use 0
  ring
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro k
  by_cases h : k > 0
  --apply not equal of less than
  apply ne_of_lt
  have hk : 1 <= k := by addarith[h]
  --calc step
  calc
    - (- (2 - (0 + 1))) = 1 := by numbers
    _ < 5 * 1 := by numbers
    _ <= 5 * k := by rel[hk]
  --apply not equal of greater than
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    5 * k <= 5 * (0) := by rel[h]
    _ < 1 := by numbers
    _ = 2 - (1) := by ring

end






/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

-- not Reflexive holds
example : ¬ Reflexive (· ∼ ·) := by
  dsimp[Reflexive]
  push_neg
  use 1
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro k
  by_cases h : k > 0
  apply ne_of_lt
  have hh : 1 <= k := by addarith[h]
  calc
    -(-(1 + 1)) = 2 := by ring
    _ < 3 * 1 := by numbers
    _ <= 3 * k := by rel[hh]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    3 * k <= 3 * (0) := by rel[h]
    _ = 0 := by numbers
    _ < 1 + 1 := by numbers



-- Symmetric holds
example : Symmetric (· ∼ ·) := by
  dsimp[Symmetric]
  intro x y h
  have hk : y + x = x + y := by ring
  rw[hk]
  apply h

example : ¬ Symmetric (· ∼ ·) := by
  sorry



example : AntiSymmetric (· ∼ ·) := by
  sorry

-- not AntiSymmetric holds
example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp[AntiSymmetric]
  push_neg
  use 1
  use 2
  constructor
  use 1
  ring
  constructor
  use 1
  ring
  numbers

example : Transitive (· ∼ ·) := by
  sorry

-- not Transitive holds
example : ¬ Transitive (· ∼ ·) := by
  dsimp[Transitive]
  push_neg
  use 1
  use 2
  use 1
  constructor
  --choose 1
  use 1
  ring
  constructor
  use 1
  ring
  dsimp[Int.ModEq]
  dsimp[Int.instDvdInt]
  push_neg
  intro k
  by_cases h : k > 0
  apply ne_of_lt
  have hk : 1 <= k := by addarith[h]
  calc
    -(-(1 + 1)) = 2 := by ring
    _ < 3 * 1 := by numbers
    _ <= 3 * k := by rel[hk]
  apply ne_of_gt
  have h := le_of_not_gt h
  calc
    3 * k <= 3 * (0) := by rel[h]
    _ < 2 := by numbers
    _ = 1 + 1 := by ring

end






/-# Problem 2-/
--Exercise 10.1.5.6

-- Reflexive holds
example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp[Reflexive]
  intro x
  dsimp[Set.subset_def]
  intro x h
  apply h


example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry




example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry


-- Not Symmetric holds
example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp[Symmetric]
  push_neg
  use {1}
  use {1, 2}
  dsimp[Set.subset_def]
  constructor
  intro x h
  left
  apply h
  push_neg
  --choose 2
  use 2
  constructor
  right
  numbers
  numbers

-- AntiSymmetric holds
example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp[AntiSymmetric]
  dsimp[Set.subset_def]
  intro x y h1 h2
  ext x
  constructor
  intro h3
  apply h1 x h3
  intro h3
  apply h2 x h3


example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

-- Transitive holds
example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp[Transitive]
  dsimp[Set.subset_def]
  intro x y z h1 h2
  intro t h
  have h3 := h1 t h
  apply h2 t h3

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
