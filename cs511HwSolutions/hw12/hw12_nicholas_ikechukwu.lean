import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust


math2001_init

open Set Function Nat



/-# Exercise 4-/

--Exercise 6.4.3.1


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
match n with
|0 =>
have contra := Nat.not_lt_zero 0
contradiction
|1 =>
  use 0, 1
  constructor
  dsimp[Odd]
  use 0
  numbers
  numbers
|2 =>
  use 1, 1
  constructor
  dsimp[Odd]
  use 0
  numbers
  numbers
|k+3 =>
  let h_ev_od := Nat.even_or_odd k
  let t := (Nat.succ k)
  have hk : Nat.succ k > 0 := by extra
  obtain h_even | h_odd := h_ev_od
  have IH := extract_pow_two t hk
  obtain ⟨a, x, h_odd, ht⟩ := IH
  use 0, k + 3
  constructor
  dsimp[Odd]
  obtain ⟨r, h_even⟩ := h_even
  use r+1
  rw[h_even]
  ring
  ring
  have IH := extract_pow_two t hk
  obtain ⟨a, x, hod, ht⟩ := IH
  match a with
  |0 =>
  use 0, x+2
  constructor
  obtain ⟨l, hl⟩ := hod
  use l+1
  rw[hl]
  ring
  -- calc step with k + 3
  calc
    k + 3 = t + 2 := by rfl
    _ = 2 ^ 0 * x + 2 := by rw[ht]
    _ = 2 ^ 0 * (x + 2) := by ring
  |1 =>
    have hx : x + 1 > 0 := by extra
    have IH := extract_pow_two (x + 1) hx
    obtain ⟨y, u, hu_odd, hxx⟩ := IH
    use y+1, u
    constructor
    apply hu_odd
    -- calc step with k + 3
    calc
      k + 3 = t + 2 := by rfl
      _ = 2 ^ 1 * x + 2 := by rw[ht]
      _ = 2 * (x + 1) := by ring
      _ = 2 * (2 ^ y * u) := by rw[hxx]
      _ = 2 ^ (y + 1) * u := by ring
  |s + 2 =>
  use 1, 2 ^ (s + 1) * x + 1
  constructor
  use 2^s*x
  ring
  calc
    k + 3 = t + 2 := by rfl
    _ = 2 ^ (s + 2) * x + 2:= by rw[ht]
    _ = 2 ^ 1 * (2 ^ (s + 1) * x + 1) := by ring



/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

--DISPROVED
example : 4 ∉ {a : ℚ | a < 3} := by
  intro h
  have : ¬(4 < 3) := by norm_num
  contradiction
------------------------------------------------------------------------------------
--Exercise 9.1.10.2

--PROVED
example : 6 ∈ {n : ℕ | n ∣ 42} := by
  use 7
  norm_num

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

--DISPROVED
example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  intro h
  have ⟨m, hm⟩ := h
  have : (8 % 5) = (5 * m % 5) := congr_arg (· % 5) hm
  norm_num at this -- Shows contradiction since mod should be non-zero.




/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

--PROVED
example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  intros a ha
  rcases ha with ⟨k, rfl⟩ -- a = 20 * k for some k
  use (4 * k)
  ring_nf -- simplifies to show that a = (5 * (4 * k))

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

--DISPROVED
example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  -- Assume for contradiction that the subset relation holds
  intro h
  -- Provide a counterexample: a = 5
  let a := 5
  have h1 : 5 ∣ a := by
    use 1
    exact Nat.mul_one 5
  have h2 : ¬ (20 ∣ a) := by
    intro h_div
    obtain ⟨k, hk⟩ := h_div
    cases k with
    | zero =>
      dsimp at hk; contradiction
    | succ n =>
      have : a = 20 * (n + 1) := hk
      have : a ≥ 20 := by
        rw [this]
        exact Nat.mul_le_mul_left 20 (Nat.succ_pos n)
      have : ¬ (a ≥ 20) := by exhaust
      exact this ‹a ≥ 20›
  exact h2 (h h1)



--------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intro x hx
  constructor
  obtain ⟨t, ht⟩ := hx
  -- use step
  use 5*t + 3
  -- calc step for x - 1
  calc
    x - 1 = (x - 7) + 6 := by ring
    _ = (10 * t) + 6 := by rw[ht]
    _ = 2 * (5 * t + 3) := by ring
  -- Obtain witnesses
  obtain ⟨t, ht⟩ := hx
  -- use step
  use 2*t + 1
  -- calc step for x -2
  calc
    x - 2 = (x - 7) + 5 := by ring
    _ = (10 * t) + 5 := by rw[ht]
    _ = 5 * (2 * t + 1) := by ring




/-# Problem 2-/

--Exercise 9.2.8.6


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  intro n h
  -- Unpack the intersection condition: n is divisible by both 5 and 8
  obtain ⟨h5, h8⟩ := h
  -- Use the definitions of divisibility to express n
  obtain ⟨k1, hk1⟩ := h5 -- n = 5 * k1
  obtain ⟨k2, hk2⟩ := h8 -- n = 8 * k2
  -- Rewrite n using one of its divisibility expressions
  rw [hk1] at hk2 -- Substitute n = 5 * k1 into the second equation
  -- Simplify to show that k1 is divisible by 8
  have h_k1 : (8 : ℤ) ∣ k1 := by
    use k2
    sorry -- rw [← mul_assoc] at hk2
    -- exact hk2.symm
  -- Conclude that n is divisible by 40
  obtain ⟨m, hm⟩ := h_k1 -- k1 = 8 * m for some m
  rw [hm] at hk1 -- Substitute k1 = 8 * m into n = 5 * k1
  use m -- Show that n = 40 * m
  rw [hk1]
  ring_nf -- Simplify to show n = 40 * m



-- example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
--   dsimp [Set.subset_def]
--   intro x hx

--   -- Destructure the intersection
--   obtain ⟨h5, h8⟩ := hx

--   -- Obtain witnesses for divisibility
--   obtain ⟨t, ht5⟩ := h5
--   obtain ⟨s, ht8⟩ := h8

--   -- Use step
--   use 8*t

--   -- Prove divisibility by 40
--   have a: x = 5 * t := ht5
--   calc
--     x = 5 * t := a
--     _ = 8 * s := ht8
--     _ = 40 * t := by ring





--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}



example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  -- Provide a counterexample: two distinct sets with the same image under r
  use {1}, {1, 3}
  constructor
  · -- Prove that r({1}) = r({1, 3})
    dsimp [r]
    ext x
    constructor
    · -- Forward direction: x ∈ {1} ∪ {3} → x ∈ {1, 3}
      intro h
      cases h with
      | inl h1 => exact Or.inl sorry -- x ∈ {1} implies x ∈ {1, 3}
      | inr h3 => exact Or.inr h3 -- x ∈ {3} implies x ∈ {1, 3}
    · -- Backward direction: x ∈ {1, 3} → x ∈ {1} ∪ {3}
      intro h
      cases h with
      | inl h1 => exact Or.inl sorry -- x ∈ {1} implies x ∈ {1} ∪ {3}
      | inr h3 => exact Or.inr h3 -- x ∈ {3} implies x ∈ {1} ∪ {3}
  · -- Prove that {1} ≠ {1, 3}
    intro h_eq
    have : 3 ∈ {1, 3} := by right; rfl -- Explicitly show that 3 is in {1, 3}
    rw [←h_eq] at this -- Substitute equality into the proof
    have : 3 ∈ {1} := this
    cases this -- Contradiction



-- example : ¬ Injective r := by
--   dsimp [Injective, r]
--   push_neg
--   use {1, 2}, {1, 2, 3}
--   dsimp
--   constructor
--   · ext x
--     dsimp
--     suffices x ∈ {1, 2} → x ∈ {1, 2, 3} by exhaust
--     intro hx
--     right
--     exact hx
--   · ext x
--     dsimp
--     suffices x ∈ {1, 2, 3} → x ∈ {1, 2} by exhaust
--     intro hx
--     exact hx.left


-- example : ¬ Injective r := by
--   dsimp [Injective]
--   push_neg
--   -- Provide a counterexample: two distinct sets with the same image under r
--   use {1}, {1, 3}
--   constructor
--   · -- Prove that r({1}) = r({1, 3})
--     dsimp [r]
--     ext x
--     constructor
--     · -- Forward direction: x ∈ {1} ∪ {3} → x ∈ {1, 3}
--       intro h
--       cases h with
--       | inl h1 => exact Or.inl h1
--       | inr h3 => exact Or.inr h3
--     · -- Backward direction: x ∈ {1, 3} → x ∈ {1} ∪ {3}
--       intro h
--       cases h with
--       | inl h1 => exact Or.inl h1
--       | inr h3 => exact Or.inr h3
--   · -- Prove that {1} ≠ {1, 3}
--     intro h_eq
--     have : 3 ∈ {1, 3} := by right; rfl
--     rw [←h_eq] at this
--     have : 3 ∈ {1} := this
--     cases this
