import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust


math2001_init

open Set Function Nat

/-
# Important tactics and lemmas:

# Tactics
mod_cases
interval_cases
numbers (to reach a contradiction)

# Lemmas
Int.ModEq.add
Int.ModEq.sub
Int.ModEq.neg
Int.ModEq.mul
Int.ModEq.pow
Int.ModEq.refl
Int.ModEq.symm
Int.ModEq.trans
Nat.pos_of_dvd_of_pos
eq_or_lt_of_le
Nat.le_of_dvd
Nat.not_dvd_of_exists_lt_and_lt
Int.even_iff_modEq
Int.odd_iff_modEq
Int.even_or_odd
prime_test
-/


/-# Exercise 4-/

--Exercise 6.4.3.1


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry

-- theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
--   -- Case split on the parity of n
--   obtain h_even | h_odd := Nat.even_or_odd n
--   · -- Case: n is even
--     -- Extract k such that n = 2 * k using the definition of even
--     obtain ⟨k, hk⟩ := h_even
--     have hk_pos : 0 < k := by
--       apply Nat.pos_of_ne_zero
--       intro hk_zero
--       rw [hk_zero, Nat.mul_zero] at hk
--       exact Nat.not_lt_zero _ hn
--     -- Apply the inductive hypothesis to k
--     obtain ⟨b, y, hy_odd, hy⟩ := extract_pow_two k hk_pos
--     use b + 1, y
--     constructor
--     · exact hy_odd -- y is odd
--     · calc
--         n = 2 * k         := hk
--         _ = 2 * (2 ^ b * y) := by rw [hy]
--         _ = 2 ^ (b + 1) * y := by ring
--   · -- Case: n is odd
--     use 0, n
--     constructor
--     · exact h_odd -- n itself is odd
--     · rw [Nat.pow_zero, Nat.one_mul]


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
    -- If 20 divides 5, then there exists k such that `20 * k = 5`, which is impossible
    cases k with
    | zero =>
      -- Case k = 0: Contradiction since `20 * k = 0 ≠ 5`
      dsimp at hk; contradiction
    | succ n =>
      -- Case k = succ n: Contradiction since `20 * (n + 1) ≥ 20 > 5`
      have : a = 20 * (n + 1) := hk
      have : a ≥ 20 := by
        rw [this]
        exact Nat.mul_le_mul_left 20 (Nat.succ_pos n)
      -- This contradicts the fact that `a = 5`
      have : ¬ (a ≥ 20) := by exhaust
      exact this ‹a ≥ 20›
  -- Contradiction: `h` assumes that every `a` in {a | 5 ∣ a} is also in {x | 20 ∣ x}
  exact h2 (h h1)



--------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  sorry

-- example : {r : ℤ | r ≡ 7 [ZMOD 10]}
--     ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
--   intro r hr
--   -- Unpack the intersection condition
--   constructor
--   · -- Show that r ≡ 1 [ZMOD 2]
--     have h_mod_2 : r % 2 = 7 % 2 := by sorry -- rw [hr]
--     calc
--       r % 2 = 7 % 2 := h_mod_2
--       _ = 1 := by norm_num
--     -- Conclude that r ≡ 1 [ZMOD 2]
--     exact Int.mod_eq_of_lt (by norm_num) (by norm_num)
--   · -- Show that r ≡ 2 [ZMOD 5]
--     have h_mod_5 : r % 5 = 7 % 5 := by sorry -- rw [hr]
--     calc
--       r % 5 = 7 % 5 := h_mod_5
--       _ = 2 := by norm_num
--     -- Conclude that r ≡ 2 [ZMOD 5]
--     exact Int.mod_eq_of_lt (by norm_num) (by norm_num)







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
    have : 3 ∈ {1} := this -- This implies `3 ∈ {1}`, which is a contradiction because `{1}` does not contain `3`
    cases this -- Contradiction
