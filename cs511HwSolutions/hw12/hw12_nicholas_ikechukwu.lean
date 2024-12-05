import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

--Exercise 6.4.3.1

-- theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
--   sorry

-- theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
--   -- Use strong induction on `n`.
--   induction n using Nat.strong_induction_on with n ih
--   cases n with
--   | zero =>
--     -- Contradiction because `n = 0` violates `hn : 0 < n`.
--     exfalso
--     exact Nat.lt_irrefl 0 hn
--   | succ n' =>
--     -- Check if `n` is odd.
--     by_cases h_odd : Odd (n + 1)
--     · -- If `n + 1` is odd, set `a = 0` and `x = n + 1`.
--       use 0, n + 1
--       constructor
--       · exact h_odd
--       · simp
--     · -- If `n + 1` is not odd, it must be even.
--       have h_even : Even (n + 1) := Nat.not_odd_iff.mpr h_odd
--       obtain ⟨k, hk⟩ := h_even
--       -- Rewrite `n + 1 = 2 * k`.
--       rw [hk] at hn
--       -- `k` is strictly smaller than `n + 1`, so apply the induction hypothesis.
--       have hk_pos : 0 < k := Nat.div_pos hn (by norm_num)
--       obtain ⟨a, x, hx_odd, hx_eq⟩ := ih k hk_pos
--       -- Combine results to construct the solution for `n + 1`.
--       use a + 1, x
--       constructor
--       · exact hx_odd
--       · rw [hx_eq, pow_succ, mul_assoc, ← hk]

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

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  sorry

-- example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
--   -- Provide a counterexample
--   intro h
--   let a := 5
--   have h1 : 5 ∣ a := by
--     use 1
--     dsimp
--   have h2 : ¬ (20 ∣ a) := by
--     intro h_div
--     obtain ⟨k, hk⟩ := h_div
--     have : 5 = 20 * k := hk -- Directly use `hk` here, no `rw` is needed
--     cases k with
--     | zero => dsimp at this; contradiction
--     | succ n =>
--       dsimp at this
--       have : 20 * (n + 1) ≥ 20 := Nat.mul_le_mul_left 20 (Nat.zero_le (n + 1))
--       have : 5 < 20 := by norm_num
--       have : 5 ≥ 20 := Nat.le_trans (Nat.le_of_eq this.symm) ‹20 * (n + 1) ≥ 20›
--       contradiction
--   -- Contradiction: `h` assumes that every `a` in {5 ∣ a} is also in {20 ∣ x}
--   exact h2 (h h1)

-- example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
--   -- Provide a counterexample
--   intro h
--   let a := 5
--   have h1 : 5 ∣ a := by
--     use 1
--     dsimp
--   have h2 : ¬ (20 ∣ a) := by
--     intro h_div
--     obtain ⟨k, hk⟩ := h_div
--     dsimp at hk
--     rw [hk] at a
--     have : a = 20 * k := hk
--     have : 5 = 20 * k := this
--     cases k with
--     | zero => dsimp at this; contradiction
--     | succ n =>
--       dsimp at this
--       have : 20 * (n + 1) ≥ 20 := Nat.mul_le_mul_left 20 (Nat.zero_le (n + 1))
--       have : 5 < 20 := by norm_num
--       have : 5 ≥ 20 := Nat.le_trans (Nat.le_of_eq this.symm) ‹20 * (n + 1) ≥ 20›
--       contradiction
--   -- Contradiction: `h` assumes that every `a` in {5 ∣ a} is also in {20 ∣ x}
--   exact h2 (h h1)




------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  sorry

-- example : {r : ℤ | r ≡ 7 [ZMOD 10]}
--     ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
--   intro r hr
--   constructor
--   -- Show that r ≡ 1 [ZMOD 2]
--   · have h2 : r ≡ 7 [ZMOD 2] := hr.symm.trans (Int.modEq_of_dvd (by norm_num))
--     rw [Int.modEq_iff_dvd] at h2
--     exact Int.modEq_of_dvd h2
--   -- Show that r ≡ 2 [ZMOD 5]
--   · have h5 : r ≡ 7 [ZMOD 5] := hr.symm.trans (Int.modEq_of_dvd (by norm_num))
--     rw [Int.modEq_iff_dvd] at h5
--     exact Int.modEq_of_dvd h5


/-# Problem 2-/

--Exercise 9.2.8.6

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry


-- example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
--   intro n h
--   -- Unpack the intersection condition: n is divisible by both 5 and 8
--   obtain ⟨h5, h8⟩ := h
--   -- Use the fact that lcm(5, 8) = 40 to conclude that n is divisible by 40
--   have h40 : 40 ∣ n := Int.dvd_lcm h5 h8
--   exact h40

-- example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
--   intro n h
--   -- Unpack the intersection condition: n is divisible by both 5 and 8
--   obtain ⟨h5, h8⟩ := h
--   -- Use the fact that lcm(5, 8) = 40 to conclude that n is divisible by 40
--   dsimp at h5 h8 ⊢
--   obtain ⟨k1, hk1⟩ := h5
--   obtain ⟨k2, hk2⟩ := h8
--   -- Since n = 5 * k1 and n = 8 * k2, we know both divide n
--   use lcm (5 : ℕ) (8 : ℕ)
--   rw [Int.coe_nat_lcm] at *
--   have h40 : (40 : ℤ) ∣ n := by exact Int.dvd_of_dvd_nat hk1 hk2


example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  intro n h
  -- Unpack the intersection condition: n is divisible by both 5 and 8
  obtain ⟨h5, h8⟩ := h
  -- Use the definitions of divisibility to express n
  obtain ⟨k1, hk1⟩ := h5
  obtain ⟨k2, hk2⟩ := h8
  -- Since n = 5 * k1 and n = 8 * k2, we show that n is divisible by lcm(5, 8) = 40
  have : lcm (5 : ℕ) (8 : ℕ) = 40 := by norm_num
  rw [this]
  -- Rewrite n using one of its divisibility expressions
  rw [hk1] at hk2
  -- Show that k1 is divisible by 8 (since both expressions for n must match)
  have h_k1 : (8 : ℤ) ∣ k1 := by
    use k2
    rw [← mul_assoc]
    exact hk2.symm
  -- Conclude that n is divisible by 40
  use k1 / 8
  rw [hk1]
  ring_nf
  rw [Int.mul_div_cancel' h_k1]


--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry

-- example : ¬ Injective r := by
--   dsimp [Injective]
--   push_neg
--   -- Provide a counterexample: two distinct sets with the same image under r
--   use {1}, {2}
--   constructor
--   · -- Show that the function values are equal
--     dsimp [r]
--     ext x
--     dsimp
--     apply Or.comm
--   · -- Show that the inputs are distinct
--     intro h_eq
--     have : 1 ∈ {1} := by dsimp; exact Or.inl rfl
--     rw [h_eq] at this
--     dsimp at this -- This implies `1 ∈ {2}`, which is a contradiction
