import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

namespace Nat

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · dsimp [Int.ModEq]
    use 0
    ring
  · dsimp [Int.ModEq] at *
    obtain ⟨y,hy⟩ := h
    obtain ⟨x,hx⟩ := IH
    use a*x + b^k*y
    calc
      a ^ (k+1) - b ^ (k+1) = a * (a^k - b^k) + b^k * (a - b) := by ring
      _ = a * (d*x) + b^k * (d*y) := by rw [hx,hy]
      _ = d * (a * x + b ^ k * y) := by ring

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    use 0
    ring
  · obtain IH | IH := IH
    · right
      obtain ⟨m,hm⟩ := IH
      have hm' : 6 ^ k = 7 * m + 1 := by addarith [hm]
      use 6 * m
      calc
        6 ^ (k + 1) - 6 = 6 * 6 ^ k - 6 := by ring
        _ = 6 * (7 * m + 1) - 6 := by rw [hm']
        _ = 7 * (6 * m) := by ring
    · left
      obtain ⟨m,hm⟩ := IH
      have hm' : 6 ^ k = 7 * m + 6 := by addarith [hm]
      use 6 * m + 5
      calc
        6 ^ (k + 1) - 1 = 6 * 6 ^ k - 1 := by ring
        _ = 6 * (7 * m + 6) - 1 := by rw [hm']
        _ = 7 * (6 * m + 5) := by ring

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    use 0
    ring
  · obtain IH | IH | IH := IH
    · right; right
      obtain ⟨m,hm⟩ := IH
      have hm' : 4 ^ k = 7 * m + 1 := by addarith [hm]
      conv => lhs; ring; rw [hm']
      use 4 * m
      ring
    · left
      obtain ⟨m,hm⟩ := IH
      have hm' : 4 ^ k = 7 * m + 2 := by addarith [hm]
      conv => lhs; ring; rw [hm']
      use 4 * m + 1
      ring
    · right; left
      obtain ⟨m,hm⟩ := IH
      have hm' : 4 ^ k = 7 * m + 4 := by addarith [hm]
      conv => lhs; ring; rw [hm']
      use 4 * m + 2
      ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k IH
  · dsimp [Odd] at *
    use 0
    ring
  · dsimp [Odd] at *
    obtain ⟨s,hs⟩ := ha
    obtain ⟨t,ht⟩ := IH
    use 2 * s * t + s + t
    calc
      a ^ (k + 1) = a * a ^ k := by ring
      _ = (2 * s + 1) * (a ^ k) := by rw [hs]
      _ = (2 * s + 1) * (2 * t + 1) := by rw [ht]
      _ = 2 * (2 * s * t + s + t) + 1 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with k hk IH
  · numbers
  · calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [IH]
      _ = k ^ 2 + 4 + k * k + 4 := by ring
      _ ≥ k ^ 2 + 4 + 5 * k + 4 := by rel [hk]
      _ = k ^ 2 + 2 * k + 5 + (3 * k + 3) := by ring
      _ ≥ k ^ 2 + 2 * k + 5 + (3 * 5 + 3) := by rel [hk]
      _ ≥ k ^ 2 + 2 * k + 5 := by extra
      _ = (k + 1) ^ 2 + 4 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intros x hx
  induction_from_starting_point x, hx with k hk IH
  · numbers
  · calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 3 := by rel [IH]
      _ = k ^ 3 + k * k ^ 2 := by ring
      _ ≥ k ^ 3 + 10 * k ^ 2 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 7 * k * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * k := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
      _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
      _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by extra
      _ = (k + 1) ^ 3 := by ring
