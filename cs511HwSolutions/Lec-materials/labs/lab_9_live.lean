import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

namespace Nat

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  -- · apply Int.ModEq.pow; apply h
  -- · apply Int.ModEq.pow; apply h
  · apply Int.ModEq.pow; apply h
  · dsimp [Int.ModEq] at *
    obtain ⟨y,hy⟩ := h
    obtain ⟨x,hx⟩ := IH
    use a * x + b ^ k * y
    calc
      a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d*x) + b ^ k * (d * y) := by rw [hx, hy]
      _ = d * (a * x + b ^ k * y):= by ring



example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  · left
    use 0
    ring
  · obtain IH | IH := IH
    · right
      obtain ⟨m,hm⟩ := IH
      have hm' : 6 ^ k = 7 * m + 1 := by addarith [hm]
      dsimp [Int.ModEq]
      use 6 * m
      calc
        6 ^ (k +1) - 6 = 6 * (6 ^ k - 1) - 6 := by ring
        _ = 6 * (7 * m ) := by rw [hm]
        _ = 7 * (6 * m) := by ring
      · left
        obtain ⟨m,hm⟩ := IH
        have hm' : 6 ^ k = 7 * m +6 := by addarith [hm]
        use 6 * m + 5
        calc
          6 ^ (k + 1) - 6 = 6 * (6 ^ k - 1) - 6 := by ring
          _ = 6 * (7 * m + 6) := by rw [hm]
          _ = 7 * (6 * m) := by ring




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
      conv => lhs; ring; rw [hm'] --converge
      use 4 * m
      ring
    · left
      obtain ⟨m, hm⟩ := IH
      have hm' : 4 ^ k = 7 * m +2 := by addarith [hm]
      conv => lhs; ring; rw[hm']
      use 4 * m + 1
      ring
    · right; left
      obtain ⟨m,hm⟩ := IH
      have hm' : 4 ^ k = 7 * m+4 := by addarith [hm]
      conv => lhs; ring; rw[hm']
      use 4 * m + 2
      ring


theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k IH
  · dsimp [Odd] at *
    use 0
    ring
  · dsimp [Odd] at *
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := IH
    use 2 * s * t + s + t
    conv => lhs; ring; rw[ ht]; rw [hs]
    ring


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with k hk IH
  · numbers
  · conv => lhs; ring
    conv => rhs; ring
    calc
      2 ^ k * 2 =  2 ^ k + 2 ^ k := by ring




example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  sorry
