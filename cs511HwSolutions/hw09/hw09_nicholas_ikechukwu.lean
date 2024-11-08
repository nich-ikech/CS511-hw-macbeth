import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--# Exercise 3

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10


example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · -- base case
    rw [c]  -- c 0 = 7
    use 3   -- show 7 = 2*3 + 1
    ring
  · -- inductive step
    rw [c]  -- c (k+1) = 3 * c k - 10
    obtain ⟨m, hm⟩ := IH  -- get m where c k = 2*m + 1
    use (3*m - 4)  -- claim c (k+1) = 2*(3*m - 4) + 1
    calc
      3 * c k - 10 = 3 * (2*m + 1) - 10 := by rw [hm]
      _ = 6*m + 3 - 10 := by ring
      _ = 6*m - 7 := by ring
      _ = 2*(3*m - 4) + 1 := by ring


--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]; ring
  · rw [c, IH]; ring



--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · rw [y]; ring
  · rw [y, IH]; ring





--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]; ring
  · rw [b]; ring
  · rw [b]; rw[IH1]; rw [IH2]; ring

--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c']; ring
  · rw [c']; ring
  · rw [c']; rw[IH1]; ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]; ring
  · rw [t]; ring
  · rw [t]; rw[IH1]; rw [IH2]; ring

--# Problem 2

--Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ n : ℕ,
      (s n ≡ 2 [ZMOD 5] ∧ s (n+1) ≡ 3 [ZMOD 5])
      ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n+1) ≡ 2 [ZMOD 5])
  · intro n
    induction n with
    | zero =>
      left
      constructor
      · rw [s]
        apply Int.ModEq.refl
      · rw [s]
        apply Int.ModEq.refl
    | succ k IH =>
      cases IH with
      | inl h =>
        right
        constructor
        · exact h.right
        · rw [s]
          calc
            2 * s (k + 1) + 3 * s k ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [h.left, h.right]
            _ = 2 + (2 *5) := by rfl
            _ ≡ 2 [ZMOD 5] := by extra
      | inr h =>
        left
        constructor
        · exact h.right
        · rw [s]
          calc
            2 * s (k + 1) + 3 * s k ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [h.left, h.right]
            _ =  3 + (2 *5)  := by rfl
            _ ≡ 3 [ZMOD 5] := by extra

  cases H m with
  | inl h => left; exact h.left
  | inr h => right; exact h.left




--Exercise 6.3.6.7


def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2^n := by
  dsimp [forall_sufficiently_large]
  use 5  -- We start from n = 5
  intros n hn
  induction_from_starting_point n, hn with k hk IH
  · -- Base case: n = 5
    have h5 : r 5 = 30 := by
      rw [r, r, r, r, r]
      ring
    have h : 30 ≥ 2^5 := by norm_num
    exact h5.symm h
  · -- Inductive step
    have h_rec : r (k + 2) = 2 * r (k + 1) + r k := by rfl
    rw [h_rec]
    have IH1 : r k ≥ 2^k := IH (Nat.le_succ (Nat.le_succ (Nat.le_refl _)))
    have IH2 : r (k+1) ≥ 2^(k+1) := IH (Nat.le_succ (Nat.le_refl _))
    calc
      2 * r (k + 1) + r k ≥ 2 * 2^(k+1) + 2^k := by rel [IH1, IH2]
      _ = 2^(k+2) + 2^k := by ring
      _ ≥ 2^(k+2) := by extra
