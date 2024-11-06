import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · rw [B]; ring -- dsimp [B] -- or rw [B]
  · rw [B, IH];ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · rw [S]; ring
  · rw [S, IH]; ring


def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · rw [factorial]; numbers
  · rw [factorial]; extra --or positivity

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  · dsimp [factorial]
    use 1
    ring
  · dsimp [Nat.Even] at *
    dsimp [factorial]
    obtain ⟨m,hm⟩ := IH
    rw [hm]
    use (k+1) * m
    ring

-- or
-- example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
--   induction_from_starting_point n, hn with k hk IH
--   · rw [factorial]
--     use 1
--     rw [factorial]
--     rw [factorial]


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  --we neet to use 2-step induction
  two_step_induction n with k IH1 IH2
  · rw [q]; ring
  · rw [q]; ring
  · rw [q]; rw[IH1]; rw [IH2]; ring

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n


#eval a 6 -- to check the outputs of a function
example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ , 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧  a (n+1) ≡ 5 [ZMOD 6])
      ∨ (a n ≡ 1 [ZMOD 6] ∧  a (n+1) ≡ 5 [ZMOD 6])
  · intros n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      · rw[a]; apply Int.ModEq.refl
      · dsimp [a]
        calc
          1 + 2 * 2 = 5 := by ring
          _ ≡ 5 [ZMOD 6] := by extra
    . obtain ⟨IH1,IH2⟩ := IH
      · right
        constructor
        · apply IH2
        · calc
            a (k +1+1) = a (k+1) +2 * a k := by rw [a]
            _ ≡ 5 + 2 * 1 [ZMOD 6] := by rel [IH1, IH2]
            _ = 6 * 1 + 1 := by ring
            _ ≡ 1 [ZMOD 6] := by extra
      · left
        constructor
        · apply IH2
        · calc
            a (k + 1 + 1) = a (k + 1) + 2 * a k := by rw [a]
            _ ≡ 1 + 2 * 5 [ZMOD 6] := by rel [IH1, IH2]
            _ = 6 * 1 +5 := by ring
            _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨H1, H2⟩ | ⟨H1,H2⟩ := H m hm
  · left
    apply H1
  · right
    apply IH2
