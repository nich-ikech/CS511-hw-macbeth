import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

math2001_init

/- # Lemmas:

# Int.ModEq.add
# Int.ModEq.sub
# Int.ModEq.neg
# Int.ModEq.mul
# Int.ModEq.pow
# Int.ModEq.refl
# Int.ModEq.symm
# Int.ModEq.trans

# We'll take the above as given.  You prove some of them on the homework, and others are given in the textbook. -/

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply h
  apply Int.ModEq.refl

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) : 4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply hb
  apply Int.ModEq.pow
  apply hb
  apply Int.ModEq.refl

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  dsimp [Int.ModEq]
  use 1
  ring

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  dsimp [Int.ModEq]
  use 3
  ring

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  dsimp [Int.ModEq] at hn
  obtain ⟨k,hk⟩ := hn
  use 9*k^3 + 9*k^2 + 10*k + 2
  have hk' : n = 3 * k + 1 := by addarith [hk]
  rw [hk']
  ring

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  have hncube : n ^ 3 ≡ 1 [ZMOD 3] := by
    calc
      n ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by apply Int.ModEq.pow; apply hn
      _ ≡ 1 [ZMOD 3] := by dsimp [Int.ModEq]; use 0; ring
  calc
    n ^ 3 + 7 * n ≡ 1 + 7 * 1 [ZMOD 3] := by rel [hn,hncube]
    _ ≡ 2 [ZMOD 3] := by dsimp [Int.ModEq]; use 2; ring

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · ring
  · intros y h
    have h' : 4 * y = 4 * 3 := by
      calc
        4 * y = 4 * y - 3 + 3 := by ring
        _ = 9 + 3 := by rw [h]
        _ = 4 * 3 := by ring
    cancel 4 at h'
