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
  sorry

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) : 4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  sorry

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  sorry

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  sorry

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  sorry

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by
  sorry

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  sorry
