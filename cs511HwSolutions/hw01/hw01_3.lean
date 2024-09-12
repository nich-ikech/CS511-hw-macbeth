import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Exercise 3:  MoP Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1 - 1) / 3 := by ring
    _ = (4 - 1) / 3 := by rw [h1]
    _ = 3 / 3 := by ring
    _ = 1 := by ring
