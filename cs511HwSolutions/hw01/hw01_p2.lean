import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init



-- Problem 2:  MoP Exercise 1.3.11 no. 7
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
    calc
      a =  a + 2 * b + 3 * c - 2 * b - 3 * c := by ring
      _ = 7 - 2 * b - 3 * c := by rw [h1]
      _ = 7 - 2 * b - 3 * c - 4 * c + 4 * c:= by ring
      _ = 7 - 2 * (b + 2 * c) - 3 * c  + 4 * c:= by ring
      _ = 7 - 2 * (3) - 3 * 1  + 4 * 1:= by rw [h2, h3]
      _ = 2 := by ring
