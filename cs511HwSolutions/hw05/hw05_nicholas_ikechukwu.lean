import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

/- # The first three are theorems provided in MoP Section 3.3 -/

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


@[autograded 2]
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x - y
  calc
    a - c - (b - d) = (a - b) - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

@[autograded 2]
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  use -x
  calc
    -a - (-b) = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * (-x) := by ring

@[autograded 2]
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use -x
  calc
    b - a = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * (-x) := by ring

@[autograded 2]
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

@[autograded 2]
theorem exercise_3_3_12_6 {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  have h1 : 2 * a ≡ 2 * b [ZMOD 5] := Int.ModEq.mul (Int.ModEq.refl 2) h
  have h2 : 3 ≡ 3 [ZMOD 5] := Int.ModEq.refl 3
  exact Int.ModEq.add h1 h2

@[autograded 2]
theorem exercise_4_3_5_2 : ∃! n : ℕ, ∀ a : ℕ, n ≤ a := by
  use 0
  constructor
  · intro a
    exact Nat.zero_le a
  · intro m hm
    apply le_antisymm
    · exact hm 0
    · exact Nat.zero_le m

@[autograded 6]
theorem unique_inv {G : Type*} [Group G] (e : G)
(hId : ∀ a : G, e * a = a ∧ a * e = a)
(hInv : ∀ a : G, ∃ b : G, a * b = e ∧ b * a = e)
(hAssoc : ∀ a b c : G, (a * b) * c = a * (b * c))
: ∀ a : G, ∃! b : G, a * b = e ∧ b * a = e := by
  intro a
  obtain ⟨b, hb⟩ := hInv a
  use b
  constructor
  · exact hb
  · intro c hc
    have h1 : e * c = c := (hId c).1
    have h2 : b * a = e := hb.2
    calc
      c = e * c := by rw [h1]
      _ = (b * a) * c := by rw [h2]
      _ = b * (a * c) := by rw [hAssoc]
      _ = b * e := by rw [hc.1]
      _ = b := by rw [(hId b).2]
