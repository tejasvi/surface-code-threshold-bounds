import QEC.Count.ChunksT
import QECCountComp.AugC

/-!
# Assembling the chunked checks of an augmented certificate

The near, interface and bulk rows are checked in ranges of entries, the start completeness in ranges of first-vertex
heights (`rangeAllA`) or, per height, in ranges of first steps (`dfsTopA`). These lemmas put the chunks together
(as `ChunksT.lean` does for the seam certificates).
-/

namespace QEC

open QECComp

theorem nearRowsOKA_append {P : ParamsA} {nk nG bk bH : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : nearRowsOKA P nk nG bk bH a b = true) (h2 : nearRowsOKA P nk nG bk bH b c = true) :
    nearRowsOKA P nk nG bk bH a c = true := by
  unfold nearRowsOKA at *
  rw [range'_split hab hbc, List.all_append, h1, h2]
  rfl

theorem ifRowsOKA_append {P : ParamsA} {nk nG bk bH : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : ifRowsOKA P nk nG bk bH a b = true) (h2 : ifRowsOKA P nk nG bk bH b c = true) :
    ifRowsOKA P nk nG bk bH a c = true := by
  unfold ifRowsOKA at *
  rw [range'_split hab hbc, List.all_append, h1, h2]
  rfl

theorem bulkRowsOKA_append {P : ParamsA} {nk nG bk bH : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : bulkRowsOKA P nk nG bk bH a b = true) (h2 : bulkRowsOKA P nk nG bk bH b c = true) :
    bulkRowsOKA P nk nG bk bH a c = true := by
  unfold bulkRowsOKA at *
  rw [range'_split hab hbc, List.all_append, h1, h2]
  rfl

theorem rangeAllA_append {lo : ℤ} {c1 c2 : ℕ} {f : ℤ → Bool} (h1 : rangeAllA lo c1 f = true)
    (h2 : rangeAllA (lo + c1) c2 f = true) : rangeAllA lo (c1 + c2) f = true := by
  unfold rangeAllA at *
  rw [List.all_eq_true] at *
  intro i hi
  rcases Nat.lt_or_ge i c1 with h | h
  · exact h1 i (List.mem_range.mpr h)
  · have hi' : i - c1 < c2 := by
      have := List.mem_range.mp hi
      omega
    have := h2 (i - c1) (List.mem_range.mpr hi')
    have e : lo + (c1 : ℤ) + ((i - c1 : ℕ) : ℤ) = lo + (i : ℤ) := by omega
    rw [e] at this
    exact this

theorem rangeAllA_append' {lo lo2 : ℤ} {c1 c2 : ℕ} {f : ℤ → Bool} (h1 : rangeAllA lo c1 f = true)
    (h2 : rangeAllA lo2 c2 f = true) (he : lo2 = lo + c1) : rangeAllA lo (c1 + c2) f = true :=
  rangeAllA_append h1 (he ▸ h2)

/-- One height. -/
theorem rangeAllA_one {lo : ℤ} {f : ℤ → Bool} (h : f lo = true) : rangeAllA lo 1 f = true := by
  unfold rangeAllA
  simp [h]

/-- Consecutive ranges of first steps. -/
theorem all_range'_append {f : ℕ → Bool} {a n m : ℕ} (h1 : (List.range' a n).all f = true)
    (h2 : (List.range' (a + n) m).all f = true) : (List.range' a (n + m)).all f = true := by
  rw [List.range'_append_1.symm, List.all_append, h1, h2]
  rfl

/-- Start completeness from one height is the check of its 8 first steps. -/
theorem dfsHA_eq_all (P : ParamsA) (nk nG bk bH : Array ℕ) (h0 : ℤ) :
    dfsHA P nk nG bk bH h0 = (List.range' 0 8).all (dfsTopA P nk nG bk bH h0) := by
  unfold dfsHA
  rw [List.range_eq_range']
  rfl

end QEC
