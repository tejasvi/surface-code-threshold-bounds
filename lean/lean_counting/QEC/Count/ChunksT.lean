import QECCountComp.SeamC
import Mathlib.Tactic.Linarith

/-!
# Assembling the chunked checks of a seam certificate

The near and bulk rows are checked in ranges of entries, the start completeness and the start sums in ranges of
offsets (`rangeAllT`). These lemmas put the chunks together.
-/

namespace QEC

open QECComp

theorem range'_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
  have h := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
  rw [show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
  exact h.symm

theorem nearRowsOK_append {P : ParamsT} {nk nG bk bH : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : nearRowsOK P nk nG bk bH a b = true) (h2 : nearRowsOK P nk nG bk bH b c = true) :
    nearRowsOK P nk nG bk bH a c = true := by
  unfold nearRowsOK at *
  rw [range'_split hab hbc, List.all_append, h1, h2]
  rfl

theorem bulkRowsOK_append {P : ParamsT} {nk nG bk bH : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : bulkRowsOK P nk nG bk bH a b = true) (h2 : bulkRowsOK P nk nG bk bH b c = true) :
    bulkRowsOK P nk nG bk bH a c = true := by
  unfold bulkRowsOK at *
  rw [range'_split hab hbc, List.all_append, h1, h2]
  rfl

theorem rangeAllT_append {lo : ℤ} {c1 c2 : ℕ} {f : ℤ → Bool} (h1 : rangeAllT lo c1 f = true)
    (h2 : rangeAllT (lo + c1) c2 f = true) : rangeAllT lo (c1 + c2) f = true := by
  unfold rangeAllT at *
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

theorem rangeAllT_append' {lo lo2 : ℤ} {c1 c2 : ℕ} {f : ℤ → Bool} (h1 : rangeAllT lo c1 f = true)
    (h2 : rangeAllT lo2 c2 f = true) (he : lo2 = lo + c1) : rangeAllT lo (c1 + c2) f = true :=
  rangeAllT_append h1 (he ▸ h2)

end QEC
