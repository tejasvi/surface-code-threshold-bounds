import QECCountComp.Load
import Mathlib.Tactic.Linarith

/-!
# Assembling the chunked checks

The rows are checked in ranges of states (`rowsOK P keys Hs lo hi`), and the start completeness by the first step
(`dfsTop P keys j`). These lemmas put the chunks together.
-/

namespace QEC

open QECComp

theorem rowsOK_append {P : Params} {keys Hs : Array ℕ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : rowsOK P keys Hs a b = true) (h2 : rowsOK P keys Hs b c = true) : rowsOK P keys Hs a c = true := by
  unfold rowsOK at *
  have : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    have h := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
    rw [show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
    exact h.symm
  rw [this, List.all_append, h1, h2]
  rfl

theorem rowCheck_of_rowsOK {P : Params} {keys Hs : Array ℕ} {hi : ℕ} (h : rowsOK P keys Hs 0 hi = true) :
    ∀ i < hi, rowCheck P keys Hs i = true := by
  intro i hi'
  unfold rowsOK at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)

theorem dfsOK_of_tops {P : Params} {keys : Array ℕ} (hK : 1 ≤ P.K)
    (h : ∀ j < (candList P.n).length, dfsTop P keys j = true) : dfsOK P keys P.K [] = true := by
  obtain ⟨r, hr⟩ : ∃ r, P.K = r + 1 := ⟨P.K - 1, by omega⟩
  rw [hr]
  simp only [dfsOK, List.nil_append, List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h j hj
  simp only [dfsTop, List.getElem?_eq_getElem hj, hr, Nat.add_sub_cancel] at this
  exact this

end QEC
