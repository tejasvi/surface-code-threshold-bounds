import QECCountComp.Kern
import Mathlib.Tactic.Linarith

/-!
# Start completeness of the kernel route in chunks of two first steps

`dfsTop2K P t j1 j2` covers the walks that begin with the candidate steps `j1`, `j2`; together they give
`dfsOKK P t P.K []` (for `K ≥ 2`).
-/

namespace QEC

open QECComp

theorem dfsOKK_of_tops2 {P : Params} {t : KTree} (hK : 2 ≤ P.K)
    (h : ∀ j1 < (candList P.n).length, ∀ j2 < (candList P.n).length, dfsTop2K P t j1 j2 = true) :
    dfsOKK P t P.K [] = true := by
  obtain ⟨r, hr⟩ : ∃ r, P.K = r + 2 := ⟨P.K - 2, by omega⟩
  rw [hr]
  simp only [dfsOKK, List.nil_append, List.all_eq_true]
  intro x1 hx1
  obtain ⟨j1, hj1, rfl⟩ := List.getElem_of_mem hx1
  by_cases hsa : selfAvoid P.n [(candList P.n)[j1]] = true
  · by_cases hee : exclEndingK P [(candList P.n)[j1]] = true
    · simp [hee]
    · simp only [hsa, hee, Bool.not_true, Bool.false_or, dfsOKK, List.all_eq_true, List.singleton_append]
      intro x2 hx2
      obtain ⟨j2, hj2, rfl⟩ := List.getElem_of_mem hx2
      have := h j1 hj1 j2 hj2
      simp only [dfsTop2K, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2, hsa, hee, hr,
        Bool.not_true, Bool.false_or, Nat.add_sub_cancel] at this
      exact this
  · simp [hsa]

end QEC
