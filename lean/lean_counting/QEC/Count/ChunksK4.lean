import QEC.Count.ChunksK3

/-!
# Kernel route, version 2: one more level of start-completeness prefixes

`dfsPreK_split1`: the start check for the walks that begin with the candidate steps `js` follows from the checks for
the walks that begin with `js ++ [j]`, for every candidate index `j`. So the prefixes of the start-completeness check
can be refined where a chunk is too large, and the facts assembled back level by level.
-/

namespace QEC

open QECComp

namespace ChunksK4

theorem dfsPreK_split1_aux {P : Params} {t : KTree} :
    ∀ (js : List ℕ) (pfx : List (ℕ × Bool)), pfx.length + js.length < P.K →
      (∀ j < (candList P.n).length, dfsPreK P t (js ++ [j]) pfx = true) → dfsPreK P t js pfx = true
  | [], pfx, hlen, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 :=
      ⟨P.K - pfx.length - 1, by simp only [List.length_nil, Nat.add_zero] at hlen; omega⟩
    simp only [dfsPreK]
    rw [hr]
    simp only [dfsOKK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hh := h j hj
    simp only [List.nil_append, dfsPreK, List.getElem?_eq_getElem hj] at hh
    have hlen' : P.K - (pfx ++ [(candList P.n)[j]]).length = r := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hlen'] at hh
    exact hh
  | j0 :: js, pfx, hlen, h => by
    cases hc : (candList P.n)[j0]? with
    | none => simp [dfsPreK, hc]
    | some x =>
      simp only [dfsPreK, hc]
      by_cases hb : (!selfAvoid P.n (pfx ++ [x]) || exclEndingK P (pfx ++ [x])) = true
      · rw [hb]
        rfl
      · rw [Bool.eq_false_iff.mpr hb, Bool.false_or]
        apply dfsPreK_split1_aux js (pfx ++ [x])
          (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
        intro j hj
        have hh := h j hj
        simp only [List.cons_append, dfsPreK, hc] at hh
        rw [Bool.eq_false_iff.mpr hb, Bool.false_or] at hh
        exact hh

end ChunksK4

theorem dfsPreK_split1 {P : Params} {t : KTree} {js : List ℕ} (hlen : js.length < P.K)
    (h : ∀ j < (candList P.n).length, dfsPreK P t (js ++ [j]) [] = true) : dfsPreK P t js [] = true :=
  ChunksK4.dfsPreK_split1_aux js [] (by simpa using hlen) h

end QEC
