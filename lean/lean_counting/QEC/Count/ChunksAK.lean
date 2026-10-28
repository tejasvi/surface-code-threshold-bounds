import QEC.Count.ChunksK4
import QECCountComp.KernA

/-!
# Kernel route for the augmented certificates: chunks of the start-completeness check

* `dfsPreAK_split1`: the start check from the height `h0` for the walks that begin with the candidate steps `js` follows
  from the checks for the walks that begin with `js ++ [j]`, for every candidate index `j`;
* `dfsAK_of_prefixes`: start completeness from the height `h0` from the checks of all prefixes of `D` candidate steps.

These are `dfsPreK_split1` and `dfsOKK_of_prefixes` of the box route for `dfsPreAK`, `dfsAK`, whose disjuncts are
`!selfAvoid`, `height < 0`, the extension, and the exclusion search, in this order.
-/

namespace QEC

open QECComp

namespace ChunksAK

theorem dfsPreAK_split1_aux {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {h0 : ℤ} :
    ∀ (js : List ℕ) (pfx : List (ℕ × Bool)), pfx.length + js.length < P.K →
      (∀ j < (candList 2).length, dfsPreAK P fN fB h0 (js ++ [j]) pfx = true) →
        dfsPreAK P fN fB h0 js pfx = true
  | [], pfx, hlen, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 :=
      ⟨P.K - pfx.length - 1, by simp only [List.length_nil, Nat.add_zero] at hlen; omega⟩
    simp only [dfsPreAK]
    rw [hr]
    simp only [dfsAK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hh := h j hj
    simp only [List.nil_append, dfsPreAK, List.getElem?_eq_getElem hj] at hh
    have hlen' : P.K - (pfx ++ [(candList 2)[j]]).length = r := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hlen'] at hh
    exact hh
  | j0 :: js, pfx, hlen, h => by
    cases hc : (candList 2)[j0]? with
    | none => simp [dfsPreAK, hc]
    | some x =>
      simp only [dfsPreAK, hc]
      by_cases hab : (!selfAvoid 2 (pfx ++ [x]) || decide (h0 - vdisp (pfx ++ [x]) < 0)) = true
      · rw [hab]
        rfl
      · by_cases hex : exclEndingAK P h0 (pfx ++ [x]) = true
        · rw [hex, Bool.or_true]
        · rw [Bool.eq_false_iff.mpr hab, Bool.eq_false_iff.mpr hex, Bool.false_or, Bool.or_false]
          apply dfsPreAK_split1_aux js (pfx ++ [x])
            (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
          intro j hj
          have hh := h j hj
          simp only [List.cons_append, dfsPreAK, hc] at hh
          rw [Bool.eq_false_iff.mpr hab, Bool.eq_false_iff.mpr hex, Bool.false_or, Bool.or_false] at hh
          exact hh

theorem dfsAK_of_prefixes_aux {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {h0 : ℤ} :
    ∀ (d : ℕ) (pfx : List (ℕ × Bool)), pfx.length + d ≤ P.K →
      (∀ js : List ℕ, js.length = d → (∀ j ∈ js, j < (candList 2).length) →
        dfsPreAK P fN fB h0 js pfx = true) →
        dfsAK P fN fB h0 (P.K - pfx.length) pfx = true
  | 0, pfx, _, h => by
    have := h [] rfl (by simp)
    simpa [dfsPreAK] using this
  | d + 1, pfx, hd, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 := ⟨P.K - pfx.length - 1, by omega⟩
    rw [hr]
    simp only [dfsAK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hab : (!selfAvoid 2 (pfx ++ [(candList 2)[j]]) ||
        decide (h0 - vdisp (pfx ++ [(candList 2)[j]]) < 0)) = true
    · rw [hab]
      rfl
    · by_cases hex : exclEndingAK P h0 (pfx ++ [(candList 2)[j]]) = true
      · rw [hex, Bool.or_true]
      · have hrec := dfsAK_of_prefixes_aux (P := P) (fN := fN) (fB := fB) (h0 := h0) d
          (pfx ++ [(candList 2)[j]]) (by simp only [List.length_append, List.length_singleton]; omega)
          (fun js hjs hjv => by
            have hh := h (j :: js) (by simp [hjs]) (by
              intro j' hj'
              rcases List.mem_cons.mp hj' with rfl | h'
              · exact hj
              · exact hjv j' h')
            simp only [dfsPreAK, List.getElem?_eq_getElem hj] at hh
            rw [Bool.eq_false_iff.mpr hab, Bool.eq_false_iff.mpr hex, Bool.false_or, Bool.or_false] at hh
            exact hh)
        have hlen : P.K - (pfx ++ [(candList 2)[j]]).length = r := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [hlen] at hrec
        rw [Bool.eq_false_iff.mpr hab, Bool.eq_false_iff.mpr hex, Bool.false_or, Bool.or_false]
        exact hrec

end ChunksAK

theorem dfsPreAK_split1 {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {h0 : ℤ} {js : List ℕ} (hlen : js.length < P.K)
    (h : ∀ j < (candList 2).length, dfsPreAK P fN fB h0 (js ++ [j]) [] = true) :
    dfsPreAK P fN fB h0 js [] = true :=
  ChunksAK.dfsPreAK_split1_aux js [] (by simpa using hlen) h

theorem dfsAK_of_prefixes {P : ParamsA} {fN fB : ℕ → Option (ℕ × ℕ)} {h0 : ℤ} (D : ℕ) (hD : D ≤ P.K)
    (h : ∀ js : List ℕ, js.length = D → (∀ j ∈ js, j < (candList 2).length) →
      dfsPreAK P fN fB h0 js [] = true) :
    dfsAK P fN fB h0 P.K [] = true := by
  have := ChunksAK.dfsAK_of_prefixes_aux D [] (by simpa using hD) h
  simpa using this

end QEC
