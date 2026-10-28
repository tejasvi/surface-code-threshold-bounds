import QEC.Count.ChunksK4
import QECCountComp.KernT

/-!
# Kernel route for the seam certificates: the chunk lemmas

The checks of `QECCountComp/KernT.lean` are assembled from per-chunk facts:

* `sumL_append`, `totTK_eq`: the structural totals `totTK f t` (combined over the named internal nodes with `addL`) are
  the pointwise sums `sumL` of the contributions of the entries of `t.toList`;
* `dfsPreTK_split1`: the start check for the walks that begin with the candidate steps `js` follows from the checks for
  the walks that begin with `js ++ [j]`, for every candidate index `j`;
* `dfsTK_of_prefixes`: start completeness from one offset, from the checks of all prefixes of `D` candidate steps.

`dfsTK` and `dfsPreTK` try the extension before the exclusion search (`(a || b) || c` instead of `(a || c) || b`);
the proofs split on the two outer disjuncts.
-/

namespace QEC

open QECComp

namespace ChunksTK

theorem addL_nil_right : ∀ xs : List ℕ, addL xs [] = xs
  | [] => by simp [addL]
  | x :: xs => addL.eq_2 (x :: xs) (by simp)

theorem addL_cons_cons (x y : ℕ) (xs ys : List ℕ) : addL (x :: xs) (y :: ys) = (x + y) :: addL xs ys :=
  addL.eq_3 x xs y ys

theorem addL_assoc : ∀ xs ys zs : List ℕ, addL (addL xs ys) zs = addL xs (addL ys zs)
  | [], ys, zs => by simp [addL]
  | x :: xs, [], zs => by
    rw [addL_nil_right]
    simp [addL]
  | x :: xs, y :: ys, [] => by
    rw [addL_nil_right, addL_nil_right]
  | x :: xs, y :: ys, z :: zs => by
    rw [addL_cons_cons, addL_cons_cons, addL_cons_cons, addL_cons_cons, addL_assoc xs ys zs, Nat.add_assoc]

end ChunksTK

theorem sumL_append (a b : List (List ℕ)) : sumL (a ++ b) = addL (sumL a) (sumL b) := by
  induction a with
  | nil => simp [sumL, addL]
  | cons x xs ih =>
    rw [List.cons_append, sumL, sumL, ih, ChunksTK.addL_assoc]

theorem totTK_eq (f : ℕ × ℕ × ℕ → List ℕ) (t : KTree) : totTK f t = sumL (t.toList.map f) := by
  induction t with
  | leaf => simp [totTK, KTree.toList, sumL]
  | node l k h m r ihl ihr =>
    rw [totTK, KTree.toList, List.map_append, List.map_cons, sumL_append, sumL, ihl, ihr]

namespace ChunksTK

theorem dfsPreTK_split1_aux {P : ParamsT} {fN fB : ℕ → Option (ℕ × ℕ)} {o0 : ℤ} :
    ∀ (js : List ℕ) (pfx : List (ℕ × Bool)), pfx.length + js.length < P.K →
      (∀ j < (candList 2).length, dfsPreTK P fN fB o0 (js ++ [j]) pfx = true) → dfsPreTK P fN fB o0 js pfx = true
  | [], pfx, hlen, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 :=
      ⟨P.K - pfx.length - 1, by simp only [List.length_nil, Nat.add_zero] at hlen; omega⟩
    simp only [dfsPreTK]
    rw [hr]
    simp only [dfsTK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hh := h j hj
    simp only [List.nil_append, dfsPreTK, List.getElem?_eq_getElem hj] at hh
    have hlen' : P.K - (pfx ++ [(candList 2)[j]]).length = r := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [hlen'] at hh
    exact hh
  | j0 :: js, pfx, hlen, h => by
    cases hc : (candList 2)[j0]? with
    | none => simp [dfsPreTK, hc]
    | some x =>
      simp only [dfsPreTK, hc]
      cases ha : (!selfAvoid 2 (pfx ++ [x])) with
      | true => simp
      | false =>
        cases hx : exclEndingTK P o0 (pfx ++ [x]) with
        | true => simp
        | false =>
          simp only [Bool.false_or, Bool.or_false]
          apply dfsPreTK_split1_aux js (pfx ++ [x])
            (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
          intro j hj
          have hh := h j hj
          simp only [List.cons_append, dfsPreTK, hc, ha, hx, Bool.false_or, Bool.or_false] at hh
          exact hh

theorem dfsTK_of_prefixes_aux {P : ParamsT} {fN fB : ℕ → Option (ℕ × ℕ)} {o0 : ℤ} :
    ∀ (d : ℕ) (pfx : List (ℕ × Bool)), pfx.length + d ≤ P.K →
      (∀ js : List ℕ, js.length = d → (∀ j ∈ js, j < (candList 2).length) → dfsPreTK P fN fB o0 js pfx = true) →
        dfsTK P fN fB o0 (P.K - pfx.length) pfx = true
  | 0, pfx, _, h => by
    have := h [] rfl (by simp)
    simpa [dfsPreTK] using this
  | d + 1, pfx, hd, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 := ⟨P.K - pfx.length - 1, by omega⟩
    rw [hr]
    simp only [dfsTK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    cases ha : (!selfAvoid 2 (pfx ++ [(candList 2)[j]])) with
    | true => simp
    | false =>
      cases hx : exclEndingTK P o0 (pfx ++ [(candList 2)[j]]) with
      | true => simp
      | false =>
        simp only [Bool.false_or, Bool.or_false]
        have hrec := dfsTK_of_prefixes_aux (P := P) (fN := fN) (fB := fB) (o0 := o0) d
          (pfx ++ [(candList 2)[j]]) (by simp; omega)
          (fun js hjs hjv => by
            have hh := h (j :: js) (by simp [hjs]) (by
              intro j' hj'
              rcases List.mem_cons.mp hj' with rfl | h'
              · exact hj
              · exact hjv j' h')
            simp only [dfsPreTK, List.getElem?_eq_getElem hj, ha, hx, Bool.false_or, Bool.or_false] at hh
            exact hh)
        have hlen : P.K - (pfx ++ [(candList 2)[j]]).length = r := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [hlen] at hrec
        exact hrec

end ChunksTK

theorem dfsPreTK_split1 {P : ParamsT} {fN fB : ℕ → Option (ℕ × ℕ)} {o0 : ℤ} {js : List ℕ}
    (hlen : js.length < P.K)
    (h : ∀ j < (candList 2).length, dfsPreTK P fN fB o0 (js ++ [j]) [] = true) :
    dfsPreTK P fN fB o0 js [] = true :=
  ChunksTK.dfsPreTK_split1_aux js [] (by simpa using hlen) h

theorem dfsTK_of_prefixes {P : ParamsT} {fN fB : ℕ → Option (ℕ × ℕ)} {o0 : ℤ} (D : ℕ) (hD : D ≤ P.K)
    (h : ∀ js : List ℕ, js.length = D → (∀ j ∈ js, j < (candList 2).length) →
      dfsPreTK P fN fB o0 js [] = true) :
    dfsTK P fN fB o0 P.K [] = true := by
  have := ChunksTK.dfsTK_of_prefixes_aux D [] (by simpa using hD) h
  simpa using this

end QEC

#print axioms QEC.totTK_eq
#print axioms QEC.dfsPreTK_split1
#print axioms QEC.dfsTK_of_prefixes
#print axioms QEC.sumL_append
