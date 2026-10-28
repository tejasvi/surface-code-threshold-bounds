import QECCountComp.Kern2
import QEC.Count.CertSoundK

/-!
# Kernel route, version 2: the chunk lemmas

The checks of `QECCountComp/Kern2.lean` give the hypotheses of `box_bound_of_certK` (`FinalK.lean`):

* `allE_iff`: `allE f t` is `f` at every entry of `t.toList` (rows, from facts per subtree combined with `allE_node`);
* `startOKK_of_totK`: the start-sum bound computed from the structural totals `totK` (combined with `totK_node`)
  is `startOKK`;
* `dfsOKK_of_prefixes`: start completeness from the checks of all prefixes of `d` candidate steps.
-/

namespace QEC

open QECComp

theorem allE_iff {f : ℕ × ℕ × ℕ → Bool} {t : KTree} : t.allE f = true ↔ ∀ e ∈ t.toList, f e = true := by
  induction t with
  | leaf => simp [KTree.allE, KTree.toList]
  | node l k h m r ihl ihr =>
    simp only [KTree.allE, KTree.toList, Bool.and_eq_true, ihl, ihr, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨hl, hk⟩, hr⟩ e he
      rcases he with he | he | he
      · exact hl e he
      · rw [he]; exact hk
      · exact hr e he
    · intro hall
      exact ⟨⟨fun e he => hall e (Or.inl he), hall _ (Or.inr (Or.inl rfl))⟩,
        fun e he => hall e (Or.inr (Or.inr he))⟩

theorem allE_node {f : ℕ × ℕ × ℕ → Bool} {l r : KTree} {k h m : ℕ} :
    (KTree.node l k h m r).allE f = ((l.allE f && f (k, h, m)) && r.allE f) := rfl

theorem totK_node (P : Params) (l r : KTree) (k h m : ℕ) :
    totK P (KTree.node l k h m r) =
      addL (totK P l) (addL ((List.replicate (P.K + 1) 0).set (nCOf P.n P.K k) h) (totK P r)) := rfl

namespace ChunksK3

theorem addL_getD : ∀ (xs ys : List ℕ) (c : ℕ), (addL xs ys).getD c 0 = xs.getD c 0 + ys.getD c 0
  | [], ys, c => by simp [addL]
  | x :: xs, [], c => by
    rw [addL.eq_2 (x :: xs) (by simp)]
    simp
  | x :: xs, y :: ys, c => by
    rw [addL.eq_3]
    cases c with
    | zero => simp
    | succ c => simpa using addL_getD xs ys c

theorem addL_length : ∀ (xs ys : List ℕ), (addL xs ys).length = max xs.length ys.length
  | [], ys => by simp [addL]
  | x :: xs, [] => by
    rw [addL.eq_2 (x :: xs) (by simp)]
    simp
  | x :: xs, y :: ys => by
    rw [addL.eq_3]
    simp [addL_length xs ys, Nat.succ_max_succ]

/-- The totals of a tree are the sums over its entries. -/
theorem totK_spec (P : Params) : ∀ t : KTree, (totK P t).length = P.K + 1 ∧
    ∀ c ≤ P.K, (totK P t).getD c 0 =
      ((t.toList.filter (fun e => decide (nCOf P.n P.K e.1 = c))).map (fun e => e.2.1)).sum
  | .leaf => by
    refine ⟨by simp [totK], fun c hc => ?_⟩
    simp only [totK, KTree.toList, List.filter_nil, List.map_nil, List.sum_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  | .node l k h m r => by
    obtain ⟨hl1, hl2⟩ := totK_spec P l
    obtain ⟨hr1, hr2⟩ := totK_spec P r
    have hk := nCOf_le P.n P.K k
    refine ⟨?_, fun c hc => ?_⟩
    · rw [totK_node, addL_length, addL_length, List.length_set, List.length_replicate, hl1, hr1]
      simp
    · rw [totK_node, addL_getD, addL_getD, hl2 c hc, hr2 c hc]
      have hs : ((List.replicate (P.K + 1) 0).set (nCOf P.n P.K k) h).getD c 0 =
          if nCOf P.n P.K k = c then h else 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hkc : nCOf P.n P.K k = c
        · rw [if_pos hkc, if_pos (by rw [List.length_replicate]; omega), if_pos hkc]
          rfl
        · rw [if_neg hkc, if_neg hkc, List.getElem?_replicate, if_pos (by omega)]
          rfl
      rw [hs]
      simp only [KTree.toList, List.filter_append, List.filter_cons, List.map_append, List.sum_append]
      by_cases hkc : nCOf P.n P.K k = c
      · simp [hkc]
      · simp [hkc]

end ChunksK3

theorem startOKK_of_totK {P : Params} {t : KTree} (h : startOK2 P (totK P t) = true) : startOKK P t = true := by
  have hfold := CertSoundK.foldl_setAddL (fun e : ℕ × ℕ × ℕ => nCOf P.n P.K e.1) (fun e => e.2.1) P.K
    (fun e => nCOf_le P.n P.K e.1) t.toList (List.replicate (P.K + 1) 0) (by simp)
  obtain ⟨_, htot⟩ := ChunksK3.totK_spec P t
  have heq : ∀ c ≤ P.K,
      (t.toList.foldl (fun (acc : List ℕ) e =>
        acc.set (nCOf P.n P.K e.1) (acc.getD (nCOf P.n P.K e.1) 0 + e.2.1)) (List.replicate (P.K + 1) 0)).getD c 0 =
        (totK P t).getD c 0 := by
    intro c hc
    rw [hfold.2 c hc, htot c hc]
    have h0 : (List.replicate (P.K + 1) 0).getD c 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    rw [h0, Nat.zero_add]
  have hS : List.foldl (fun acc c => acc + (List.foldl (fun (acc : List ℕ) e =>
        acc.set (nCOf P.n P.K e.1) (acc.getD (nCOf P.n P.K e.1) 0 + e.2.1)) (List.replicate (P.K + 1) 0)
          t.toList).getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c) 0 (List.range (P.K + 1)) =
      List.foldl (fun acc c => acc + (totK P t).getD c 0 * P.wE ^ (P.K - c) * P.wC ^ c) 0
        (List.range (P.K + 1)) := by
    apply List.foldl_ext
    intro acc c hc
    rw [heq c (by have := List.mem_range.mp hc; omega)]
  unfold startOK2 at h
  unfold startOKK
  dsimp only at h ⊢
  rw [hS]
  exact h

theorem dfsOKK_of_prefixes_aux {P : Params} {t : KTree} :
    ∀ (d : ℕ) (pfx : List (ℕ × Bool)), pfx.length + d ≤ P.K →
      (∀ js : List ℕ, js.length = d → (∀ j ∈ js, j < (candList P.n).length) → dfsPreK P t js pfx = true) →
        dfsOKK P t (P.K - pfx.length) pfx = true
  | 0, pfx, _, h => by
    have := h [] rfl (by simp)
    simpa [dfsPreK] using this
  | d + 1, pfx, hd, h => by
    obtain ⟨r, hr⟩ : ∃ r, P.K - pfx.length = r + 1 := ⟨P.K - pfx.length - 1, by omega⟩
    rw [hr]
    simp only [dfsOKK, List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hc : (!selfAvoid P.n (pfx ++ [(candList P.n)[j]]) ||
        exclEndingK P (pfx ++ [(candList P.n)[j]])) = true
    · rw [hc]
      rfl
    · have hrec := dfsOKK_of_prefixes_aux (P := P) (t := t) d (pfx ++ [(candList P.n)[j]]) (by simp; omega)
        (fun js hjs hjv => by
          have hh := h (j :: js) (by simp [hjs]) (by
            intro j' hj'
            rcases List.mem_cons.mp hj' with rfl | h'
            · exact hj
            · exact hjv j' h')
          simp only [dfsPreK, List.getElem?_eq_getElem hj] at hh
          rw [Bool.eq_false_iff.mpr hc, Bool.false_or] at hh
          exact hh)
      have hlen : P.K - (pfx ++ [(candList P.n)[j]]).length = r := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hlen] at hrec
      rw [Bool.eq_false_iff.mpr hc, Bool.false_or]
      exact hrec

theorem dfsOKK_of_prefixes {P : Params} {t : KTree} {d : ℕ} (hd : d ≤ P.K)
    (h : ∀ js : List ℕ, js.length = d → (∀ j ∈ js, j < (candList P.n).length) → dfsPreK P t js [] = true) :
    dfsOKK P t P.K [] = true := by
  have := dfsOKK_of_prefixes_aux d [] (by simpa using hd) h
  simpa using this

end QEC
