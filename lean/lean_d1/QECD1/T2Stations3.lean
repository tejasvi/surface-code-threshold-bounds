import QECD1.T2Lam3

/-!
# The stations of a T2 path (3D)

The 3D analogue of the station part of the 2D `TwoD/T2Count`.

* `T1ev3`: some family has a block in each strip (the T1 event).
* `ends_ne3`: without T1, the two ends of a T2 path are distinct nodes.
* `no_adj_nonchk3`: without T1, no two adjacent nodes of a T2 path are both non-checks: families are not adjacent to
  each other, the two boundaries are not adjacent, and a family adjacent to a boundary has a block in that strip, so it
  would be the other end, a T1 family.
* `t2_stations3`: the stations of a T2 path (its end nodes and its intermediate families), their entry and exit
  checks, with at least one check between consecutive stations: the indexing of `metric_stations3`.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **The T1 event**: some family has a block in each strip. -/
def T1ev3 (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : Prop :=
  ∃ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
    (∃ c ∈ Fm, c.2.2 ≤ hs3) ∧ ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3

/-- Without T1, the two ends of a T2 path are distinct nodes. -/
theorem ends_ne3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} (hT1 : ¬ S.T1ev3 ny E) {x y : GNode3 T w h}
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y) :
    x ≠ y := by
  rintro rfl
  rcases x with u | b | F
  · rcases hx with hc | hc
    · exact absurd hc (by simp)
    · exact hc
  · rcases hx with hc | hc
    · rcases hy with hc' | hc'
      · rw [hc] at hc'
        exact absurd hc' (by simp)
      · exact hc'
    · exact hc
  · rcases hx with hc | ⟨hF, c1, hc1, hr1⟩
    · exact absurd hc (by simp)
    · rcases hy with hc' | ⟨-, c2, hc2, hr2⟩
      · exact absurd hc' (by simp)
      · exact hT1 ⟨F, hF, ⟨c1, hc1, hr1⟩, ⟨c2, hc2, hr2⟩⟩

/-- **No two adjacent non-check nodes** on a T2 path without T1. -/
theorem no_adj_nonchk3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2}
    (hT1 : ¬ S.T1ev3 ny E) {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y) (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    (hint : ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam3 ny E z)
    {z1 z2 : GNode3 T w h} (hz1 : z1 ∈ l) (hz2 : z2 ∈ l) (hadj : S.gadj3 Z ny E z1 z2)
    (h1 : ¬ isChk3 z1) (h2 : ¬ isChk3 z2) : False := by
  have key : ∀ {F : Finset V3} {b : Bool}, (.inr (.inr F) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) ∈ l → S.gadj3 Z ny E (.inr (.inr F)) (.inr (.inl b)) → False := by
    intro F b hF hb hg
    have hg0 : S.gadj0 Z ny E (.inr (.inr F)) (.inr (.inl b)) := by
      rcases hg with hg | hg
      · exact hg
      · rcases b with _ | _ <;> simp [gadj0] at hg
    rcases b with _ | _
    · obtain ⟨hFm, hpc⟩ := hg0
      obtain ⟨c1, hc1, hr1⟩ := S.strip_bot_of_pcls3 Z hFm hpc
      have hbx : (.inr (.inl false) : GNode3 T w h) = x := by
        rcases hbd false hb with hc | hc
        · exact hc
        · exfalso
          rcases hy with hc' | hc'
          · rw [← hc] at hc'
            simp at hc'
          · rw [← hc] at hc'
            exact hc'
      by_cases hFx : (.inr (.inr F) : GNode3 T w h) = x
      · rw [← hbx] at hFx
        simp at hFx
      by_cases hFy : (.inr (.inr F) : GNode3 T w h) = y
      · rw [← hFy] at hy
        rcases hy with hc' | ⟨-, c2, hc2, hr2⟩
        · simp at hc'
        · exact hT1 ⟨F, hFm, ⟨c1, hc1, hr1⟩, ⟨c2, hc2, hr2⟩⟩
      · obtain ⟨-, hall⟩ := hint _ hF hFx hFy
        have := (hall c1 hc1).1
        omega
    · obtain ⟨hFm, hpc⟩ := hg0
      obtain ⟨c2, hc2, hr2⟩ := S.strip_top_of_pclsT3 Z hh hFm hpc
      have hby : (.inr (.inl true) : GNode3 T w h) = y := by
        rcases hbd true hb with hc | hc
        · exfalso
          rcases hx with hc' | hc'
          · rw [← hc] at hc'
            simp at hc'
          · rw [← hc] at hc'
            exact hc'
        · exact hc
      by_cases hFy : (.inr (.inr F) : GNode3 T w h) = y
      · rw [← hby] at hFy
        simp at hFy
      by_cases hFx : (.inr (.inr F) : GNode3 T w h) = x
      · rw [← hFx] at hx
        rcases hx with hc' | ⟨-, c1, hc1, hr1⟩
        · simp at hc'
        · exact hT1 ⟨F, hFm, ⟨c1, hc1, hr1⟩, ⟨c2, hc2, hr2⟩⟩
      · obtain ⟨-, hall⟩ := hint _ hF hFx hFy
        have := (hall c2 hc2).2
        omega
  rcases z1 with u1 | b1 | F1
  · exact h1 ⟨u1, rfl⟩
  · rcases z2 with u2 | b2 | F2
    · exact h2 ⟨u2, rfl⟩
    · rcases hadj with hg | hg <;> rcases b1 with _ | _ <;> rcases b2 with _ | _ <;> simp [gadj0] at hg
    · exact key hz2 hz1 (Or.symm hadj)
  · rcases z2 with u2 | b2 | F2
    · exact h2 ⟨u2, rfl⟩
    · exact key hz1 hz2 hadj
    · exact S.not_gadj_fam_fam3 Z hadj

/-- **The stations of a T2 path** (the indexing of `metric_stations3`): positions `p 0 = 0 < p 1 < … < p (m+1) =
length - 1` of the end nodes and the intermediate families, the entry checks `u i` before and the exit checks `v i`
after them, with at least one check between consecutive stations. -/
theorem t2_stations3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2}
    (hT1 : ¬ S.T1ev3 ny E) {l : List (GNode3 T w h)} {x y : GNode3 T w h} (hhd : l.head? = some x)
    (hlst : l.getLast? = some y) (hnd : l.Nodup) (hch : List.IsChain (S.gadj3 Z ny E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    (hint : ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam3 ny E z) :
    ∃ (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → PVert3 T w h), 2 ≤ l.length ∧
      (∀ i j, i < j → j ≤ m + 1 → p i < p j) ∧ p 0 = 0 ∧ p (m + 1) = l.length - 1 ∧
      (∀ i, 1 ≤ i → i ≤ m → isFam3 (nd3 l (p i))) ∧
      (∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam3 (nd3 l k)) ∧
      (∀ i, 1 ≤ i → i ≤ m + 1 → nd3 l (p i - 1) = .inl (u i)) ∧
      (∀ i ≤ m, nd3 l (p i + 1) = .inl (v i)) ∧
      (∀ i ≤ m, p i + 1 < p (i + 1)) := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hx0 : nd3 l 0 = x := nd3_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hyl : nd3 l (l.length - 1) = y := nd3_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have hlen : 2 ≤ l.length := by
    by_contra hlt
    have hl1 : l.length = 1 := by
      have := List.length_pos_of_ne_nil hl
      omega
    apply S.ends_ne3 hT1 hx hy
    rw [← hx0, ← hyl, hl1]
  have hmem : ∀ k, k < l.length → nd3 l k ∈ l := by
    intro k hk
    rw [nd3_of_getElem? (List.getElem?_eq_getElem hk)]
    exact List.getElem_mem hk
  have hxnc : ¬ isChk3 x := by
    rintro ⟨u, rfl⟩
    rcases hx with hc | hc
    · simp at hc
    · exact hc
  have hync : ¬ isChk3 y := by
    rintro ⟨u, rfl⟩
    rcases hy with hc | hc
    · simp at hc
    · exact hc
  have hfnc : ∀ z : GNode3 T w h, isFam3 z → ¬ isChk3 z := by
    rintro z ⟨F, rfl⟩ ⟨u, hu⟩
    simp at hu
  -- the family positions strictly inside, and the stations
  set FP : List ℕ := (List.range l.length).filter
    (fun k => decide (0 < k ∧ k + 1 < l.length ∧ isFam3 (nd3 l k))) with hFP
  have hFPmem : ∀ k, k ∈ FP ↔ 0 < k ∧ k + 1 < l.length ∧ isFam3 (nd3 l k) := by
    intro k
    simp only [hFP, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hk⟩
      exact hk
    · intro hk
      exact ⟨by omega, hk⟩
  have hFPs : FP.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  set SL : List ℕ := 0 :: (FP ++ [l.length - 1]) with hSL
  have hSLs : SL.Pairwise (· < ·) := by
    rw [hSL, List.pairwise_cons, List.pairwise_append]
    refine ⟨fun a ha => ?_, hFPs, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact ((hFPmem a).1 ha).1
      · rw [List.mem_singleton.1 ha]
        omega
    · rw [List.mem_singleton.1 hb]
      have := ((hFPmem a).1 ha).2.1
      omega
  have hSLlen : SL.length = FP.length + 2 := by simp [hSL]
  set m := FP.length with hm
  set p : ℕ → ℕ := fun i => SL.getD i 0 with hpdef
  have hpget : ∀ i (hi : i < SL.length), p i = SL[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j := by
    intro i j hij hj
    rw [hpget i (by omega), hpget j (by omega)]
    exact List.pairwise_iff_getElem.1 hSLs i j (by omega) (by omega) hij
  have hpmono : ∀ i j, i ≤ j → j ≤ m + 1 → p i ≤ p j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with hc | hc
    · rw [hc]
    · exact (hp i j hc hj).le
  have hp0 : p 0 = 0 := by simp [hpdef, hSL]
  have hpl : p (m + 1) = l.length - 1 := by
    simp only [hpdef, hSL, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (le_of_eq rfl)]
    simp
  have hpin : ∀ i, 1 ≤ i → i ≤ m → p i ∈ FP := by
    intro i hi1 him
    have hpi : p i = FP[i - 1] := by
      simp only [hpdef, hSL]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
    rw [hpi]
    exact List.getElem_mem _
  have hFPp : ∀ k ∈ FP, ∃ i, 1 ≤ i ∧ i ≤ m ∧ p i = k := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hk
    refine ⟨j + 1, by omega, by omega, ?_⟩
    simp only [hpdef, hSL]
    rw [List.getD_cons_succ, List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj]
  have hpfam : ∀ i, 1 ≤ i → i ≤ m → isFam3 (nd3 l (p i)) :=
    fun i hi1 him => ((hFPmem _).1 (hpin i hi1 him)).2.2
  have hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam3 (nd3 l k) := by
    intro k hk hf
    by_cases hkl : k < l.length
    · by_cases hk0 : k = 0
      · exact hk 0 (Nat.zero_le _) (by rw [hk0, hp0])
      by_cases hkL : k = l.length - 1
      · exact hk (m + 1) le_rfl (by rw [hkL, hpl])
      obtain ⟨i, hi1, him, hi⟩ := hFPp k ((hFPmem k).2 ⟨by omega, by omega, hf⟩)
      exact hk i (by omega) hi.symm
    · obtain ⟨F, hF⟩ := hf
      simp [nd3, List.getElem?_eq_none (by omega : l.length ≤ k)] at hF
  -- nodes at stations are not checks
  have hstnc : ∀ i ≤ m + 1, ¬ isChk3 (nd3 l (p i)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hc | hc
    · rw [hc, hp0, hx0]
      exact hxnc
    · rcases eq_or_lt_of_le hi with hc' | hc'
      · rw [hc', hpl, hyl]
        exact hync
      · exact hfnc _ (hpfam i hc (by omega))
  have hplt : ∀ i ≤ m + 1, p i < l.length := by
    intro i hi
    have := hpmono i (m + 1) hi le_rfl
    rw [hpl] at this
    omega
  -- at least one check between consecutive stations
  have hgap : ∀ i ≤ m, p i + 1 < p (i + 1) := by
    intro i hi
    by_contra hng
    have hlt := hp i (i + 1) (by omega) (by omega)
    have heq : p (i + 1) = p i + 1 := by omega
    have hadj := chain_step hch (getElem?_nd3 (hplt i (by omega)))
      (by rw [← heq]; exact getElem?_nd3 (hplt (i + 1) (by omega)))
    exact S.no_adj_nonchk3 Z hh hT1 hy hx hbd hint (hmem _ (hplt i (by omega)))
      (hmem _ (hplt (i + 1) (by omega))) hadj (hstnc i (by omega)) (hstnc (i + 1) (by omega))
  -- positions strictly between consecutive stations hold checks
  have hbetween : ∀ i ≤ m, ∀ k, p i < k → k < p (i + 1) → isChk3 (nd3 l k) := by
    intro i hi k hk1 hk2
    have hkl : k < l.length := by
      have := hplt (i + 1) (by omega)
      omega
    have hns : ∀ j ≤ m + 1, k ≠ p j := by
      intro j hj hkj
      rw [hkj] at hk1 hk2
      by_cases hji : j ≤ i
      · have := hpmono j i hji (by omega)
        omega
      · have := hpmono (i + 1) j (by omega) hj
        omega
    rcases hz : nd3 l k with u | b | F
    · exact ⟨u, rfl⟩
    · exfalso
      have hbmem : (.inr (.inl b) : GNode3 T w h) ∈ l := by
        rw [← hz]
        exact hmem k hkl
      rcases hbd b hbmem with hc | hc
      · rw [← hz, ← hx0, nd3_eq_iff hnd hkl (by omega)] at hc
        exact hns 0 (Nat.zero_le _) (by rw [hc, hp0])
      · rw [← hz, ← hyl, nd3_eq_iff hnd hkl (by omega)] at hc
        exact hns (m + 1) le_rfl (by rw [hc, hpl])
    · exact absurd ⟨F, hz⟩ (hnofam k hns)
  refine ⟨m, p, fun i => gchk3 (nd3 l (p i - 1)), fun i => gchk3 (nd3 l (p i + 1)), hlen, hp, hp0, hpl, hpfam,
    hnofam, fun i hi1 him => ?_, fun i hi => ?_, hgap⟩
  · have hg := hgap (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at hg
    exact nd3_isChk (hbetween (i - 1) (by omega) _ (by omega) (by rw [show i - 1 + 1 = i by omega]; omega))
  · exact nd3_isChk (hbetween i hi _ (by omega) (hgap i hi))

end Stage13

end QECD1
