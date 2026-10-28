import QEC.Count.AugDefs
import QEC.Count.RotSound

/-!
# Soundness of the region-aware exclusions in the rotated code (Theorem B at `p ≤ 93/2000`)

Let `C` be a failing minimum-weight correction of least `Φ = phiRot cA` for the rotated code (as a region code), and
`v0, …, vm` a self-avoiding path of checks, labelled by membership in `C`. Then its pattern is not excluded by the
region-aware check `checkWA 0 h0` at the height `h0 = heightR v0` of its first check.

The proof is the second half of `rot_not_exclS` (`RotSound.lean`), stated once for any checked witness whose
alternative stays in the smooth strip `-1 ≤ U - V ≤ d - 1` (`rot_contra_of_strip`): edges with an end at a check are
transported to the code, the others dropped (Lemma R), and `exchangeR` gives the contradiction. For `checkWA 0 h0`
the alternative is in the strip by the check itself: every point `q` has `x - y ≤ h0` relative to `v0`, i.e.
`U - V ≤ d - 1` (top side), and `x - y ≥ minXY w`, the least `x - y` over the window, i.e. `U - V ≥` the least
`U - V` of the path's checks `≥ -1` (bottom side).
-/

namespace QEC

open Finset QECComp RotSound

namespace RotSoundA

/-- `xyOf` (`AugC.lean`) is `dxy` (`Safe.lean`). -/
theorem xyOf_eq_dxy (p : List ℤ) : xyOf p = dxy p := rfl

/-- The least `x - y` of a window, as in `winRange`. -/
theorem minXY_eq (w : List (ℕ × Bool)) : minXY w = (winRange 2 w).1 := rfl

end RotSoundA

open RotSoundA

/-- **A checked witness whose alternative stays in the smooth strip contradicts the minimality of a failing
correction** (the second half of the proof of `rot_not_exclS`). -/
theorem rot_contra_of_strip {d : ℕ} {c : List ℤ} {E C : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    (hC : IsPhiMinFailR (rotEdges d) rotSide (phiRot c) E C) (S : Finset (Sym2 (RVx (RChk d) (ROut d))))
    (v0 : RChk d) (rest : List (RChk d)) (hadj : AdjChainR (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest),
      (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C))
    (W : Wit) (hcW : checkW 2 c (patOfR S (v0 :: rest)) W = true)
    (hprof : ∀ e ∈ altEdges 2 W.alt,
      (-1 ≤ dxy (tr v0 e.1) ∧ dxy (tr v0 e.1) ≤ d - 1) ∧ (-1 ≤ dxy (tr v0 e.2) ∧ dxy (tr v0 e.2) ≤ d - 1)) :
    False := by
  classical
  set w := patOfR S (v0 :: rest) with hw
  have hz : addP (posC v0) (zeros 2) = posC v0 := by
    have := addP_zeros (posC v0); rwa [length_posC] at this
  -- the window edges
  have hE1 : edgesFrom 2 (posC v0) w =
      (edgesFrom 2 (zeros 2) w).map (fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2)) := by
    have := edgesFrom_translate (o := posC v0) (o' := zeros 2) (length_posC v0) (length_zeros 2) w
    rw [hz] at this
    exact this
  have hwinE : ∀ e ∈ edgesFrom 2 (zeros 2) w, ∃ uv ∈ pairs (v0 :: rest), tr v0 e.1.1 = posC uv.1 ∧
      tr v0 e.1.2 = posC uv.2 ∧ e.2 = decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S) := by
    intro e he
    have hm : ((tr v0 e.1.1, tr v0 e.1.2), e.2) ∈ edgesFrom 2 (posC v0) w := by
      rw [hE1]; exact List.mem_map_of_mem (f := fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2)) he
    rw [hw, edgesFrom_patOfR S v0 rest hadj, List.mem_map] at hm
    obtain ⟨uv, huv, heq⟩ := hm
    simp only [Prod.mk.injEq] at heq
    exact ⟨uv, huv, heq.1.1.symm, heq.1.2.symm, heq.2.symm⟩
  -- unpack the witness
  simp only [checkW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcW
  obtain ⟨⟨halt, hpar⟩, hsz⟩ := hcW
  set X := cEdges 2 w with hX
  set Y := if W.useE then eEdges 2 w else [] with hY
  set P := altEdges 2 W.alt with hP
  have hXmem : ∀ e ∈ X, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = true ∧ e'.1 = e := by
    intro e he
    simp only [hX, cEdges, List.mem_map, List.mem_filter] at he
    obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
    exact ⟨e', he', hl, rfl⟩
  have hYmem : ∀ e ∈ Y, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = false ∧ e'.1 = e := by
    intro e he
    rw [hY] at he
    split_ifs at he
    · simp only [eEdges, List.mem_map, List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
      exact ⟨e', he', hl, rfl⟩
    · simp at he
  -- facts about a window edge
  have hwin : ∀ e' ∈ edgesFrom 2 (zeros 2) w, GoodR v0 [e'.1] ∧ keep v0 e'.1 = true ∧
      FS (tr v0 e'.1.1) = false ∧ FS (tr v0 e'.1.2) = false ∧
      ∃ uv ∈ pairs (v0 :: rest), trE v0 e'.1 = s(RVx.chk uv.1, RVx.chk uv.2) ∧
        e'.2 = decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S) := by
    intro e' he'
    obtain ⟨uv, huv, h1, h2, h3⟩ := hwinE e' he'
    have hpe := mem_edgesFrom_pts 2 (zeros 2) w e' he'
    have l1a : e'.1.1.length = 2 := length_of_mem_walkPts (length_zeros 2) hpe.1
    have l1b : e'.1.2.length = 2 := length_of_mem_walkPts (length_zeros 2) hpe.2
    have hadj1 := adj_of_mem_pairsR hadj huv
    refine ⟨?_, ?_, by rw [h1]; exact (chk_facts uv.1).2.2.1, by rw [h2]; exact (chk_facts uv.2).2.2.1,
      uv, huv, ?_, h3⟩
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      refine ⟨l1a, l1b, ?_, ?_, ?_⟩
      · have : l1 (tr v0 e'.1.1) (tr v0 e'.1.2) = l1 e'.1.1 e'.1.2 := l1_translate (length_posC v0) l1a l1b
        rw [← this, h1, h2]; exact hadj1
      · rw [h1]; exact ⟨(chk_facts uv.1).1, (chk_facts uv.1).2.1⟩
      · rw [h2]; exact ⟨(chk_facts uv.2).1, (chk_facts uv.2).2.1⟩
    · simp only [keep, Bool.or_eq_true, decide_eq_true_eq]
      left; rw [h1]; exact (chk_facts uv.1).2.2.2
    · simp only [trE]; rw [h1, h2, toRV_posC, toRV_posC]
  have hwinXY : ∀ e ∈ X ++ Y, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.1 = e := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · obtain ⟨e', he', -, rfl⟩ := hXmem e h; exact ⟨e', he', rfl⟩
    · obtain ⟨e', he', -, rfl⟩ := hYmem e h; exact ⟨e', he', rfl⟩
  have hgoodXY : GoodR v0 (X ++ Y) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact (hwin e' he').1 _ (by simp)
  have hkeepXY : ∀ e ∈ X ++ Y, keep v0 e = true := by
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact (hwin e' he').2.1
  have hgoodP : GoodR v0 P := by
    intro e he
    simp only [hP, altEdges, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨⟨hd4, hb1⟩, -⟩ := halt a ha
    have la : a.1.length = 2 := by
      simp only [inBB, Bool.and_eq_true, beq_iff_eq] at hb1; exact hb1.1
    have hprof' := hprof (a.1, addP a.1 (vecOf 2 a.2)) (by
      rw [hP]; simp only [altEdges, List.mem_map]; exact ⟨a, ha, rfl⟩)
    exact ⟨la, by simp [la], l1_unit la (by omega), hprof'.1, hprof'.2⟩
  -- the window edges are distinct
  have hE0 : (edgesFrom 2 (zeros 2) w).map (fun e => trE v0 e.1) =
      (pairs (v0 :: rest)).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2)) := by
    calc (edgesFrom 2 (zeros 2) w).map (fun e => trE v0 e.1)
        = ((edgesFrom 2 (zeros 2) w).map (fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2))).map
            (fun e : Edge × Bool => s(toRV (RVx.chk v0) e.1.1, toRV (RVx.chk v0) e.1.2)) := by
          rw [List.map_map]; rfl
      _ = ((pairs (v0 :: rest)).map
            (fun uv => ((posC uv.1, posC uv.2), decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S)))).map
            (fun e : Edge × Bool => s(toRV (RVx.chk v0) e.1.1, toRV (RVx.chk v0) e.1.2)) := by
          rw [← hE1, hw, edgesFrom_patOfR S v0 rest hadj]
      _ = (pairs (v0 :: rest)).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2)) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro uv _
          simp [toRV_posC]
  have hall : ((cEdges 2 w ++ eEdges 2 w).map (trE v0)).Nodup := by
    have hperm : (cEdges 2 w ++ eEdges 2 w).Perm ((edgesFrom 2 (zeros 2) w).map Prod.fst) := by
      unfold cEdges eEdges
      rw [← List.map_append]
      exact (List.filter_append_perm _ _).map _
    have hl : ((edgesFrom 2 (zeros 2) w).map Prod.fst).map (trE v0) =
        ledges ((v0 :: rest).map (RVx.chk (W := ROut d))) := by
      rw [ledges_map_chk, List.map_map]
      exact hE0
    rw [(hperm.map _).nodup_iff, hl]
    exact ledges_nodup (hnd.map (fun _ _ h => RVx.chk.inj h))
  have hXYnd : (X.map (trE v0) ++ Y.map (trE v0)).Nodup := by
    rw [hY]
    split_ifs
    · rw [← List.map_append]; exact hall
    · rw [List.map_nil, List.append_nil, ← List.append_nil (X.map (trE v0))]
      rw [List.map_append] at hall
      exact (List.nodup_append.mp hall).1.append List.nodup_nil (by simp)
  have hXC : ∀ e ∈ X.map (trE v0), e ∈ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hXmem f hf
    obtain ⟨-, -, -, -, uv, huv, ht, hlab⟩ := hwin e' he'
    rw [ht]
    rw [hl] at hlab
    have hnS : s(RVx.chk uv.1, RVx.chk uv.2) ∉ S := by simpa using hlab.symm
    by_contra hc
    exact hnS ((hS uv huv).mpr hc)
  have hYC : ∀ e ∈ Y.map (trE v0), e ∉ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hYmem f hf
    obtain ⟨-, -, -, -, uv, huv, ht, hlab⟩ := hwin e' he'
    rw [ht]
    rw [hl] at hlab
    have hS' : s(RVx.chk uv.1, RVx.chk uv.2) ∈ S := by simpa using hlab.symm
    exact (hS uv huv).mp hS'
  have hg : ∀ e ∈ X.map (trE v0) ++ Y.map (trE v0) ++ (P.filter (keep v0)).map (trE v0), e ∈ rotEdges d := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · rw [← List.map_append] at h
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      exact kept_mem (goodR_sub hgoodXY (fun g hg => by simp at hg; subst hg; exact hf)) (hkeepXY f hf)
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      rw [List.mem_filter] at hf
      exact kept_mem (goodR_sub hgoodP (fun g hg => by simp at hg; subst hg; exact hf.1)) hf.2
  have hXYout : ∀ e ∈ X.map (trE v0) ++ Y.map (trE v0), ∀ w' : ROut d, RVx.out w' ∉ e := by
    intro e he w'
    rw [← List.map_append] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', rfl⟩ := hwinXY f hf
    obtain ⟨-, -, -, -, uv, -, ht, -⟩ := hwin e' he'
    rw [ht]
    simp [Sym2.mem_iff]
  have hpar' : Even (∑ w' ∈ univ.filter (fun w' : ROut d => rotSide w' = true),
      rldeg ((P.filter (keep v0)).map (trE v0)) (RVx.out w')) := by
    rw [side1_count v0 P hgoodP]
    refine crossings_even v0 (fun e he => ne_of_l1 (hgoodP e he).2.2.1) (parOK_spec hpar) ?_
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact ⟨(hwin e' he').2.2.1, (hwin e' he').2.2.2.1⟩
  have hXYkeep : (X ++ Y).filter (keep v0) = X ++ Y := List.filter_eq_self.mpr hkeepXY
  have hodd : roddD ((P.filter (keep v0)).map (trE v0)) = roddD (X.map (trE v0) ++ Y.map (trE v0)) := by
    ext v
    simp only [roddD, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← List.map_append, ← hXYkeep, rldeg_kept v0 hgoodP v, rldeg_kept v0 hgoodXY v, Nat.odd_iff,
      Nat.odd_iff, parOK_spec hpar]
  have hex := exchangeR hC hXYnd hXC hYC hg hXYout hpar' hodd
  simp only [List.length_map] at hex
  have hPlen : (P.filter (keep v0)).length ≤ P.length := List.length_filter_le _ _
  rcases hsz with hlt | ⟨⟨heq, hnodup⟩, hphi⟩
  · exact absurd hex.1 (by omega)
  · by_cases hallk : (P.filter (keep v0)).length = P.length
    · have hkP : ∀ e ∈ P, keep v0 e = true := List.length_filter_eq_length_iff.mp hallk
      have hPf : P.filter (keep v0) = P := List.filter_eq_self.mpr hkP
      rw [hPf] at hex
      have h2 := hex.2 heq.symm (nodup_map_trE v0 hgoodP hkP hnodup)
      rw [phi_map_trE c v0 (goodR_sub hgoodXY (fun e he => List.mem_append_left _ he))
          (fun e he => hkeepXY e (List.mem_append_left _ he)),
        phi_map_trE c v0 (goodR_sub hgoodXY (fun e he => List.mem_append_right _ he))
          (fun e he => hkeepXY e (List.mem_append_right _ he)),
        phi_map_trE c v0 hgoodP hkP] at h2
      have hlen' : (X.length : ℤ) = Y.length + P.length := by exact_mod_cast heq.symm
      have hmul : 2 * (X.length : ℤ) * phiP c (posC v0) =
          2 * (Y.length : ℤ) * phiP c (posC v0) + 2 * (P.length : ℤ) * phiP c (posC v0) := by
        rw [hlen']; ring
      linarith
    · exact absurd hex.1 (by omega)

/-- **Soundness of the region-aware exclusions in the rotated code.** -/
theorem rot_not_exclA {d : ℕ} {E C : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    (hC : IsPhiMinFailR (rotEdges d) rotSide (phiRot cA) E C) (S : Finset (Sym2 (RVx (RChk d) (ROut d))))
    (v0 : RChk d) (rest : List (RChk d)) (hadj : AdjChainR (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest),
      (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C))
    (hlen : rest.length < d) :
    ¬ ExclA 0 (heightR v0) (patOfR S (v0 :: rest)) := by
  classical
  rintro ⟨W, hW⟩
  set w := patOfR S (v0 :: rest) with hw
  set pts := walkPts 2 (zeros 2) (w.map Prod.fst) with hpts
  -- the points of the window, translated, are the checks of the path
  have hwalk : pts.map (tr v0) = (v0 :: rest).map posC := by
    rw [← walkPts_patOfR S v0 rest hadj, ← hw, walkPts_eq_map (length_posC v0), hpts]
    rfl
  have hptsC : ∀ p ∈ pts, p.length = 2 ∧ ∃ u ∈ v0 :: rest, tr v0 p = posC u := by
    intro p hp
    refine ⟨length_of_mem_walkPts (length_zeros 2) hp, ?_⟩
    have : tr v0 p ∈ (v0 :: rest).map posC := by rw [← hwalk]; exact List.mem_map_of_mem hp
    obtain ⟨u, hu, hpu⟩ := List.mem_map.mp this
    exact ⟨u, hu, hpu.symm⟩
  -- absolute `x - y` of the window points
  have habs : ∀ p ∈ pts, dxy (tr v0 p) = dxy (posC v0) + dxy p ∧ -1 ≤ dxy (tr v0 p) := by
    intro p hp
    obtain ⟨hl, u, -, hu⟩ := hptsC p hp
    refine ⟨dxy_addP (length_posC v0) hl, ?_⟩
    rw [hu]; exact (chk_facts u).1
  -- the least `x - y` of the window is attained at one of its points
  have hz0 : zeros 2 ∈ pts := zeros_mem_walkPts _
  have hlo_att : ∃ p ∈ pts, dxy p = minXY w := by
    have hds : minXY w = (pts.map dxy).foldl min 0 := rfl
    have := foldl_min_mem (pts.map dxy) 0
    rw [List.mem_cons] at this
    rcases this with h | h
    · exact ⟨zeros 2, hz0, by rw [hds, h]; rfl⟩
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
      exact ⟨p, hp, by rw [hds, hpe]⟩
  obtain ⟨plo, hplo, hplo'⟩ := hlo_att
  have hlo1 : -1 ≤ dxy (posC v0) + minXY w := by
    have := (habs plo hplo).2
    rw [(habs plo hplo).1, hplo'] at this
    exact this
  -- the height of the first check
  have hv0 := chk_facts v0
  have hh0 : heightR v0 = (d : ℤ) - 1 - dxy (posC v0) := by
    rw [dxy_eq_pr, pr_posC]; rfl
  have hh0nn : ¬ heightR v0 < ((0 : ℕ) : ℤ) := by
    rw [hh0]; push_cast; omega
  -- unpack the region-aware check
  have hif : (if heightR v0 < ((0 : ℕ) : ℤ) then (1 : ℤ) else 0) = 0 := by
    split_ifs
    rfl
  unfold checkWA at hW
  rw [hif, sub_zero] at hW
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hW
  obtain ⟨hcW, hprofA⟩ := hW
  -- the lengths of the alternative's points
  have hlen2 : ∀ e ∈ altEdges 2 W.alt, e.1.length = 2 ∧ e.2.length = 2 := by
    intro e he
    have hcW' := hcW
    simp only [checkW, Bool.and_eq_true, List.all_eq_true] at hcW'
    simp only [altEdges, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    have h3 := hcW'.1.1 a ha
    simp only [Bool.and_eq_true, inBB, beq_iff_eq] at h3
    exact ⟨h3.1.2.1, h3.2.1⟩
  refine rot_contra_of_strip hC S v0 rest hadj hnd hS W hcW ?_
  intro e he
  obtain ⟨⟨⟨t1, t2⟩, b1⟩, b2⟩ := hprofA e he
  obtain ⟨l1e, l2e⟩ := hlen2 e he
  rw [xyOf_eq_dxy] at t1 t2 b1 b2
  rw [hh0] at t1 t2
  rw [show tr v0 e.1 = addP (posC v0) e.1 from rfl, show tr v0 e.2 = addP (posC v0) e.2 from rfl,
    dxy_addP (length_posC v0) l1e, dxy_addP (length_posC v0) l2e]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end QEC
