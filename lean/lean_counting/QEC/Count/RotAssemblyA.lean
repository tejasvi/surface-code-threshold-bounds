import QEC.Count.AugDefs
import QEC.Count.RotAssembly

/-!
# Assembly for the rotated code with the augmented certificate (Theorem B at `p ≤ 93/2000`)

As `RotAssembly.lean`, with the region-aware rules: a window is tested at the height of its first vertex. If some
minimum-weight correction fails, take a failing one `C` of least `Φ = phiRot cA` (`exists_phiMinFailR`) and the failure
path (`failure_pathR`): a side-1 half-edge, checks `v0 … vL`, a side-2 half-edge. The interior pattern is legal for the
heights: walking the pattern from `heightR v0` with `nxtA` gives the heights of the checks (`offAt_patOfR`), which
are `≥ 0` (`heightR_nonneg`), so the negative-height clause of `ExA` never applies, and no window is excluded (the
hypothesis `hwin`, on every sub-path). The union bound, the tilt and the injection
`(γ, S) ↦ (first half-edge, its label, pattern, direction of the last half-edge, its label)` are those of
`pfail_rot_le`; the target is a sigma type over the first half-edge, whose check fixes the start height of the
patterns, which are counted by the hypothesis `hcount`.
-/

namespace QEC

open Finset QECComp
open scoped symmDiff

namespace RotAssemblyA

variable {d : ℕ}

/-- Checks lie below the top smooth side. -/
theorem heightR_nonneg (v : RChk d) : 0 ≤ heightR v := by
  have := RotAssembly.chk_cond v
  unfold heightR
  omega

/-- The height of a vertex of the graph (`0` for outer points). -/
def hvA : RVx (RChk d) (ROut d) → ℤ
  | .chk v => heightR v
  | .out _ => 0

/-- The sum of the heights of the ends of an edge; for a half-edge `s(out w, chk v)` the height of `v`. -/
def hgtE (e : Sym2 (RVx (RChk d) (ROut d))) : ℤ := Sym2.lift ⟨fun a b => hvA a + hvA b, fun _ _ => add_comm _ _⟩ e

theorem hgtE_out_chk (w : ROut d) (v : RChk d) : hgtE s(RVx.out w, RVx.chk v) = heightR v := by
  simp [hgtE, hvA]

theorem foldl_add_dl2 : ∀ (w : List (ℕ × Bool)) (a : ℤ),
    w.foldl (fun s x => s + dl2 x.1) a = a + vdisp w
  | [], a => by simp [vdisp]
  | x :: w, a => by
    have h1 := foldl_add_dl2 w (a + dl2 x.1)
    have h2 := foldl_add_dl2 w (0 + dl2 x.1)
    simp only [List.foldl_cons] at h1 ⊢
    unfold vdisp
    simp only [List.foldl_cons]
    rw [h1, h2]
    ring

theorem vdisp_cons (x : ℕ × Bool) (w : List (ℕ × Bool)) : vdisp (x :: w) = dl2 x.1 + vdisp w := by
  have := foldl_add_dl2 w (0 + dl2 x.1)
  unfold vdisp at this ⊢
  simp only [List.foldl_cons]
  rw [this]
  ring

theorem vdisp_nil : vdisp [] = 0 := rfl

theorem foldl_nxtA : ∀ (w : List (ℕ × Bool)) (h : ℤ), (w.map Prod.fst).foldl nxtA h = h - vdisp w
  | [], h => by simp [vdisp]
  | x :: w, h => by
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_nxtA w (nxtA h x.1), vdisp_cons, nxtA]
    ring

/-- Walking a pattern changes the height by `-vdisp`. -/
theorem offAt_nxtA (h : ℤ) (w : List (ℕ × Bool)) (i : ℕ) : offAt nxtA h w i = h - vdisp (w.take i) := by
  unfold offAt
  exact foldl_nxtA (w.take i) h

/-- A step to a neighbour changes the height by `-dl2` of its direction. -/
theorem heightR_step {u v : RChk d} (h : l1 [u.1.1, u.1.2] [v.1.1, v.1.2] = 1) :
    heightR v = heightR u - dl2 (dirOfR u v) := by
  obtain ⟨hd4, e⟩ := RotAssembly.adj_dir h
  rw [RotAssembly.vecOf_two _ hd4] at e
  unfold heightR dl2
  rcases (show dirOfR u v = 0 ∨ dirOfR u v = 1 ∨ dirOfR u v = 2 ∨ dirOfR u v = 3 by omega) with hd | hd | hd | hd <;>
    simp [hd, addP] at e <;> simp [hd] <;> omega

/-- The heights along the pattern of a path of checks are the heights of its checks. -/
theorem offAt_patOfR (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (v0 : RChk d) (rest : List (RChk d)), AdjChainR (v0 :: rest) → ∀ i (hi : i < rest.length + 1),
      offAt nxtA (heightR v0) (patOfR S (v0 :: rest)) i = heightR ((v0 :: rest)[i]'hi)
  | v0, [], _, i, hi => by
    have : i = 0 := by simp at hi; omega
    subst this
    simp [offAt]
  | v0, v :: rest, h, 0, _ => by simp [offAt]
  | v0, v :: rest, h, i + 1, hi => by
    have ih := offAt_patOfR S v rest h.2 i (by simp at hi ⊢; omega)
    simp only [List.getElem_cons_succ]
    rw [← ih]
    unfold offAt
    simp only [patOfR, List.take_succ_cons, List.map_cons, List.foldl_cons]
    rw [nxtA, ← heightR_step h.1]

/-- The interior pattern of the failure path is legal for the region-aware rules (given the window property). -/
theorem legal_interiorA {hN K : ℕ} {C : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    (hwin : ∀ (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) (v0 : RChk d) (rest : List (RChk d)),
        AdjChainR (v0 :: rest) → (v0 :: rest).Nodup →
        (∀ uv ∈ pairs (v0 :: rest), (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C)) →
        rest.length < d → ¬ ExclA hN (heightR v0) (patOfR S (v0 :: rest)))
    {S : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    {v0 : RChk d} {rest : List (RChk d)} (hadj : AdjChainR (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest),
      (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C))
    (hKd : K + 1 < d) :
    LegalG nxtA (ExA hN) (K + 1) (heightR v0) (patOfR S (v0 :: rest)) := by
  refine ⟨?_, RotAssembly.dirOK_patOfR S _ hadj, ?_⟩
  · unfold SelfAv
    have h1 := RotAssembly.walkPts_patOfR S v0 rest hadj
    rw [walkPts_eq_map (by simp [RotAssembly.cpos] : (RotAssembly.cpos v0).length = 2)] at h1
    have h2 : ((v0 :: rest).map RotAssembly.cpos).Nodup := hnd.map RotAssembly.cpos_injective
    rw [← h1] at h2
    exact h2.of_map _
  · intro i m hm2 hmM him
    rw [RotAssembly.length_patOfR] at him
    have hL : (v0 :: rest).length = rest.length + 1 := rfl
    have hi : i < rest.length + 1 := by omega
    rw [offAt_patOfR S v0 rest hadj i hi, RotAssembly.patOfR_drop, RotAssembly.patOfR_take]
    have hlen : 0 < (((v0 :: rest).drop i).take (m + 1)).length := by
      rw [List.length_take, List.length_drop]
      omega
    obtain ⟨v', rest', hws⟩ : ∃ v' rest', ((v0 :: rest).drop i).take (m + 1) = v' :: rest' := by
      cases h : ((v0 :: rest).drop i).take (m + 1) with
      | nil => rw [h] at hlen; simp at hlen
      | cons v' rest' => exact ⟨v', rest', rfl⟩
    have hlen' : rest'.length ≤ m := by
      have := congrArg List.length hws
      rw [List.length_take, List.length_cons] at this
      omega
    have hv' : (v0 :: rest)[i]'hi = v' := by
      have e1 : (((v0 :: rest).drop i).take (m + 1))[0]? = some v' := by rw [hws]; rfl
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero,
        List.getElem?_eq_getElem hi] at e1
      exact Option.some.inj e1
    rw [hv', hws]
    have hadj' : AdjChainR (v' :: rest') := by
      rw [← hws]
      exact RotAssembly.adjChainR_take _ _ (RotAssembly.adjChainR_drop _ _ hadj)
    rintro (hex | ⟨j, hj, hneg⟩)
    · apply hwin S v' rest' hadj'
      · rw [← hws]
        exact (hnd.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
      · intro uv huv
        rw [← hws] at huv
        exact hS uv (Assembly.pairs_drop _ i (Assembly.pairs_take _ (m + 1) huv))
      · omega
      · exact hex
    · rw [RotAssembly.length_patOfR] at hj
      have hj' : j < rest'.length + 1 := by simp at hj; omega
      rw [← offAt_nxtA, offAt_patOfR S v' rest' hadj' j hj'] at hneg
      exact absurd hneg (not_lt.mpr (heightR_nonneg _))

end RotAssemblyA

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The failure probability of the rotated code** with the region-aware rules: from the window property (`hwin`)
and a bound on the weight of the legal patterns of each length from each start height (`hcount`). -/
theorem pfail_rot_leA (d K hN : ℕ) {p X lam B : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 ≤ X)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : 0 ≤ B)
    (hwin : ∀ E C : Finset (Sym2 (RVx (RChk d) (ROut d))), IsPhiMinFailR (rotEdges d) rotSide (phiRot cA) E C →
      ∀ (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) (v0 : RChk d) (rest : List (RChk d)),
        AdjChainR (v0 :: rest) → (v0 :: rest).Nodup →
        (∀ uv ∈ pairs (v0 :: rest), (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C)) →
        rest.length < d → ¬ ExclA hN (heightR v0) (patOfR S (v0 :: rest)))
    (hcount : ∀ h0 : ℤ, 0 ≤ h0 → ∀ n, K ≤ n →
      ∑ w ∈ (pats 2 n).filter (LegalG nxtA (ExA hN) (K + 1) h0), wtW (p * X) ((1 - p) / X) w ≤
        lam ^ (n - K) * B)
    (hK : K + 2 ≤ d) :
    PfailMWR (rotEdges d) rotSide p ≤
      #((rotEdges d).filter (fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e)) * 2 *
        (p * X + (1 - p) / X) ^ 2 * B * (lam ^ (d - 2 - K) / (1 - lam)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hE0 : 0 ≤ p * X := (mul_pos hp0 hX0).le
  have hC0 : 0 ≤ (1 - p) / X := div_nonneg (by linarith) hX0.le
  have hd2 : 2 ≤ d := by omega
  unfold PfailMWR
  set ωE := p * X with hωE
  set ωC := (1 - p) / X with hωC
  set Eg := rotEdges d with hEg
  set S1 := (rotEdges d).filter (fun e => ∃ w : ROut d, rotSide w = true ∧ RVx.out w ∈ e) with hS1
  set geo := lam ^ (d - 2 - K) / (1 - lam) with hgeo
  have hgeo0 : 0 ≤ geo := div_nonneg (pow_nonneg hlam0 _) (by linarith)
  -- the good labelled paths
  set NL := (univ : Finset {l : List (RVx (RChk d) (ROut d)) // l.Nodup}).map (Function.Embedding.subtype _)
    with hNL
  set I := (NL ×ˢ Eg.powerset).filter
    (fun x : List (RVx (RChk d) (ROut d)) × Finset (Sym2 (RVx (RChk d) (ROut d))) =>
      (∃ (w1 w2 : ROut d) (v0 : RChk d) (rest : List (RChk d)), rotSide w1 = true ∧ rotSide w2 = false ∧
        x.1 = RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) ∧
        IsSPath (decGraph Eg) (RVx.out w1) (RVx.out w2) x.1 ∧
        LegalG nxtA (ExA hN) (K + 1) (heightR v0) (patOfR x.2 (v0 :: rest))) ∧
      x.2 ⊆ pedges x.1 ∧ #(pedges x.1 \ x.2) ≤ #x.2) with hI
  -- every failing error meets a good labelled path exactly in its E-edges
  have hincl : ∀ E ⊆ Eg, (∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C) → ∃ x ∈ I, E ∩ pedges x.1 = x.2 := by
    intro E hE hfail
    obtain ⟨C, hC⟩ := exists_phiMinFailR Eg rotSide (phiRot cA) hfail
    obtain ⟨w1, w2, v0, rest, hs1, hs2, hl⟩ :=
      failure_pathR rotSide RotAssembly.rotEdges_not_diag RotAssembly.out_out_not_mem hE hC.1 hC.2.1
    have hR : E ∆ C ⊆ Eg := fun e he =>
      (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hE h) (fun h => hC.1.1 h)
    set l := RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) with hl_def
    have hlEg : IsSPath (decGraph Eg) (RVx.out w1) (RVx.out w2) l :=
      ⟨hl.head, hl.last, hl.chain.imp (fun _ _ h => decGraph_mono hR h), hl.nodup⟩
    have hsubR : pedges l ⊆ E ∆ C := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    have hsubEg : pedges l ⊆ Eg := hsubR.trans hR
    have hf := RotAssembly.path_factsR hR hl
    refine ⟨(l, E ∩ pedges l), ?_, rfl⟩
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    refine ⟨⟨Finset.mem_map.mpr ⟨⟨l, hl.nodup⟩, Finset.mem_univ _, rfl⟩, Finset.inter_subset_left.trans hE⟩,
      ⟨w1, w2, v0, rest, hs1, hs2, rfl, hlEg, ?_⟩, Finset.inter_subset_right, ?_⟩
    · apply RotAssemblyA.legal_interiorA (hwin E C hC) hf.1 hf.2.1 _ (by omega)
      intro uv huv
      have hmem : s(RVx.chk uv.1, RVx.chk uv.2) ∈ pedges l := by
        rw [hl_def]
        apply List.mem_toFinset.mpr
        rw [RotAssembly.ledges_pathR, RotAssembly.ledges_map_chk]
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        exact List.mem_map_of_mem (f := fun uv : RChk d × RChk d => s(RVx.chk uv.1, RVx.chk uv.2)) huv
      have h2 := hsubR hmem
      rw [Finset.mem_symmDiff] at h2
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hE', -⟩ hC'
        rcases h2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact h hC'
        · exact h hE'
      · intro hC'
        rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact ⟨h, hmem⟩
        · exact absurd h hC'
    · have h := half_weight_unifR hC.1 hsubEg (RotAssembly.rbd_pathR w1 w2 v0 rest hl.nodup) hsubR
      have e1 : pedges l \ (E ∩ pedges l) = pedges l \ E := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [e1, Finset.inter_comm]
      exact h
  -- the union bound
  have hunion : PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C) ≤
      ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) :=
    le_trans (PrIID_mono Eg hp0.le hp1.le hincl) (PrIID_exists_le Eg hp0.le hp1.le I _)
  -- each term, tilted
  have hterm : ∀ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) ≤ ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := by
    intro x hx
    rw [hI, Finset.mem_filter] at hx
    obtain ⟨-, ⟨w1, w2, v0, rest, -, -, -, hl, -⟩, hS, hhalf⟩ := hx
    have hsubEg : pedges x.1 ⊆ Eg := fun e he => ledges_subset_of_chain hl.chain e (List.mem_toFinset.mp he)
    rw [PrIID_inter_eq Eg p hsubEg hS]
    exact tilt_unif hp0.le hp1.le hX hhalf
  have hRHS0 : 0 ≤ (#S1 : ℝ) * 2 * (ωE + ωC) ^ 2 * B * geo :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (sq_nonneg _)) hB) hgeo0
  rcases Finset.eq_empty_or_nonempty I with hI0 | ⟨x0, hx0⟩
  · calc PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C)
        ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
      _ = 0 := by rw [hI0, Finset.sum_empty]
      _ ≤ _ := hRHS0
  -- a check, to define the injection
  obtain ⟨vstar⟩ : Nonempty (RChk d) := by
    rw [hI, Finset.mem_filter] at hx0
    obtain ⟨-, ⟨-, -, v0, -, -, -, -, -, -⟩, -, -⟩ := hx0
    exact ⟨v0⟩
  set dflt : RVx (RChk d) (ROut d) := RVx.chk vstar with hdflt
  -- the injection into (first half-edge; its label, interior pattern, direction of the last half-edge, its label)
  set f : List (RVx (RChk d) (ROut d)) × Finset (Sym2 (RVx (RChk d) (ROut d))) →
      Σ _ : Sym2 (RVx (RChk d) (ROut d)), Bool × List (ℕ × Bool) × Bool × Bool :=
    fun x => ⟨s(x.1.headD dflt, RVx.chk ((RotAssembly.getChksR x.1).headD vstar)),
      (decide (s(x.1.headD dflt, RVx.chk ((RotAssembly.getChksR x.1).headD vstar)) ∉ x.2),
      patOfR x.2 (RotAssembly.getChksR x.1),
      decide (posR (x.1.getLastD dflt) = [((RotAssembly.getChksR x.1).getLastD vstar).1.1 + 1,
        ((RotAssembly.getChksR x.1).getLastD vstar).1.2]),
      decide (s(RVx.chk ((RotAssembly.getChksR x.1).getLastD vstar), x.1.getLastD dflt) ∉ x.2))⟩ with hf
  set g : (Σ _ : Sym2 (RVx (RChk d) (ROut d)), Bool × List (ℕ × Bool) × Bool × Bool) → ℝ :=
    fun y => (if y.2.1 then ωC else ωE) * wtW ωE ωC y.2.2.1 * (if y.2.2.2.2 then ωC else ωE) with hg
  set Pset : Sym2 (RVx (RChk d) (ROut d)) → Finset (List (ℕ × Bool)) := fun h1 =>
    (Finset.Ico (d - 2) (Fintype.card (RChk d))).biUnion
      (fun L => (pats 2 L).filter (LegalG nxtA (ExA hN) (K + 1) (max 0 (RotAssemblyA.hgtE h1)))) with hPset
  set J : Finset (Σ _ : Sym2 (RVx (RChk d) (ROut d)), Bool × List (ℕ × Bool) × Bool × Bool) :=
    S1.sigma (fun h1 => (univ : Finset Bool) ×ˢ (Pset h1 ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool))))
    with hJ
  have hfx : ∀ x ∈ I, ∃ (w1 w2 : ROut d) (v0 : RChk d) (rest : List (RChk d)),
      x.1 = RVx.out w1 :: ((v0 :: rest).map RVx.chk ++ [RVx.out w2]) ∧
      f x = ⟨s(RVx.out w1, RVx.chk v0), (decide (s(RVx.out w1, RVx.chk v0) ∉ x.2), patOfR x.2 (v0 :: rest),
        decide (posR (RVx.out w2 : RVx (RChk d) (ROut d)) =
          [((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.1 + 1, ((v0 :: rest).getLast (List.cons_ne_nil _ _)).1.2]),
        decide (s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∉ x.2))⟩ ∧
      AdjChainR (v0 :: rest) ∧ (v0 :: rest).Nodup ∧ s(RVx.out w1, RVx.chk v0) ∈ Eg ∧
      s(RVx.chk ((v0 :: rest).getLast (List.cons_ne_nil _ _)), RVx.out w2) ∈ Eg ∧
      rotSide w1 = true ∧ rotSide w2 = false ∧
      LegalG nxtA (ExA hN) (K + 1) (heightR v0) (patOfR x.2 (v0 :: rest)) ∧
      x.2 ⊆ pedges x.1 ∧ x.1.Nodup := by
    intro x hx
    rw [hI, Finset.mem_filter] at hx
    obtain ⟨-, ⟨w1, w2, v0, rest, hs1, hs2, hdec, hl, hleg⟩, hS, -⟩ := hx
    have hpf := RotAssembly.path_factsR (Finset.Subset.refl Eg) (hdec ▸ hl)
    refine ⟨w1, w2, v0, rest, hdec, ?_, hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2, hs1, hs2, hleg, hS, hl.nodup⟩
    simp only [hf, hdec, RotAssembly.getChksR_path, List.headD_cons, RotAssembly.getLastD_pathR]
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (List.cons_ne_nil v0 rest), Option.getD_some]
  have hmaps : I.image f ⊆ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w1, w2, v0, rest, -, hfx1, hadj, hnd, h01, hlast, hs1, hs2, hleg, -, -⟩ := hfx x hx
    rw [hfx1, hJ, Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [hS1, Finset.mem_filter]
      exact ⟨h01, w1, hs1, Sym2.mem_mk_left _ _⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, and_true]
      rw [hPset, Finset.mem_biUnion]
      refine ⟨rest.length, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        have hc := RotAssembly.sum_last_le v0 rest hadj
        have h0 := RotAssembly.sum_first h01 hs1
        have hl2 := (RotAssembly.last_facts hlast hs2 hd2).1
        have hcard := hnd.length_le_card
        simp only [List.length_cons] at hcard
        constructor
        · omega
        · omega
      · rw [Finset.mem_filter, mem_pats, RotAssembly.length_patOfR, RotAssemblyA.hgtE_out_chk,
          max_eq_right (RotAssemblyA.heightR_nonneg v0)]
        exact ⟨⟨by simp, RotAssembly.dirOK_patOfR _ _ hadj⟩, hleg⟩
  have hinj : Set.InjOn f I := by
    intro x hx x' hx' hxx
    obtain ⟨w1, w2, v0, rest, hdec, hfx1, hadj, -, -, hlast, -, hs2, -, hS, -⟩ := hfx x hx
    obtain ⟨w1', w2', v0', rest', hdec', hfx1', hadj', -, -, hlast', -, hs2', -, hS', -⟩ := hfx x' hx'
    rw [hfx1, hfx1', Sigma.mk.inj_iff] at hxx
    obtain ⟨h1, hxx⟩ := hxx
    rw [heq_iff_eq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hxx
    obtain ⟨hl1, hp, hj, hl2⟩ := hxx
    obtain ⟨rfl, rfl⟩ := RotAssembly.out_chk_eq h1
    have hrest : rest = rest' := RotAssembly.rest_eq_of_patOfR hadj hadj' hp
    subst hrest
    have hw2 : w2 = w2' := by
      have f1 := (RotAssembly.last_facts hlast hs2 hd2).2
      have f2 := (RotAssembly.last_facts hlast' hs2' hd2).2
      set vl := (v0 :: rest).getLast (List.cons_ne_nil _ _) with hvl
      have key : ∀ w : ROut d, decide (posR (RVx.out w : RVx (RChk d) (ROut d)) = [vl.1.1 + 1, vl.1.2]) = true ↔
          w.1 = (vl.1.1 + 1, vl.1.2) := by
        intro w
        simp only [decide_eq_true_eq, posR, List.cons.injEq, and_true]
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext h1 h2
        · intro h
          rw [h]
          exact ⟨rfl, rfl⟩
      apply Subtype.ext
      rcases f1 with e1 | e1 <;> rcases f2 with e2 | e2
      · rw [e1, e2]
      · exfalso
        have h1 := (key w2).mpr e1
        rw [hj] at h1
        have h2 := (key w2').mp h1
        rw [e2] at h2
        simp only [Prod.mk.injEq] at h2
        omega
      · exfalso
        have h1 := (key w2').mpr e2
        rw [← hj] at h1
        have h2 := (key w2).mp h1
        rw [e1] at h2
        simp only [Prod.mk.injEq] at h2
        omega
      · rw [e1, e2]
    subst hw2
    have hl : x.1 = x'.1 := by rw [hdec, hdec']
    have hSS : x.2 = x'.2 := by
      ext e
      by_cases he : e ∈ pedges x.1
      · rw [hdec] at he
        have he' := List.mem_toFinset.mp he
        rw [RotAssembly.ledges_pathR, List.mem_cons, List.mem_append, List.mem_singleton] at he'
        rcases he' with rfl | he' | rfl
        · exact Assembly.mem_iff_of_decide_eq hl1
        · exact RotAssembly.patOfR_eq_labels _ hp e he'
        · exact Assembly.mem_iff_of_decide_eq hl2
      · constructor
        · intro h
          exact absurd (hS h) he
        · intro h
          rw [hl] at he
          exact absurd (hS' h) he
    exact Prod.ext hl hSS
  have hwt : ∀ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) = g (f x) := by
    intro x hx
    obtain ⟨w1, w2, v0, rest, hdec, hfx1, -, -, -, -, -, -, -, hS, hnd⟩ := hfx x hx
    rw [hfx1, hg]
    simp only
    rw [hdec] at hS hnd ⊢
    exact RotAssembly.path_weightR ωE ωC hnd hS
  have hg0 : ∀ y ∈ J, y ∉ I.image f → 0 ≤ g y := by
    intro y _ _
    simp only [hg]
    apply mul_nonneg (mul_nonneg _ (Counting.wtW_nonneg hE0 hC0 _))
    · split_ifs
      · exact hC0
      · exact hE0
    · split_ifs
      · exact hC0
      · exact hE0
  have hsum1 : ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) ≤ ∑ y ∈ J, g y :=
    Finset.sum_le_sum_of_injOn f hinj hmaps (fun x hx => le_of_eq (hwt x hx)) hg0
  -- the patterns from each start height, by length
  have hPsum : ∀ h1, ∑ w ∈ Pset h1, wtW ωE ωC w ≤ B * geo := by
    intro h1
    rw [hPset, Finset.sum_biUnion]
    · calc ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)),
            ∑ w ∈ (pats 2 L).filter (LegalG nxtA (ExA hN) (K + 1) (max 0 (RotAssemblyA.hgtE h1))), wtW ωE ωC w
          ≤ ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)), lam ^ (L - K) * B := by
            apply Finset.sum_le_sum
            intro L hL
            rw [Finset.mem_Ico] at hL
            exact hcount _ (le_max_left _ _) L (by omega)
        _ = B * ∑ L ∈ Finset.Ico (d - 2) (Fintype.card (RChk d)), lam ^ (L - K) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun L _ => by ring)
        _ ≤ B * geo := mul_le_mul_of_nonneg_left (Assembly.geom_shift_le hlam0 hlam1 (by omega)) hB
    · intro L _ L' _ hLL'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [Finset.mem_filter, mem_pats] at hw hw'
      exact hLL' (hw.1.1.symm.trans hw'.1.1)
  -- the sum over the target
  have hJsum : ∑ y ∈ J, g y ≤ #S1 * (2 * ((ωE + ωC) ^ 2 * (B * geo))) := by
    rw [hJ, Finset.sum_sigma]
    have hconst : ∀ h1 ∈ S1,
        ∑ z ∈ (univ : Finset Bool) ×ˢ (Pset h1 ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool))), g ⟨h1, z⟩ ≤
          2 * ((ωE + ωC) ^ 2 * (B * geo)) := by
      intro h1 _
      have e : ∑ z ∈ (univ : Finset Bool) ×ˢ (Pset h1 ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool))),
          g ⟨h1, z⟩ = 2 * ((ωE + ωC) ^ 2 * ∑ w ∈ Pset h1, wtW ωE ωC w) := by
        simp only [hg, Finset.sum_product, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w _
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hPsum h1) (sq_nonneg _)) (by norm_num)
    calc ∑ h1 ∈ S1, ∑ z ∈ (univ : Finset Bool) ×ˢ (Pset h1 ×ˢ ((univ : Finset Bool) ×ˢ (univ : Finset Bool))),
          g ⟨h1, z⟩
        ≤ ∑ h1 ∈ S1, 2 * ((ωE + ωC) ^ 2 * (B * geo)) := Finset.sum_le_sum hconst
      _ = #S1 * (2 * ((ωE + ωC) ^ 2 * (B * geo))) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR rotSide E C)
      ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges x.1 = x.2) := hunion
    _ ≤ ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges x.1 \ x.2) := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ J, g y := hsum1
    _ ≤ #S1 * (2 * ((ωE + ωC) ^ 2 * (B * geo))) := hJsum
    _ = #S1 * 2 * (ωE + ωC) ^ 2 * B * geo := by ring

end QEC
