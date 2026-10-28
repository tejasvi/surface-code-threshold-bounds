import QEC.Count.TorWalk

/-!
# Assembly: the failure probability of the toric code (Theorem A′)

If some minimum-weight correction fails, take a failing one `C` of least `Φ = phiTor L` (`exists_phiMinFailT`). Its
residual `C ∆ E` is even and nontrivial, so it contains a simple cycle `v0, …, v_{n-1}` with `n ≥ L`
(`nontrivial_cycle`). Its E-edges `S` satisfy `|γ \ S| ≤ |S|` (`half_weight_unif`; the cycle has empty boundary,
`bd_cycle`), and the pattern of the path `v0, …, v_{n-1}` (without the closing edge) is legal for the seam rules: its
unrolled walk is self-avoiding (`selfAv_patOfT`), the offsets of its vertices are their seam offsets
(`offAt_patOfT`), and no window is excluded (hypothesis `hwin`). By the union bound and `PrIID_inter_eq`,
`P_fail ≤ ∑ p^|S| (1 - p)^|γ \ S|`, and by the tilt (`tilt_unif`) each term is at most `ω_E^|S| ω_C^|γ \ S|`. The map
`(γ, S) ↦ (v0, label of the closing edge, pattern)` is injective (`eq_of_patOfT`); the closing edge contributes at most
`ω_E + ω_C`, and the patterns of each length `n - 1 ≥ L - 1` from `v0` are counted by the hypothesis `hcount`.
-/

namespace QEC

open Finset QECComp TorWalk
open scoped symmDiff

namespace TorAssembly

/-- The closed vertex list of a cycle `v0, …, v_{n-1}`: its vertices in the decoding graph, then `v0` again. -/
def clist {L : ℕ} : List (TorV L) → List (Vx (TorV L))
  | [] => []
  | v :: r => (v :: r).map Vx.det ++ [Vx.det v]

theorem clist_cons {L : ℕ} (v : TorV L) (r : List (TorV L)) :
    clist (v :: r) = (v :: r).map Vx.det ++ [Vx.det v] := rfl

/-- The edges of the path part of a cycle are edges of the cycle. -/
theorem ledges_sub_clist {L : ℕ} (v0 : TorV L) (rest : List (TorV L)) {e : Sym2 (Vx (TorV L))}
    (he : e ∈ ledges ((v0 :: rest).map Vx.det)) : e ∈ pedges (clist (v0 :: rest)) := by
  rw [clist_cons, pedges, List.mem_toFinset, Assembly.ledges_append_single _ _ (by simp)]
  exact List.mem_append_left _ he

/-- The edges of a cycle: the path part and the closing edge. -/
theorem mem_pedges_clist {L : ℕ} {v0 : TorV L} {rest : List (TorV L)} {e : Sym2 (Vx (TorV L))}
    (he : e ∈ pedges (clist (v0 :: rest))) :
    e ∈ ledges ((v0 :: rest).map Vx.det) ∨
      e = s(Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _)), Vx.det v0) := by
  rw [clist_cons, pedges, List.mem_toFinset, Assembly.ledges_append_single _ _ (by simp), List.mem_append,
    List.mem_singleton, List.getLast_map] at he
  exact he

/-- The weight of a labelled cycle: the closing edge and the pattern of the path part. -/
theorem cycle_weight {L : ℕ} (ωE ωC : ℝ) {S : Finset (Sym2 (Vx (TorV L)))} {v0 : TorV L} {rest : List (TorV L)}
    (hcyc : (ledges (clist (v0 :: rest))).Nodup) (hS : S ⊆ pedges (clist (v0 :: rest))) :
    ωE ^ #S * ωC ^ #(pedges (clist (v0 :: rest)) \ S) =
      (if decide (s(Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _)), Vx.det v0) ∉ S) then ωC else ωE) *
        wtW ωE ωC (patOfT S (v0 :: rest)) := by
  classical
  set l := clist (v0 :: rest) with hl
  have e1 : ∏ e ∈ pedges l, (if e ∈ S then ωE else ωC) = ωE ^ #S * ωC ^ #(pedges l \ S) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS, ← Finset.sdiff_eq_filter]
  have e2 : ∏ e ∈ pedges l, (if e ∈ S then ωE else ωC) = lwt (fun e => if e ∈ S then ωE else ωC) l := by
    rw [pedges, List.prod_toFinset _ hcyc, lwt_eq_prod]
  rw [← e1, e2, hl, clist_cons, Assembly.lwt_append_single _ _ _ (by simp), List.getLast_map, lwt_patOfT]
  have hF : ∀ e : Sym2 (Vx (TorV L)), (if e ∈ S then ωE else ωC) = (if decide (e ∉ S) then ωC else ωE) := by
    intro e
    by_cases h : e ∈ S <;> simp [h]
  rw [hF]
  ring

end TorAssembly

open TorAssembly in
open scoped Classical in
/-- **The failure probability of the toric code**, from the window property of the seam rules (`hwin`) and a bound
on the weight of the legal patterns of each length from each start vertex (`hcount`). -/
theorem pfail_tor_le (L L0 K : ℕ) (hKL : 2 * (K + 1) + 2 < L) {p X lam B : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 ≤ X) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : 0 ≤ B)
    (hwin : ∀ E C : Finset (Sym2 (Vx (TorV L))), E ⊆ torEdges L → IsPhiMinFailT (phiTor L) E C →
      ∀ vs : List (TorV L), vs.Nodup → (vs.map Vx.det).IsChain (decGraph (C ∆ E)).Adj →
      ∀ i m, 2 ≤ m → m ≤ K + 1 → ∀ h : i + m < vs.length,
        ¬ ExclT L0 (qoff (vs[i]'(by omega))) (((patOfT E vs).drop i).take m))
    (hcount : ∀ (v : TorV L) (n : ℕ), K ≤ n →
      ∑ w ∈ (pats 2 n).filter (LegalG (nxtT L) (ExclT L0) (K + 1) (qoff v)), wtW (p * X) ((1 - p) / X) w ≤
        lam ^ (n - K) * B) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * (p * X + (1 - p) / X) * B * (lam ^ (L - 1 - K) / (1 - lam)) := by
  classical
  have hL3 : 3 ≤ L := by omega
  have hX0 : 0 < X := by linarith
  have hE0 : 0 ≤ p * X := (mul_pos hp0 hX0).le
  have hC0 : 0 ≤ (1 - p) / X := div_nonneg (by linarith) hX0.le
  unfold PfailTor
  set ωE := p * X with hωE
  set ωC := (1 - p) / X with hωC
  set Eg := torEdges L with hEg
  set geo := lam ^ (L - 1 - K) / (1 - lam) with hgeo
  have hgeo0 : 0 ≤ geo := div_nonneg (pow_nonneg hlam0 _) (by linarith)
  -- the vertex lists without repetitions
  set nlists : Finset (List (TorV L)) :=
    (univ : Finset {l : List (TorV L) // l.Nodup}).map (Function.Embedding.subtype _) with hnlists
  have mem_nlists : ∀ l, l ∈ nlists ↔ l.Nodup := by
    intro l
    simp only [hnlists, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨l', rfl⟩
      exact l'.2
    · exact fun h => ⟨⟨l, h⟩, rfl⟩
  -- the good labelled cycles
  set I := (nlists ×ˢ Eg.powerset).filter (fun x : List (TorV L) × Finset (Sym2 (Vx (TorV L))) =>
    x.2 ⊆ pedges (clist x.1) ∧ #(pedges (clist x.1) \ x.2) ≤ #x.2 ∧
      ∃ v0 rest, x.1 = v0 :: rest ∧ L ≤ rest.length + 1 ∧ (clist x.1).IsChain (decGraph Eg).Adj ∧
        LegalG (nxtT L) (ExclT L0) (K + 1) (qoff v0) (patOfT x.2 (v0 :: rest))) with hI
  -- every failing error meets a good labelled cycle exactly in its E-edges
  have hincl : ∀ E ⊆ Eg, (∃ C, IsMinCorr Eg (bd E) C ∧ FailsT E C) →
      ∃ x ∈ I, E ∩ pedges (clist x.1) = x.2 := by
    intro E hE hfail
    obtain ⟨C, hC⟩ := exists_phiMinFailT (phiTor L) hfail
    have hR : C ∆ E ⊆ Eg := fun e he =>
      (Finset.mem_union.mp (Finset.symmDiff_subset_union he)).elim (fun h => hC.1.1 h) (fun h => hE h)
    have hbd : bd (C ∆ E) = ∅ := by
      rw [bd_symmDiff, hC.1.2.1, symmDiff_self, Finset.bot_eq_empty]
    obtain ⟨v0, rest, hnd, hlen, hch, hsub, -⟩ := nontrivial_cycle hL3 hR hbd hC.2.1
    have h2 : 2 ≤ rest.length := by omega
    have hch' : (clist (v0 :: rest)).IsChain (decGraph (C ∆ E)).Adj := hch
    have hsub' : pedges (clist (v0 :: rest)) ⊆ C ∆ E := hsub
    have hγEg : pedges (clist (v0 :: rest)) ⊆ Eg := hsub'.trans hR
    have hvs : ((v0 :: rest).map Vx.det).IsChain (decGraph (C ∆ E)).Adj := by
      rw [clist_cons, List.isChain_append] at hch'
      exact hch'.1
    have hadj : AdjChainT (v0 :: rest) := adjChainT_of_isChain hR (v0 :: rest) hvs
    refine ⟨(v0 :: rest, E ∩ pedges (clist (v0 :: rest))), ?_, rfl⟩
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, mem_nlists]
    refine ⟨⟨hnd, Finset.inter_subset_left.trans hE⟩, Finset.inter_subset_right, ?_, v0, rest, rfl, hlen,
      hch'.imp (fun _ _ h => decGraph_mono hR h), ?_⟩
    · have h := half_weight_unif hC.1 hγEg (bd_cycle hnd h2) (by rw [symmDiff_comm]; exact hsub')
      have e1 : pedges (clist (v0 :: rest)) \ (E ∩ pedges (clist (v0 :: rest))) =
          pedges (clist (v0 :: rest)) \ E := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [e1, Finset.inter_comm]
      exact h
    · have hpat : patOfT (E ∩ pedges (clist (v0 :: rest))) (v0 :: rest) = patOfT E (v0 :: rest) := by
        apply patOfT_congr
        intro e he
        have := ledges_sub_clist v0 rest he
        simp only [Finset.mem_inter]
        tauto
      rw [hpat]
      refine ⟨selfAv_patOfT hL3 E hadj hnd, dirOK_patOfT E _, ?_⟩
      intro i m hm2 hmK him
      rw [length_patOfT] at him
      have hi : i < rest.length + 1 := by simp at him; omega
      rw [offAt_patOfT hL3 E v0 rest hadj i hi]
      exact hwin E C hE hC (v0 :: rest) hnd hvs i m hm2 hmK (by simp at him ⊢; omega)
  -- the union bound
  have hunion : PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsT E C) ≤
      ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges (clist x.1) = x.2) :=
    le_trans (PrIID_mono Eg hp0.le hp1.le hincl) (PrIID_exists_le Eg hp0.le hp1.le I _)
  -- the facts about a good labelled cycle
  have hfacts : ∀ x ∈ I, ∃ v0 rest, x.1 = v0 :: rest ∧ L ≤ rest.length + 1 ∧ (v0 :: rest).Nodup ∧
      AdjChainT (v0 :: rest) ∧ pedges (clist x.1) ⊆ Eg ∧ x.2 ⊆ pedges (clist x.1) ∧
      #(pedges (clist x.1) \ x.2) ≤ #x.2 ∧ LegalG (nxtT L) (ExclT L0) (K + 1) (qoff v0) (patOfT x.2 (v0 :: rest)) := by
    intro x hx
    rw [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, mem_nlists] at hx
    obtain ⟨⟨hnd, -⟩, hS, hhalf, v0, rest, hx1, hlen, hch, hleg⟩ := hx
    have hγ : pedges (clist x.1) ⊆ Eg := fun e he => ledges_subset_of_chain hch e (List.mem_toFinset.mp he)
    rw [hx1] at hch hnd
    have hvs : ((v0 :: rest).map Vx.det).IsChain (decGraph Eg).Adj := by
      rw [clist_cons, List.isChain_append] at hch
      exact hch.1
    exact ⟨v0, rest, hx1, hlen, hnd, adjChainT_of_isChain (Finset.Subset.refl Eg) (v0 :: rest) hvs, hγ, hS, hhalf,
      hleg⟩
  -- each term, tilted
  have hterm : ∀ x ∈ I, PrIID Eg p (fun E => E ∩ pedges (clist x.1) = x.2) ≤
      ωE ^ #x.2 * ωC ^ #(pedges (clist x.1) \ x.2) := by
    intro x hx
    obtain ⟨-, -, -, -, -, -, hγ, hS, hhalf, -⟩ := hfacts x hx
    rw [PrIID_inter_eq Eg p hγ hS]
    exact tilt_unif hp0.le hp1.le hX hhalf
  -- a vertex, to define the injection
  have hL0 : 0 < L := by omega
  set vstar : TorV L := (⟨0, hL0⟩, ⟨0, hL0⟩) with hvstar
  -- the injection into (first vertex, label of the closing edge, pattern of the path part)
  set Pset : TorV L → Finset (List (ℕ × Bool)) := fun v => (Finset.Ico (L - 1) (L ^ 2)).biUnion
    (fun n => (pats 2 n).filter (LegalG (nxtT L) (ExclT L0) (K + 1) (qoff v))) with hPset
  set J : Finset (Σ _ : TorV L, Bool × List (ℕ × Bool)) := univ.sigma (fun v => univ ×ˢ Pset v) with hJ
  set f : List (TorV L) × Finset (Sym2 (Vx (TorV L))) → Σ _ : TorV L, Bool × List (ℕ × Bool) :=
    fun x => ⟨x.1.headD vstar,
      (decide (s(Vx.det (x.1.getLastD vstar), Vx.det (x.1.headD vstar)) ∉ x.2), patOfT x.2 x.1)⟩ with hf
  set g : (Σ _ : TorV L, Bool × List (ℕ × Bool)) → ℝ :=
    fun y => (if y.2.1 then ωC else ωE) * wtW ωE ωC y.2.2 with hg
  have hfx : ∀ x ∈ I, ∀ v0 rest, x.1 = v0 :: rest →
      f x = ⟨v0, (decide (s(Vx.det ((v0 :: rest).getLast (List.cons_ne_nil _ _)), Vx.det v0) ∉ x.2),
        patOfT x.2 (v0 :: rest))⟩ := by
    intro x _ v0 rest hx1
    simp only [hf, hx1, List.headD_cons, List.getLastD_eq_getLast?,
      List.getLast?_eq_some_getLast (List.cons_ne_nil v0 rest), Option.getD_some]
  have hmaps : I.image f ⊆ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v0, rest, hx1, hlen, hnd, -, -, -, -, hleg⟩ := hfacts x hx
    rw [hfx x hx v0 rest hx1, hJ, Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hPset, Finset.mem_biUnion]
    refine ⟨rest.length, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      have hcard := hnd.length_le_card
      simp only [List.length_cons, Fintype.card_prod, Fintype.card_fin] at hcard
      constructor
      · omega
      · rw [sq]
        omega
    · rw [Finset.mem_filter, mem_pats, length_patOfT]
      exact ⟨⟨by simp, dirOK_patOfT _ _⟩, hleg⟩
  have hinj : Set.InjOn f I := by
    intro x hx x' hx' hxx
    obtain ⟨v0, rest, hx1, -, -, hadj, -, hS, -, -⟩ := hfacts x hx
    obtain ⟨v0', rest', hx1', -, -, hadj', -, hS', -, -⟩ := hfacts x' hx'
    rw [hfx x hx v0 rest hx1, hfx x' hx' v0' rest' hx1', Sigma.mk.inj_iff] at hxx
    obtain ⟨rfl, hxx⟩ := hxx
    rw [heq_iff_eq, Prod.mk.injEq] at hxx
    obtain ⟨hl1, hp⟩ := hxx
    have hrest : rest = rest' := eq_of_patOfT hL3 v0 rest rest' hadj hadj' hp
    subst hrest
    have hl : x.1 = x'.1 := by rw [hx1, hx1']
    have hSS : x.2 = x'.2 := by
      ext e
      by_cases he : e ∈ pedges (clist x.1)
      · rw [hx1] at he
        rcases mem_pedges_clist he with he' | rfl
        · exact patOfT_eq_labels _ hp e he'
        · exact Assembly.mem_iff_of_decide_eq hl1
      · constructor
        · intro h
          exact absurd (hS h) he
        · intro h
          rw [hl] at he
          exact absurd (hS' h) he
    exact Prod.ext hl hSS
  have hwt : ∀ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges (clist x.1) \ x.2) = g (f x) := by
    intro x hx
    obtain ⟨v0, rest, hx1, hlen, hnd, -, -, hS, -, -⟩ := hfacts x hx
    rw [hfx x hx v0 rest hx1, hg]
    simp only
    rw [hx1] at hS ⊢
    have hcyc : (ledges (clist (v0 :: rest))).Nodup :=
      ledges_cycle_nodup (v0 := Vx.det v0) (rest := rest.map Vx.det)
        (hnd.map (fun a b h => Vx.det.inj h)) (by simp; omega)
    exact cycle_weight ωE ωC hcyc hS
  have hg0 : ∀ y ∈ J, y ∉ I.image f → 0 ≤ g y := by
    intro y _ _
    simp only [hg]
    apply mul_nonneg _ (Counting.wtW_nonneg hE0 hC0 _)
    split_ifs
    · exact hC0
    · exact hE0
  have hsum1 : ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges (clist x.1) \ x.2) ≤ ∑ y ∈ J, g y :=
    Finset.sum_le_sum_of_injOn f hinj hmaps (fun x hx => le_of_eq (hwt x hx)) hg0
  -- the patterns from each vertex, by length
  have hPsum : ∀ v : TorV L, ∑ w ∈ Pset v, wtW ωE ωC w ≤ B * geo := by
    intro v
    rw [hPset, Finset.sum_biUnion]
    · calc ∑ n ∈ Finset.Ico (L - 1) (L ^ 2),
            ∑ w ∈ (pats 2 n).filter (LegalG (nxtT L) (ExclT L0) (K + 1) (qoff v)), wtW ωE ωC w
          ≤ ∑ n ∈ Finset.Ico (L - 1) (L ^ 2), lam ^ (n - K) * B := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Ico] at hn
            exact hcount v n (by omega)
        _ = B * ∑ n ∈ Finset.Ico (L - 1) (L ^ 2), lam ^ (n - K) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun n _ => by ring)
        _ ≤ B * geo := mul_le_mul_of_nonneg_left (Assembly.geom_shift_le hlam0 hlam1 (by omega)) hB
    · intro n _ n' _ hnn'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw hw'
      rw [Finset.mem_filter, mem_pats] at hw hw'
      exact hnn' (hw.1.1.symm.trans hw'.1.1)
  -- the sum over the target
  have hJsum : ∑ y ∈ J, g y ≤ (L : ℝ) ^ 2 * ((ωE + ωC) * (B * geo)) := by
    rw [hJ, Finset.sum_sigma]
    have hv : ∀ v ∈ (univ : Finset (TorV L)), ∑ z ∈ (univ : Finset Bool) ×ˢ Pset v, g ⟨v, z⟩ ≤
        (ωE + ωC) * (B * geo) := by
      intro v _
      rw [Finset.sum_product]
      simp only [hg, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_mul]
      exact mul_le_mul_of_nonneg_left (hPsum v) (add_nonneg hC0 hE0) |>.trans (le_of_eq (by ring))
    calc ∑ v ∈ (univ : Finset (TorV L)), ∑ z ∈ (univ : Finset Bool) ×ˢ Pset v, g ⟨v, z⟩
        ≤ ∑ v ∈ (univ : Finset (TorV L)), (ωE + ωC) * (B * geo) := Finset.sum_le_sum hv
      _ = (L : ℝ) ^ 2 * ((ωE + ωC) * (B * geo)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
          push_cast
          ring
  calc PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsT E C)
      ≤ ∑ x ∈ I, PrIID Eg p (fun E => E ∩ pedges (clist x.1) = x.2) := hunion
    _ ≤ ∑ x ∈ I, ωE ^ #x.2 * ωC ^ #(pedges (clist x.1) \ x.2) := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ J, g y := hsum1
    _ ≤ (L : ℝ) ^ 2 * ((ωE + ωC) * (B * geo)) := hJsum
    _ = (L : ℝ) ^ 2 * (ωE + ωC) * B * geo := by ring

end QEC
