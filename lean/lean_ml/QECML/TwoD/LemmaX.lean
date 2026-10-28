import QECML.TwoD.LemmaC

/-!
# Lemma X (exchange), (R) second part, and the strip families of Lemma C

* `exchange` (Lemma X, general form): for a nonnegative solver weight, any part `P` of `C_top` weighs at most any
  edge set `P'` with the same odd checks (otherwise `C_top + P + P'` would be a lighter correction of `Ω`).
* `om_far` ((R), second part): odd checks of `Ω` in different families lie in blocks more than `a1` apart.
* `strip_bot_of_pcls`, `strip_top_of_pclsT`: a family whose `Y_𝓕` has odd degree at `b₁` (`b₂`) has a block in
  the bottom (top) strip; `T1_of_spanning`: a family with odd degree at both is a T1 family.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The weight of an edge set: the sum of `wt` over its support. -/
noncomputable def wsum (wt : G.Ed → ℝ) (X : G.Ed → ZMod 2) : ℝ := ∑ e, if X e ≠ 0 then wt e else 0

theorem wsum_add_le {wt : G.Ed → ℝ} (hwt : ∀ e, 0 ≤ wt e) (X Y : G.Ed → ZMod 2) :
    wsum wt (X + Y) ≤ wsum wt X + wsum wt Y := by
  unfold wsum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hw := hwt e
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (X e) with hx | hx <;> rcases zmod2_cases (Y e) with hy | hy
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy, h11]
    linarith

/-- Removing a part of an edge set lowers its weight by the weight of the part. -/
theorem wsum_add_of_subset {wt : G.Ed → ℝ} {X Y : G.Ed → ZMod 2} (h : ∀ e, X e ≠ 0 → Y e ≠ 0) :
    wsum wt (Y + X) = wsum wt Y - wsum wt X := by
  unfold wsum
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases zmod2_cases (X e) with hx | hx <;> rcases zmod2_cases (Y e) with hy | hy
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · exact absurd hy (h e (by rw [hx]; exact one_ne_zero))
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    simp [Pi.add_apply, hx, hy, this]

/-- **Lemma X (exchange), general form.** -/
theorem exchange (Z : Solver G) (hwt : ∀ e, 0 ≤ Z.wt e) {T : G.V → ZMod 2} {P P' : G.Ed → ZMod 2}
    (hP : ∀ e, P e ≠ 0 → Z.solve Set.univ T e ≠ 0) (hpsyn : psyn G.w G.h P' = psyn G.w G.h P)
    (hT : psyn G.w G.h (Z.solve Set.univ T) = T) :
    wsum Z.wt P ≤ wsum Z.wt P' := by
  have hmin := Z.minimal Set.univ T (Z.solve Set.univ T + P + P') (fun _ _ _ _ => Set.mem_univ _) (by
    rw [map_add, map_add, hT, hpsyn]
    funext v
    simp only [Pi.add_apply]
    rw [add_assoc, zmod2_add_self, add_zero])
  have h1 := wsum_add_le hwt (Z.solve Set.univ T + P) P'
  have h2 := wsum_add_of_subset (wt := Z.wt) hP
  unfold wsum at hmin h1 h2 ⊢
  linarith

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- **(R), second part**: odd checks of `Ω` in different families lie in blocks more than `a1` apart (they lie in
different level-1 components). -/
theorem om_far {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {u v : G.V} (hu : S.om a0 a1 E u ≠ 0) (hv : S.om a0 a1 E v ≠ 0)
    (hne : S.family a0 a1 E (G.blockOf u) ≠ S.family a0 a1 E (G.blockOf v)) :
    a1 < G.blockDist (G.blockOf u) (G.blockOf v) := by
  have hlev : ∀ {x : G.V}, S.om a0 a1 E x ≠ 0 → G.blockOf x ∈ S.lev1 a0 E := fun {x} hx => by
    simp only [om, S3Geom.omegaSyn] at hx
    split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx
  refine not_le.mp fun hd => hne ?_
  have hu1 := hlev hu
  have hv1 := hlev hv
  have hvmem : G.blockOf v ∈ G.comp (S.lev1 a0 E) a1 (G.blockOf u) := ⟨hu1, .single ⟨hu1, hv1, hd⟩⟩
  have hlink : S.linked a0 a1 E (G.blockOf u) (G.blockOf v) :=
    ⟨S.badD_of_lev1 hu1, S.badD_of_lev1 hv1, Or.inr ⟨hu1, hv1, (S3Geom.comp_eq_of_mem hvmem).symm⟩⟩
  exact (S.family_eq_of_mem ⟨S.badD_of_lev1 hu1, .single hlink⟩).symm

theorem top_row (x : Fin (G.w + 1)) : G.ny ≤ (G.blockOf (x, Fin.last G.h)).2.val + 1 := by
  have hL := G.hL
  have hny := G.hny
  have hh := G.h_succ
  simp only [S3Geom.blockOf, S3Geom.brow, Fin.val_last]
  have h1 : (G.ny - 1) * G.L ≤ G.h := by
    have : (G.ny - 1) * G.L = G.ny * G.L - G.L := by rw [Nat.sub_mul, one_mul]
    omega
  have h2 : G.ny - 1 ≤ G.h / G.L := (Nat.le_div_iff_mul_le (by omega)).2 h1
  omega

theorem badD_top (E : G.Ed → ZMod 2) (x : Fin (G.w + 1)) : S.badD E (G.blockOf (x, Fin.last G.h)) :=
  Or.inl (S3Geom.declared_of_rough (Or.inr rfl))

/-- A family whose `Y_𝓕` has odd degree at `b₁` has a block in the bottom strip. -/
theorem strip_bot_of_pcls {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (ha01 : a0 ≤ a1) (Z : Solver G) {E : G.Ed → ZMod 2}
    {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E) (h : pcls G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0) :
    ∃ c ∈ Fm, c.2.val ≤ hs a1 := by
  rw [pcls_apply] at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hrow0 : (G.blockOf ((x, 0) : G.V)).2.val = 0 := by simp [S3Geom.blockOf, S3Geom.brow]
  -- a nonzero summand of `Y_𝓕` at the half-edge
  simp only [Yfam, Pi.add_apply, Finset.sum_apply] at hx
  by_cases h1 : S.compUnion E (S.famQ E Fm) (.bot x) ≠ 0
  · have hQ : ((x, 0) : G.V) ∈ S.famQ E Fm := by
      by_contra hn
      exact h1 (by simp [compUnion, PEdge.ends, hn])
    exact ⟨_, S.mem_of_famQ ha0 hFm hQ (S.badD_bot E x), by rw [hrow0]; exact Nat.zero_le _⟩
  · push Not at h1
    rw [h1, zero_add] at hx
    -- a resolved component's correction contains the half-edge, so its region reaches row 0
    have hreg : ∀ (K : Set G.Block) (r : ℕ), K ⊆ Fm → r ≤ hs a1 → Z.solve (G.region K r)
        (G.restrictTo K (S.resid E)) (.bot x) ≠ 0 →
        G.Realizable (G.region K r) (G.restrictTo K (S.resid E)) → ∃ c ∈ Fm, c.2.val ≤ hs a1 := by
      intro K r hKF hr hne hreal
      have hin := Z.inside _ _ hreal (.bot x) hne (x, 0) (by simp [PEdge.ends])
      obtain ⟨k, hk, hdk⟩ := hin
      have := S3Geom.row_le_add_blockDist (G.blockOf ((x, 0) : G.V)) k
      rw [hrow0] at this
      exact ⟨k, hKF hk, by omega⟩
    by_cases h2 : (∑ K ∈ (S.res0 a0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
        S.corrK Z ((a0 + 1) / 2) E K (.bot x)) ≠ 0
    · obtain ⟨K, hK, hKx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
      obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
      exact hreg _ _ (S.res0_subset hFm hKr hk hkF) (by simp only [hs]; omega) hKx
        (S3Geom.realizable_resolved hc hres)
    · push Not at h2
      rw [h2, zero_add] at hx
      obtain ⟨K, hK, hKx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
      obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
      exact hreg _ _ (S.res1_subset hFm hKr hk hkF) (by simp only [hs]; omega) hKx
        (S3Geom.realizable_resolved hc hres)

/-- A family whose `Y_𝓕` has odd degree at `b₂` has a block in the top strip. -/
theorem strip_top_of_pclsT {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (ha01 : a0 ≤ a1) (Z : Solver G) {E : G.Ed → ZMod 2}
    {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E) (h : pclsT G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0) :
    ∃ c ∈ Fm, G.ny ≤ c.2.val + 1 + hs a1 := by
  rw [pclsT_apply] at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hrow := top_row (G := G) x
  simp only [Yfam, Pi.add_apply, Finset.sum_apply] at hx
  by_cases h1 : S.compUnion E (S.famQ E Fm) (.top x) ≠ 0
  · have hQ : ((x, Fin.last G.h) : G.V) ∈ S.famQ E Fm := by
      by_contra hn
      exact h1 (by simp [compUnion, PEdge.ends, hn])
    exact ⟨_, S.mem_of_famQ ha0 hFm hQ (S.badD_top E x), by omega⟩
  · push Not at h1
    rw [h1, zero_add] at hx
    have hreg : ∀ (K : Set G.Block) (r : ℕ), K ⊆ Fm → r ≤ hs a1 → Z.solve (G.region K r)
        (G.restrictTo K (S.resid E)) (.top x) ≠ 0 →
        G.Realizable (G.region K r) (G.restrictTo K (S.resid E)) → ∃ c ∈ Fm, G.ny ≤ c.2.val + 1 + hs a1 := by
      intro K r hKF hr hne hreal
      have hin := Z.inside _ _ hreal (.top x) hne (x, Fin.last G.h) (by simp [PEdge.ends])
      obtain ⟨k, hk, hdk⟩ := hin
      have := S3Geom.row_le_add_blockDist k (G.blockOf ((x, Fin.last G.h) : G.V))
      rw [G.blockDist_comm] at this
      exact ⟨k, hKF hk, by omega⟩
    by_cases h2 : (∑ K ∈ (S.res0 a0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
        S.corrK Z ((a0 + 1) / 2) E K (.top x)) ≠ 0
    · obtain ⟨K, hK, hKx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
      obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
      exact hreg _ _ (S.res0_subset hFm hKr hk hkF) (by simp only [hs]; omega) hKx
        (S3Geom.realizable_resolved hc hres)
    · push Not at h2
      rw [h2, zero_add] at hx
      obtain ⟨K, hK, hKx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
      obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
      exact hreg _ _ (S.res1_subset hFm hKr hk hkF) (by simp only [hs]; omega) hKx
        (S3Geom.realizable_resolved hc hres)

/-- A family with odd degree at both boundaries (a spanning family) is a T1 family. -/
theorem T1_of_spanning {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (ha01 : a0 ≤ a1) (Z : Solver G) {E : G.Ed → ZMod 2}
    {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E) (h1 : pcls G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0)
    (h2 : pclsT G.w G.h (S.Yfam a0 a1 Z E Fm) ≠ 0) : S.T1 a0 a1 E := by
  obtain ⟨c0, hc0, rfl⟩ := (S.mem_families).1 hFm
  obtain ⟨c1, hc1, hr1⟩ := S.strip_bot_of_pcls ha0 ha01 Z hFm h1
  obtain ⟨c2, hc2, hr2⟩ := S.strip_top_of_pclsT ha0 ha01 Z hFm h2
  exact ⟨c0, hc0, ⟨c1, hc1, hr1⟩, ⟨c2, hc2, hr2⟩⟩

end Stage1

/-- A reflexive-transitive chain contains a simple one (a path with distinct nodes). -/
theorem exists_simple_chain {α : Type*} {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
      List.IsChain (fun x y => x ≠ y ∧ (r x y ∨ r y x)) l := by
  have hreach : (SimpleGraph.fromRel r).Reachable a b := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    induction h with
    | refl => exact .refl
    | @tail c d _ hcd ih =>
      by_cases hc : c = d
      · rw [← hc]
        exact ih
      · exact ih.tail ((SimpleGraph.fromRel_adj r c d).2 ⟨hc, Or.inl hcd⟩)
  obtain ⟨w⟩ := hreach
  refine ⟨w.toPath.1.support, ?_, ?_, w.toPath.isPath.support_nodup, ?_⟩
  · rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.getLast_support]
  · exact (SimpleGraph.Walk.isChain_adj_support w.toPath.1).imp fun x y hxy =>
      (SimpleGraph.fromRel_adj r x y).1 hxy

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- **Lemma C, path form**: if S3' fails, a simple path of `Γ` runs from `b₁` to `b₂`. Its
family nodes are distinct; consecutive families are joined by runs of `C_top` edges between odd checks of `Ω`
(check-check edges of `Γ` are bulk edges of `C_top`); a family node next to both boundaries is a spanning family
(`T1_of_spanning`). -/
theorem lemmaC_path {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {E : G.Ed → ZMod 2}
    (hfail : failsOn (S3Geom.S3dec S a0 a1 Z) E) :
    ∃ l : List G.GNode, l.head? = some (.inr (.inl false)) ∧ l.getLast? = some (.inr (.inl true)) ∧
      l.Nodup ∧ List.IsChain (S.gadj a0 a1 Z E) l := by
  obtain ⟨l, hh, hl, hnd, hch⟩ := exists_simple_chain (S.lemmaC ha0 Z hfail)
  refine ⟨l, hh, hl, hnd, hch.imp fun x y hxy => ?_⟩
  rcases hxy.2 with h | h
  · exact h
  · exact h.symm

end Stage1

end QECML
