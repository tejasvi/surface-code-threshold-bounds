import QECML.TwoD.Headline

/-!
# Lemma B (decomposition; step (B) of the paper's proof outline)

For a family `𝓕` (analysis clusters linked by level-1 components), `Y_𝓕` is the sum of the components of `F` meeting
`𝓕` and of the resolved corrections `C_K` of the level-0 and level-1 components inside `𝓕` (`Yfam`).

* `psyn_Yfam` (Lemma B, first part): `∂Y_𝓕 = Ω ∩ 𝓕`.
* `pcls_decomp` (Lemma B, class part): the class of `E + C` is the class of `C_top` plus the classes of the
  `Y_𝓕` (the components of `F` meeting no bad block carry no half-edge: a half-edge's check lies in a declared row).
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-! ### Families as block sets -/

theorem mem_family_iff {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} :
    c' ∈ S.family a0 a1 E c ↔ S.badD E c ∧ Relation.ReflTransGen (S.linked a0 a1 E) c c' := Iff.rfl

theorem mem_family_self {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c : G.Block} (hc : S.badD E c) :
    c ∈ S.family a0 a1 E c := ⟨hc, .refl⟩

theorem badD_of_mem_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} (h : c' ∈ S.family a0 a1 E c) :
    S.badD E c' :=
  S.badD_of_linked_reach h.1 h.2

theorem family_eq_of_mem {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} (h : c' ∈ S.family a0 a1 E c) :
    S.family a0 a1 E c' = S.family a0 a1 E c := by
  obtain ⟨hc, hcc'⟩ := h
  have hc' : S.badD E c' := S.badD_of_linked_reach hc hcc'
  ext x
  constructor
  · rintro ⟨_, hx⟩
    exact ⟨hc, hcc'.trans hx⟩
  · rintro ⟨_, hx⟩
    exact ⟨hc', (S.linked_reach_symm hcc').trans hx⟩

theorem mem_family_of_cluster {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} (hc : S.badD E c)
    (h : c' ∈ S.cluster E a0 c) : c' ∈ S.family a0 a1 E c := by
  have hc' : S.badD E c' := S3Geom.comp_subset h
  exact ⟨hc, .single ⟨hc, hc', Or.inl (S3Geom.comp_eq_of_mem h).symm⟩⟩

/-- The families, as a finite set of block sets. -/
noncomputable def families (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : Finset (Set G.Block) :=
  (univ.filter (fun c => S.badD E c)).image (S.family a0 a1 E)

theorem mem_families {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm : Set G.Block} :
    Fm ∈ S.families a0 a1 E ↔ ∃ c, S.badD E c ∧ S.family a0 a1 E c = Fm := by
  simp [families]

/-- A family is the family of each of its blocks. -/
theorem family_eq_of_mem_families {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm : Set G.Block}
    (hFm : Fm ∈ S.families a0 a1 E) {c : G.Block} (hc : c ∈ Fm) : S.family a0 a1 E c = Fm := by
  obtain ⟨c0, _, rfl⟩ := (S.mem_families).1 hFm
  exact S.family_eq_of_mem hc

theorem family_mem_families {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c : G.Block} (hc : S.badD E c) :
    S.family a0 a1 E c ∈ S.families a0 a1 E :=
  (S.mem_families).2 ⟨c, hc, rfl⟩

/-- Two families sharing a block are equal. -/
theorem families_eq_of_mem {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm Fm' : Set G.Block}
    (hFm : Fm ∈ S.families a0 a1 E) (hFm' : Fm' ∈ S.families a0 a1 E) {c : G.Block} (hc : c ∈ Fm)
    (hc' : c ∈ Fm') : Fm = Fm' :=
  (S.family_eq_of_mem_families hFm hc).symm.trans (S.family_eq_of_mem_families hFm' hc')

/-! ### Components inside families -/

/-- A level-0 component lies in the family of each of its blocks. -/
theorem comp0_subset_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c k : G.Block}
    (hk : k ∈ G.comp (S3Geom.flaggedSet (S.resid E)) a0 c) :
    G.comp (S3Geom.flaggedSet (S.resid E)) a0 c ⊆ S.family a0 a1 E k := by
  have hbad : ∀ x, x ∈ S3Geom.flaggedSet (S.resid E) → S.badD E x := by
    rintro x ⟨v, hv, hD⟩
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  intro x hx
  have hkc : S.cluster E a0 k = S.cluster E a0 c :=
    S3Geom.comp_eq_of_mem (S.comp_flagged_subset_cluster hk)
  have hxc : x ∈ S.cluster E a0 c := S.comp_flagged_subset_cluster hx
  rw [← hkc] at hxc
  exact S.mem_family_of_cluster (hbad k (S3Geom.comp_subset hk)) hxc

/-- A level-1 component lies in the family of each of its blocks. -/
theorem comp1_subset_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c k : G.Block}
    (hk : k ∈ G.comp (S.lev1 a0 E) a1 c) : G.comp (S.lev1 a0 E) a1 c ⊆ S.family a0 a1 E k := by
  intro x hx
  have hk1 : k ∈ S.lev1 a0 E := S3Geom.comp_subset hk
  have hx1 : x ∈ S.lev1 a0 E := S3Geom.comp_subset hx
  refine ⟨S.badD_of_lev1 hk1, .single ⟨S.badD_of_lev1 hk1, S.badD_of_lev1 hx1, Or.inr ⟨hk1, hx1, ?_⟩⟩⟩
  rw [S3Geom.comp_eq_of_mem hk, S3Geom.comp_eq_of_mem hx]

/-! ### The checks of the components of `F` meeting a family -/

/-- The checks reachable through `F` from the blocks of `Fm`. -/
def famQ (E : G.Ed → ZMod 2) (Fm : Set G.Block) : Set G.V :=
  {v | ∃ w, G.blockOf w ∈ Fm ∧ Relation.ReflTransGen (S.Fadj E) w v}

theorem famQ_closed (E : G.Ed → ZMod 2) (Fm : Set G.Block) :
    ∀ u v, u ∈ S.famQ E Fm → S.Fadj E u v → v ∈ S.famQ E Fm :=
  fun _ _ ⟨w, hw, hwu⟩ huv => ⟨w, hw, hwu.tail huv⟩

/-- **Lemma A for families**: a check of `famQ Fm` in a bad block lies in a block of `Fm`. -/
theorem mem_of_famQ {a0 a1 : ℕ} (ha0 : 2 ≤ a0) {E : G.Ed → ZMod 2} {Fm : Set G.Block}
    (hFm : Fm ∈ S.families a0 a1 E) {v : G.V} (hv : v ∈ S.famQ E Fm) (hbad : S.badD E (G.blockOf v)) :
    G.blockOf v ∈ Fm := by
  obtain ⟨w, hw, hwv⟩ := hv
  have hwbad : S.badD E (G.blockOf w) := by
    rw [← S.family_eq_of_mem_families hFm hw] at hw
    exact S.badD_of_mem_family hw
  have hcl := S.cluster_eq_of_reach ha0 hwv hwbad hbad
  have hvcl : G.blockOf v ∈ S.cluster E a0 (G.blockOf w) := by
    rw [← hcl]
    exact S.mem_cluster_self hbad
  have := S.mem_family_of_cluster (a1 := a1) hwbad hvcl
  rwa [S.family_eq_of_mem_families hFm hw] at this

/-! ### `Y_𝓕` -/

/-- The resolved level-0 components. -/
noncomputable def res0 (a0 : ℕ) (E : G.Ed → ZMod 2) : Finset (Set G.Block) :=
  (G.comps (S3Geom.flaggedSet (S.resid E)) a0).filter (G.resolved (S.resid E) ((a0 + 1) / 2))

/-- The resolved level-1 components. -/
noncomputable def res1 (a0 a1 : ℕ) (E : G.Ed → ZMod 2) : Finset (Set G.Block) :=
  (G.comps (S3Geom.level1Set (S.resid E) a0) a1).filter (G.resolved (S.resid E) ((a1 + 1) / 2))

/-- The correction of a component (radius `r`). -/
noncomputable def corrK (Z : Solver G) (r : ℕ) (E : G.Ed → ZMod 2) (K : Set G.Block) : G.Ed → ZMod 2 :=
  Z.solve (G.region K r) (G.restrictTo K (S.resid E))

/-- **`Y_𝓕`**: the components of `F` meeting `Fm` and the resolved corrections of the components inside `Fm`. -/
noncomputable def Yfam (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (Fm : Set G.Block) : G.Ed → ZMod 2 :=
  S.compUnion E (S.famQ E Fm) +
    ∑ K ∈ (S.res0 a0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((a0 + 1) / 2) E K +
    ∑ K ∈ (S.res1 a0 a1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((a1 + 1) / 2) E K

theorem psyn_corrK0 {a0 : ℕ} (Z : Solver G) {E : G.Ed → ZMod 2} {K : Set G.Block} (hK : K ∈ S.res0 a0 E) :
    psyn G.w G.h (S.corrK Z ((a0 + 1) / 2) E K) = G.restrictTo K (S.resid E) := by
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
  exact Z.correct _ _ (S3Geom.realizable_resolved hc hres)

theorem psyn_corrK1 {a0 a1 : ℕ} (Z : Solver G) {E : G.Ed → ZMod 2} {K : Set G.Block}
    (hK : K ∈ S.res1 a0 a1 E) :
    psyn G.w G.h (S.corrK Z ((a1 + 1) / 2) E K) = G.restrictTo K (S.resid E) := by
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
  exact Z.correct _ _ (S3Geom.realizable_resolved hc hres)

/-- A resolved level-0 component meeting a family lies in it. -/
theorem res0_subset {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E)
    {K : Set G.Block} (hK : K ∈ S.res0 a0 E) {k : G.Block} (hk : k ∈ K) (hkF : k ∈ Fm) : K ⊆ Fm := by
  obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 (Finset.mem_filter.1 hK).1
  have := S.comp0_subset_family (a1 := a1) hk
  rwa [S.family_eq_of_mem_families hFm hkF] at this

/-- A resolved level-1 component meeting a family lies in it. -/
theorem res1_subset {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Fm : Set G.Block} (hFm : Fm ∈ S.families a0 a1 E)
    {K : Set G.Block} (hK : K ∈ S.res1 a0 a1 E) {k : G.Block} (hk : k ∈ K) (hkF : k ∈ Fm) : K ⊆ Fm := by
  obtain ⟨c, _, rfl⟩ := S3Geom.mem_comps_iff.1 (Finset.mem_filter.1 hK).1
  have := S.comp1_subset_family (a0 := a0) (a1 := a1) (E := E) hk
  rwa [S.family_eq_of_mem_families hFm hkF] at this

/-- Every resolved level-0 component meets exactly one family. -/
theorem res0_unique_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {K : Set G.Block} (hK : K ∈ S.res0 a0 E) :
    ∃! Fm, Fm ∈ S.families a0 a1 E ∧ ∃ c ∈ K, c ∈ Fm := by
  obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 (Finset.mem_filter.1 hK).1
  have hcbad : S.badD E c := by
    obtain ⟨v, hv, hD⟩ := hc
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  refine ⟨S.family a0 a1 E c, ⟨S.family_mem_families hcbad, c, S3Geom.mem_comp_self hc,
    S.mem_family_self hcbad⟩, fun Fm ⟨hFm, k, hk, hkF⟩ => ?_⟩
  have hsub := S.res0_subset hFm hK hk hkF
  exact S.families_eq_of_mem hFm (S.family_mem_families hcbad) (hsub (S3Geom.mem_comp_self hc))
    (S.mem_family_self hcbad)

/-- Every resolved level-1 component meets exactly one family. -/
theorem res1_unique_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {K : Set G.Block} (hK : K ∈ S.res1 a0 a1 E) :
    ∃! Fm, Fm ∈ S.families a0 a1 E ∧ ∃ c ∈ K, c ∈ Fm := by
  obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 (Finset.mem_filter.1 hK).1
  have hc1 : c ∈ S.lev1 a0 E := hc
  have hcbad : S.badD E c := S.badD_of_lev1 hc1
  refine ⟨S.family a0 a1 E c, ⟨S.family_mem_families hcbad, c, S3Geom.mem_comp_self hc,
    S.mem_family_self hcbad⟩, fun Fm ⟨hFm, k, hk, hkF⟩ => ?_⟩
  have hsub := S.res1_subset hFm hK hk hkF
  exact S.families_eq_of_mem hFm (S.family_mem_families hcbad) (hsub (S3Geom.mem_comp_self hc))
    (S.mem_family_self hcbad)

end Stage1

namespace S3Geom

variable {G : S3Geom}

/-- The residual is partitioned among the resolved components of both levels and `Ω`. -/
theorem resid_partition (Dp : G.V → ZMod 2) (a0 a1 : ℕ) (v : G.V) :
    (∑ K ∈ (G.comps (flaggedSet Dp) a0).filter (G.resolved Dp ((a0 + 1) / 2)), G.restrictTo K Dp v) +
      (∑ K ∈ (G.comps (level1Set Dp a0) a1).filter (G.resolved Dp ((a1 + 1) / 2)), G.restrictTo K Dp v) +
      omegaSyn Dp a0 a1 v = Dp v := by
  rw [sum_restrict_comps, sum_restrict_comps]
  simp only [omegaSyn]
  by_cases hv : Dp v = 0
  · simp [hv]
  · have hfl : G.blockOf v ∈ flaggedSet Dp := ⟨v, rfl, hv⟩
    by_cases h0 : G.resolved Dp ((a0 + 1) / 2) (G.comp (flaggedSet Dp) a0 (G.blockOf v))
    · have hn1 : G.blockOf v ∉ level1Set Dp a0 := fun h => h.2 h0
      simp [hfl, h0, hn1]
    · have h1 : G.blockOf v ∈ level1Set Dp a0 := ⟨hfl, h0⟩
      by_cases hr1 : G.resolved Dp ((a1 + 1) / 2) (G.comp (level1Set Dp a0) a1 (G.blockOf v))
      · simp [hfl, h0, h1, hr1]
      · simp [hfl, h0, h1, hr1]

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- **Lemma B, first part**: `∂Y_𝓕 = Ω ∩ 𝓕`. -/
theorem psyn_Yfam {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {E : G.Ed → ZMod 2} {Fm : Set G.Block}
    (hFm : Fm ∈ S.families a0 a1 E) :
    psyn G.w G.h (S.Yfam a0 a1 Z E Fm) = G.restrictTo Fm (S3Geom.omegaSyn (S.resid E) a0 a1) := by
  funext v
  have hsum0 : ∀ K ∈ (S.res0 a0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
      psyn G.w G.h (S.corrK Z ((a0 + 1) / 2) E K) v = G.restrictTo K (S.resid E) v :=
    fun K hK => by rw [S.psyn_corrK0 Z (Finset.mem_filter.1 hK).1]
  have hsum1 : ∀ K ∈ (S.res1 a0 a1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
      psyn G.w G.h (S.corrK Z ((a1 + 1) / 2) E K) v = G.restrictTo K (S.resid E) v :=
    fun K hK => by rw [S.psyn_corrK1 Z (Finset.mem_filter.1 hK).1]
  simp only [Yfam, map_add, map_sum, Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl hsum0, Finset.sum_congr rfl hsum1, S.psyn_restrictQ E (S.famQ_closed E Fm),
    S.psyn_Fcfg]
  have hpart := S3Geom.resid_partition (S.resid E) a0 a1 v
  by_cases hv : G.blockOf v ∈ Fm
  · -- every component containing the block of `v` meets `Fm`
    have hvQ : v ∈ S.famQ E Fm := ⟨v, hv, .refl⟩
    rw [Finset.sum_filter_of_ne fun K _ hK => ?_, Finset.sum_filter_of_ne fun K _ hK => ?_]
    · simp only [S3Geom.restrictTo, hv, hvQ, ↓reduceIte, res0, res1]
      simp only [S3Geom.restrictTo] at hpart
      linear_combination hpart + zmod2_add_self (S.resid E v) -
        zmod2_add_self (S3Geom.omegaSyn (S.resid E) a0 a1 v)
    · simp only [S3Geom.restrictTo] at hK
      split_ifs at hK with h
      · exact ⟨G.blockOf v, h, hv⟩
      · exact absurd rfl hK
    · simp only [S3Geom.restrictTo] at hK
      split_ifs at hK with h
      · exact ⟨G.blockOf v, h, hv⟩
      · exact absurd rfl hK
  · -- no term reaches `v`
    have h0 : ∀ K ∈ (S.res0 a0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), G.restrictTo K (S.resid E) v = 0 := by
      intro K hK
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      simp only [S3Geom.restrictTo]
      split_ifs with h
      · exact absurd (S.res0_subset hFm hKr hk hkF h) hv
      · rfl
    have h1 : ∀ K ∈ (S.res1 a0 a1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
        G.restrictTo K (S.resid E) v = 0 := by
      intro K hK
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      simp only [S3Geom.restrictTo]
      split_ifs with h
      · exact absurd (S.res1_subset hFm hKr hk hkF h) hv
      · rfl
    rw [Finset.sum_eq_zero h0, Finset.sum_eq_zero h1]
    simp only [S3Geom.restrictTo, hv, ↓reduceIte, add_zero]
    split_ifs with hvQ
    · by_contra hne
      exact hv (S.mem_of_famQ ha0 hFm hvQ (Or.inr (Or.inl ⟨v, rfl, hne⟩)))
    · rfl

theorem sum_ite_unique {ι M : Type*} [AddCommMonoid M] {s : Finset ι} {P : ι → Prop} [DecidablePred P]
    (a : M) (h : ∃! i, i ∈ s ∧ P i) : ∑ i ∈ s, (if P i then a else 0) = a := by
  obtain ⟨i0, ⟨hi0s, hi0P⟩, huniq⟩ := h
  rw [Finset.sum_eq_single_of_mem i0 hi0s fun j hj hji => by
    rw [ite_eq_right (fun hP => hji (huniq j ⟨hj, hP⟩))]]
  simp [hi0P]

/-- Regrouping a sum over components by the unique family each meets. -/
theorem sum_by_family {M : Type*} [AddCommMonoid M] {a0 a1 : ℕ} {E : G.Ed → ZMod 2}
    (s : Finset (Set G.Block)) (hs : ∀ K ∈ s, ∃! Fm, Fm ∈ S.families a0 a1 E ∧ ∃ c ∈ K, c ∈ Fm)
    (f : Set G.Block → M) :
    ∑ K ∈ s, f K = ∑ Fm ∈ S.families a0 a1 E, ∑ K ∈ s.filter (fun K => ∃ c ∈ K, c ∈ Fm), f K := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun K hK => (sum_ite_unique (f K) (hs K hK)).symm

/-- The check of a bottom half-edge lies in a declared block. -/
theorem badD_bot (E : G.Ed → ZMod 2) (x : Fin (G.w + 1)) : S.badD E (G.blockOf (x, 0)) :=
  Or.inl (Or.inl (by simp [S3Geom.blockOf, S3Geom.brow]))

/-- **The components of `F` by family, at the bottom boundary**: every bottom half-edge of `F` lies in exactly
one `famQ`. -/
theorem pcls_Fcfg {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (E : G.Ed → ZMod 2) :
    pcls G.w G.h (S.Fcfg E) = ∑ Fm ∈ S.families a0 a1 E, pcls G.w G.h (S.compUnion E (S.famQ E Fm)) := by
  simp only [pcls_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hbot : ∀ Fm, S.compUnion E (S.famQ E Fm) (.bot x) =
      if (x, 0) ∈ S.famQ E Fm then S.Fcfg E (.bot x) else 0 := fun Fm => by
    simp [compUnion, PEdge.ends]
  simp only [hbot]
  refine (sum_ite_unique _ ?_).symm
  have hb := S.badD_bot E x
  refine ⟨S.family a0 a1 E (G.blockOf (x, 0)), ⟨S.family_mem_families hb,
    ⟨(x, 0), S.mem_family_self hb, .refl⟩⟩, fun Fm ⟨hFm, hx⟩ => ?_⟩
  exact S.families_eq_of_mem hFm (S.family_mem_families hb) (S.mem_of_famQ ha0 hFm hx hb)
    (S.mem_family_self hb)

/-- **Lemma B, class part**: the class of `E + C` is the class of `C_top` plus the classes of the `Y_𝓕`. -/
theorem pcls_decomp {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) (E : G.Ed → ZMod 2) :
    pcls G.w G.h (E + S3Geom.S3dec S a0 a1 Z (psyn G.w G.h E)) =
      pcls G.w G.h (Z.solve Set.univ (S3Geom.omegaSyn (S.resid E) a0 a1)) +
        ∑ Fm ∈ S.families a0 a1 E, pcls G.w G.h (S.Yfam a0 a1 Z E Fm) := by
  have hdec : E + S3Geom.S3dec S a0 a1 Z (psyn G.w G.h E) =
      S.Fcfg E + ∑ K ∈ S.res0 a0 E, S.corrK Z ((a0 + 1) / 2) E K +
        ∑ K ∈ S.res1 a0 a1 E, S.corrK Z ((a1 + 1) / 2) E K +
        Z.solve Set.univ (S3Geom.omegaSyn (S.resid E) a0 a1) := by
    show E + (S.C0 (psyn G.w G.h E) + ∑ K ∈ S.res0 a0 E, S.corrK Z ((a0 + 1) / 2) E K +
        ∑ K ∈ S.res1 a0 a1 E, S.corrK Z ((a1 + 1) / 2) E K +
        Z.solve Set.univ (S3Geom.omegaSyn (S.resid E) a0 a1)) = _
    simp only [Fcfg]
    abel
  rw [hdec, map_add, map_add, map_add, map_sum, map_sum, S.pcls_Fcfg (a1 := a1) ha0 E,
    S.sum_by_family (S.res0 a0 E) (fun K hK => S.res0_unique_family hK),
    S.sum_by_family (S.res1 a0 a1 E) (fun K hK => S.res1_unique_family hK)]
  simp only [Yfam, map_add, map_sum, Finset.sum_add_distrib]
  abel

end Stage1

end QECML
