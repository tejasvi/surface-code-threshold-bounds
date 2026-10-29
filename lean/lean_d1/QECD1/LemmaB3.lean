import QECD1.Decoder3

/-!
# Lemma B (decomposition) on the 3D code

The 3D analogue of the 2D `TwoD/LemmaB`. For the decoder (stage-1 rule `S`, solver `Z`, noise `E`), the families
are those of `gen_skel3_final`: `famF F L e` with `F = badSet` (bad and declared blocks) and `L = levSet` (the
decoder's level-1 blocks, `lev1Set3_eq`).

* `families3`: the families as a finite set; two families sharing a block are equal (`families3_eq_of_mem`).
* `edgesIn X Q`: the part of `X` on edges with an end in `Q`. For `Q` closed under `X`-adjacency its syndrome is the
  syndrome of `X` restricted to `Q` (`psyn3_edgesIn`).
* `mem_of_famQ` (Lemma A for families): a check of `compUnion3 X Fm` in a block of `F` lies in a block of `Fm`.
* `Yfam3 Fm`: the part of `F = E + C_0` on the components meeting `Fm`, plus the corrections of the resolved
  components (both levels) meeting `Fm`.
* `psyn3_Yfam3` (Lemma B, first part): `∂Y_𝓕 = Ω ∩ 𝓕`.
* `pcls3`: the logical class, the parity of the error on the bottom half-edges at all times. `pcls3_decomp` (Lemma B,
  class part): the class of `E + C` is the class of `C_top` plus the classes of the `Y_𝓕`. Every bottom half-edge
  ends in a declared block, which lies in exactly one family.
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

/-! ### Families of `F` linked by `L` -/

theorem linked3_symm {F L : Finset V3} {c c' : V3} (hcc : Linked3 F L c c') : Linked3 F L c' c := by
  obtain ⟨hc, hc', hl⟩ := hcc
  refine ⟨hc', hc, ?_⟩
  rcases hl with h0 | ⟨h1, h2, h3⟩
  · exact Or.inl (sameComp_symm F Const.a0 h0)
  · exact Or.inr ⟨h2, h1, sameComp_symm L Const.a1 h3⟩

theorem inFamily3_symm {F L : Finset V3} {e x : V3} (hex : InFamily3 F L e x) : InFamily3 F L x e := by
  induction hex with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (linked3_symm hbc) ih

theorem self_mem_famF {F L : Finset V3} {e : V3} (he : e ∈ F) : e ∈ famF F L e := mem_famF.2 ⟨he, .refl⟩

theorem famF_eq_of_mem {F L : Finset V3} {e b : V3} (hb : b ∈ famF F L e) : famF F L b = famF F L e := by
  obtain ⟨_, heb⟩ := mem_famF.1 hb
  ext x
  simp only [mem_famF]
  constructor
  · rintro ⟨hx, hbx⟩
    exact ⟨hx, heb.trans hbx⟩
  · rintro ⟨hx, hex⟩
    exact ⟨hx, (inFamily3_symm heb).trans hex⟩

/-- The families of `F` linked by `L`. -/
noncomputable def families3 (F L : Finset V3) : Finset (Finset V3) := F.image (famF F L)

theorem mem_families3 {F L : Finset V3} {Fm : Finset V3} : Fm ∈ families3 F L ↔ ∃ c ∈ F, famF F L c = Fm := by
  unfold families3
  rw [Finset.mem_image]

theorem famF_mem_families3 {F L : Finset V3} {c : V3} (hc : c ∈ F) : famF F L c ∈ families3 F L :=
  mem_families3.2 ⟨c, hc, rfl⟩

/-- A family is the family of each of its blocks. -/
theorem famF_eq_of_mem_families3 {F L : Finset V3} {Fm : Finset V3} (hFm : Fm ∈ families3 F L) {c : V3}
    (hc : c ∈ Fm) : famF F L c = Fm := by
  obtain ⟨c0, _, rfl⟩ := mem_families3.1 hFm
  exact famF_eq_of_mem hc

/-- Two families sharing a block are equal. -/
theorem families3_eq_of_mem {F L : Finset V3} {Fm Fm' : Finset V3} (hFm : Fm ∈ families3 F L)
    (hFm' : Fm' ∈ families3 F L) {c : V3} (hc : c ∈ Fm) (hc' : c ∈ Fm') : Fm = Fm' :=
  (famF_eq_of_mem_families3 hFm hc).symm.trans (famF_eq_of_mem_families3 hFm' hc')

/-- A cluster lies in the family of each of its blocks. -/
theorem cluster_sub_famF {F L : Finset V3} {e c : V3} (hc : c ∈ famF F L e) : clusterOf F c ⊆ famF F L e := by
  intro x hx
  obtain ⟨hxF, hcx⟩ := mem_clusterOf.1 hx
  obtain ⟨hcF, hec⟩ := mem_famF.1 hc
  exact mem_famF.2 ⟨hxF, hec.tail ⟨hcF, hxF, Or.inl hcx⟩⟩

/-- A level-0 component (of a subset `Fl` of `F`) meeting a family lies in it. -/
theorem comp0_sub_family {F L Fl : Finset V3} (hFl : Fl ⊆ F) {Fm : Finset V3} (hFm : Fm ∈ families3 F L) {c k : V3}
    (hk : k ∈ compOf Fl Const.a0 c) (hkF : k ∈ Fm) : compOf Fl Const.a0 c ⊆ Fm := by
  intro x hx
  obtain ⟨hkFl, hck⟩ := mem_compOf.1 hk
  obtain ⟨hxFl, hcx⟩ := mem_compOf.1 hx
  have hkx : SameComp F Const.a0 k x := sameComp_mono_set hFl ((sameComp_symm Fl Const.a0 hck).trans hcx)
  have hsub := cluster_sub_famF (L := L) (e := k) (self_mem_famF (hFl hkFl))
  rw [famF_eq_of_mem_families3 hFm hkF] at hsub
  exact hsub (mem_clusterOf.2 ⟨hFl hxFl, hkx⟩)

/-- A level-1 component meeting a family lies in it. -/
theorem comp1_sub_family {F L : Finset V3} (hLF : L ⊆ F) {Fm : Finset V3} (hFm : Fm ∈ families3 F L) {c k : V3}
    (hk : k ∈ compOf L Const.a1 c) (hkF : k ∈ Fm) : compOf L Const.a1 c ⊆ Fm := by
  intro x hx
  obtain ⟨hkL, hck⟩ := mem_compOf.1 hk
  obtain ⟨hxL, hcx⟩ := mem_compOf.1 hx
  have hkx : SameComp L Const.a1 k x := (sameComp_symm L Const.a1 hck).trans hcx
  have hmem : x ∈ famF F L k := mem_famF.2 ⟨hLF hxL, .single ⟨hLF hkL, hLF hxL, Or.inr ⟨hkL, hxL, hkx⟩⟩⟩
  rwa [famF_eq_of_mem_families3 hFm hkF] at hmem

/-! ### The part of `X` on a set of checks -/

/-- The part of `X` on the edges with an end in `Q`. -/
noncomputable def edgesIn (X : PEdge3 T w h → ZMod 2) (Q : Finset (PVert3 T w h)) : PEdge3 T w h → ZMod 2 :=
  fun e => if ∃ v ∈ e.ends, v ∈ Q then X e else 0

/-- For `Q` closed under `X`-adjacency, the syndrome of the part of `X` on `Q` is the syndrome of `X` restricted to
`Q`. -/
theorem psyn3_edgesIn {X : PEdge3 T w h → ZMod 2} {Q : Finset (PVert3 T w h)}
    (hQ : ∀ u ∈ Q, ∀ v, Fadj X u v → v ∈ Q) (v : PVert3 T w h) :
    psyn3 (edgesIn X Q) v = if v ∈ Q then psyn3 X v else 0 := by
  unfold psyn3 edgesIn
  split_ifs with hv
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [if_pos ⟨v, (Finset.mem_filter.1 he).2, hv⟩]
  · refine Finset.sum_eq_zero fun e he => ?_
    have hve := (Finset.mem_filter.1 he).2
    split_ifs with hQe
    · obtain ⟨u, hue, huQ⟩ := hQe
      rcases zmod2_cases (X e) with h0 | h1
      · exact h0
      · exact absurd (hQ u huQ v ⟨e, h1, hue, hve⟩) hv
    · rfl

/-- **Lemma A for families**: a check of `compUnion3 X Fm` in a block of `F` lies in a block of `Fm`. -/
theorem mem_of_famQ {X : PEdge3 T w h → ZMod 2} {F L : Finset V3} (hlong : ∀ c, c ∉ F → NotLong3 X c)
    {Fm : Finset V3} (hFm : Fm ∈ families3 F L) (hFmF : Fm ⊆ F) {v : PVert3 T w h} (hv : v ∈ compUnion3 X Fm)
    (hvF : blockOf3 v ∈ F) : blockOf3 v ∈ Fm := by
  obtain ⟨u, hu, huv⟩ := mem_compUnion3.1 hv
  have hcl := a3_code3 X F hlong u v huv (hFmF hu) hvF
  have hsub := cluster_sub_famF (L := L) (e := blockOf3 u) (self_mem_famF (hFmF hu))
  rw [famF_eq_of_mem_families3 hFm hu] at hsub
  exact hsub (mem_clusterOf.2 ⟨hvF, hcl⟩)

theorem families3_sub {F L Fm : Finset V3} (hFm : Fm ∈ families3 F L) : Fm ⊆ F := by
  obtain ⟨c, _, rfl⟩ := mem_families3.1 hFm
  exact famF_sub F L c

/-! ### The logical class -/

/-- The logical class: the parity of the edge set on the bottom half-edges, at all times. -/
noncomputable def pcls3 (X : PEdge3 T w h → ZMod 2) : ZMod 2 := ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), X (.bot t x)

theorem pcls3_add (X Y : PEdge3 T w h → ZMod 2) : pcls3 (X + Y) = pcls3 X + pcls3 Y := by
  simp only [pcls3, Pi.add_apply, Finset.sum_add_distrib]

theorem pcls3_zero : pcls3 (0 : PEdge3 T w h → ZMod 2) = 0 := by
  simp [pcls3]

theorem pcls3_sum {ι : Type} (s : Finset ι) (X : ι → PEdge3 T w h → ZMod 2) :
    pcls3 (∑ i ∈ s, X i) = ∑ i ∈ s, pcls3 (X i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact pcls3_zero
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, pcls3_add, ih]

theorem sum_ite_unique {ι M : Type} [AddCommMonoid M] {s : Finset ι} {P : ι → Prop} [DecidablePred P]
    (a : M) (hP : ∃! i, i ∈ s ∧ P i) : ∑ i ∈ s, (if P i then a else 0) = a := by
  obtain ⟨i0, ⟨hi0s, hi0P⟩, huniq⟩ := hP
  rw [Finset.sum_eq_single_of_mem i0 hi0s fun j hj hji => by
    rw [ite_eq_right_iff.2 (fun hPj => absurd (huniq j ⟨hj, hPj⟩) hji)]]
  simp [hi0P]

/-- The residual is partitioned among the resolved components of both levels and `Ω`. -/
theorem resid_partition3 (Dp : PVert3 T w h → ZMod 2) (v : PVert3 T w h) :
    (∑ K ∈ (comps3 (flagSet3 Dp) Const.a0).filter (Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))),
        restrict3 K Dp v) +
      (∑ K ∈ (comps3 (lev1Set3 Dp) Const.a1).filter (Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))),
        restrict3 K Dp v) + omega3 Dp v = Dp v := by
  rw [sum_restrict_comps3, sum_restrict_comps3]
  simp only [omega3]
  by_cases hv : Dp v = 0
  · simp [hv]
  · have hfl : blockOf3 v ∈ flagSet3 Dp := Finset.mem_filter.2 ⟨blockOf3_mem_latBlocks v, v, rfl, hv⟩
    by_cases h0 : Resolved3 (parOf Dp) (reach3 T w h r0) (clusterOf (flagSet3 Dp) (blockOf3 v))
    · have hn1 : blockOf3 v ∉ lev1Set3 Dp := fun h1 => (mem_level1Set3.1 h1).2 h0
      have h0' : Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))
          (compOf (flagSet3 Dp) Const.a0 (blockOf3 v)) := h0
      simp [hfl, h0', hn1]
    · have h1 : blockOf3 v ∈ lev1Set3 Dp := mem_level1Set3.2 ⟨hfl, h0⟩
      have h0' : ¬ Resolved3 (parOf Dp) (reach3 T w h ((Const.a0 + 1) / 2))
          (compOf (flagSet3 Dp) Const.a0 (blockOf3 v)) := h0
      by_cases hr1 : Resolved3 (parOf Dp) (reach3 T w h r1) (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v))
      · have hr1' : Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))
            (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v)) := hr1
        simp [hfl, h0', h1, hr1, hr1']
      · have hr1' : ¬ Resolved3 (parOf Dp) (reach3 T w h ((Const.a1 + 1) / 2))
            (compOf (lev1Set3 Dp) Const.a1 (blockOf3 v)) := hr1
        simp [hfl, h0', h1, hr1, hr1']

/-! ### Lemma B for the decoder -/

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- The resolved level-0 components. -/
noncomputable def res0 (E : PEdge3 T w h → ZMod 2) : Finset (Finset V3) :=
  (comps3 (flagSet3 (residD3 S (psyn3 E))) Const.a0).filter
    (Resolved3 (parOf (residD3 S (psyn3 E))) (reach3 T w h ((Const.a0 + 1) / 2)))

/-- The resolved level-1 components. -/
noncomputable def res1 (E : PEdge3 T w h → ZMod 2) : Finset (Finset V3) :=
  (comps3 (lev1Set3 (residD3 S (psyn3 E))) Const.a1).filter
    (Resolved3 (parOf (residD3 S (psyn3 E))) (reach3 T w h ((Const.a1 + 1) / 2)))

/-- The correction of a component (radius `r`). -/
noncomputable def corrK (r : ℕ) (E : PEdge3 T w h → ZMod 2) (K : Finset V3) : PEdge3 T w h → ZMod 2 :=
  Z.solve (region3 K r) (restrict3 K (residD3 S (psyn3 E)))

/-- **`Y_𝓕`**: the part of `E + C_0` on the components meeting `Fm`, and the corrections of the resolved components
meeting `Fm`. -/
noncomputable def Yfam3 (E : PEdge3 T w h → ZMod 2) (Fm : Finset V3) : PEdge3 T w h → ZMod 2 :=
  edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) +
    ∑ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a0 + 1) / 2) E K +
    ∑ K ∈ (S.res1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a1 + 1) / 2) E K

theorem psyn3_corrK0 {E : PEdge3 T w h → ZMod 2} {K : Finset V3} (hK : K ∈ S.res0 E) :
    psyn3 (S.corrK Z ((Const.a0 + 1) / 2) E K) = restrict3 K (residD3 S (psyn3 E)) := by
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK1
  exact Z.correct _ _ (realizable_resolved (flagSet3_blocks _) hres)

theorem psyn3_corrK1 {E : PEdge3 T w h → ZMod 2} {K : Finset V3} (hK : K ∈ S.res1 E) :
    psyn3 (S.corrK Z ((Const.a1 + 1) / 2) E K) = restrict3 K (residD3 S (psyn3 E)) := by
  obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hK
  obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK1
  exact Z.correct _ _ (realizable_resolved (lev1Set3_blocks _) hres)

variable {S}

/-- A resolved level-0 component meeting a family lies in it. -/
theorem res0_sub {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) {K : Finset V3} (hK : K ∈ S.res0 E)
    {k : V3} (hk : k ∈ K) (hkF : k ∈ Fm) : K ⊆ Fm := by
  obtain ⟨c, _, rfl⟩ := mem_comps3.1 (Finset.mem_filter.1 hK).1
  rw [flagSet3_eq] at hk ⊢
  exact comp0_sub_family (S.flSet_sub ny E) hFm hk hkF

/-- A resolved level-1 component meeting a family lies in it. -/
theorem res1_sub {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) {K : Finset V3} (hK : K ∈ S.res1 E)
    {k : V3} (hk : k ∈ K) (hkF : k ∈ Fm) : K ⊆ Fm := by
  obtain ⟨c, _, rfl⟩ := mem_comps3.1 (Finset.mem_filter.1 hK).1
  rw [lev1Set3_eq] at hk ⊢
  exact comp1_sub_family (S.levSet_sub _ ny E) hFm hk hkF

/-- Every resolved level-0 component meets exactly one family. -/
theorem res0_unique_family {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {K : Finset V3} (hK : K ∈ S.res0 E) :
    ∃! Fm, Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ ∃ c ∈ K, c ∈ Fm := by
  obtain ⟨c, hc, rfl⟩ := mem_comps3.1 (Finset.mem_filter.1 hK).1
  have hcF : c ∈ S.badSet ny E := S.flSet_sub ny E (by rwa [flagSet3_eq] at hc)
  refine ⟨famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) c, ⟨famF_mem_families3 hcF, c, self_mem_compOf hc,
    self_mem_famF hcF⟩, fun Fm ⟨hFm, k, hk, hkF⟩ => ?_⟩
  have hsub := res0_sub hFm hK hk hkF
  exact families3_eq_of_mem hFm (famF_mem_families3 hcF) (hsub (self_mem_compOf hc)) (self_mem_famF hcF)

/-- Every resolved level-1 component meets exactly one family. -/
theorem res1_unique_family {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {K : Finset V3} (hK : K ∈ S.res1 E) :
    ∃! Fm, Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ ∃ c ∈ K, c ∈ Fm := by
  obtain ⟨c, hc, rfl⟩ := mem_comps3.1 (Finset.mem_filter.1 hK).1
  have hcF : c ∈ S.badSet ny E := S.levSet_sub _ ny E (by rwa [lev1Set3_eq] at hc)
  refine ⟨famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) c, ⟨famF_mem_families3 hcF, c, self_mem_compOf hc,
    self_mem_famF hcF⟩, fun Fm ⟨hFm, k, hk, hkF⟩ => ?_⟩
  have hsub := res1_sub hFm hK hk hkF
  exact families3_eq_of_mem hFm (famF_mem_families3 hcF) (hsub (self_mem_compOf hc)) (self_mem_famF hcF)

variable (S)

/-- **Lemma B, first part**: `∂Y_𝓕 = Ω ∩ 𝓕`. -/
theorem psyn3_Yfam3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) :
    psyn3 (S.Yfam3 Z E Fm) = restrict3 Fm (omega3 (residD3 S (psyn3 E))) := by
  funext v
  have hX : psyn3 (S.Fcfg E) = residD3 S (psyn3 E) := (residD3_eq S E).symm
  have hsum0 : ∀ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
      psyn3 (S.corrK Z ((Const.a0 + 1) / 2) E K) v = restrict3 K (residD3 S (psyn3 E)) v :=
    fun K hK => by rw [S.psyn3_corrK0 Z (Finset.mem_filter.1 hK).1]
  have hsum1 : ∀ K ∈ (S.res1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm),
      psyn3 (S.corrK Z ((Const.a1 + 1) / 2) E K) v = restrict3 K (residD3 S (psyn3 E)) v :=
    fun K hK => by rw [S.psyn3_corrK1 Z (Finset.mem_filter.1 hK).1]
  have hY : psyn3 (S.Yfam3 Z E Fm) v = psyn3 (edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm)) v +
      ∑ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), psyn3 (S.corrK Z ((Const.a0 + 1) / 2) E K) v +
      ∑ K ∈ (S.res1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), psyn3 (S.corrK Z ((Const.a1 + 1) / 2) E K) v := by
    simp only [Yfam3, psyn3_add, psyn3_sum, Pi.add_apply, Finset.sum_apply]
  rw [hY, Finset.sum_congr rfl hsum0, Finset.sum_congr rfl hsum1,
    psyn3_edgesIn (compUnion3_closed (S.Fcfg E) Fm), hX]
  have hpart : (∑ K ∈ S.res0 E, restrict3 K (residD3 S (psyn3 E)) v) +
      (∑ K ∈ S.res1 E, restrict3 K (residD3 S (psyn3 E)) v) + omega3 (residD3 S (psyn3 E)) v =
        residD3 S (psyn3 E) v := by
    exact resid_partition3 (residD3 S (psyn3 E)) v
  by_cases hv : blockOf3 v ∈ Fm
  · have hvQ : v ∈ compUnion3 (S.Fcfg E) Fm := compUnion3_contains _ _ v hv
    rw [Finset.sum_filter_of_ne fun K _ hK => ?_, Finset.sum_filter_of_ne fun K _ hK => ?_]
    · simp only [restrict3, hv, hvQ, ↓reduceIte]
      simp only [restrict3] at hpart
      linear_combination hpart + CharTwo.add_self_eq_zero (residD3 S (psyn3 E) v) -
        CharTwo.add_self_eq_zero (omega3 (residD3 S (psyn3 E)) v)
    · simp only [restrict3] at hK
      split_ifs at hK with hvK
      · exact ⟨blockOf3 v, hvK, hv⟩
      · exact absurd rfl hK
    · simp only [restrict3] at hK
      split_ifs at hK with hvK
      · exact ⟨blockOf3 v, hvK, hv⟩
      · exact absurd rfl hK
  · have h0 : ∀ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), restrict3 K (residD3 S (psyn3 E)) v = 0 := by
      intro K hK
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      simp only [restrict3]
      split_ifs with hvK
      · exact absurd (res0_sub hFm hKr hk hkF hvK) hv
      · rfl
    have h1 : ∀ K ∈ (S.res1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), restrict3 K (residD3 S (psyn3 E)) v = 0 := by
      intro K hK
      obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
      simp only [restrict3]
      split_ifs with hvK
      · exact absurd (res1_sub hFm hKr hk hkF hvK) hv
      · rfl
    rw [Finset.sum_eq_zero h0, Finset.sum_eq_zero h1]
    simp only [restrict3, hv, ↓reduceIte, add_zero]
    split_ifs with hvQ
    · by_contra hne
      have hfl : blockOf3 v ∈ S.flSet E := by
        rw [← flagSet3_eq]
        exact Finset.mem_filter.2 ⟨blockOf3_mem_latBlocks v, v, rfl, hne⟩
      exact hv (mem_of_famQ (S.badSet_hlong ny E) hFm (families3_sub hFm) hvQ (S.flSet_sub ny E hfl))
    · rfl

/-- Regrouping a sum over components by the unique family each meets. -/
theorem sum_by_family3 {M : Type} [AddCommMonoid M] {F L : Finset V3} (s : Finset (Finset V3))
    (hs : ∀ K ∈ s, ∃! Fm, Fm ∈ families3 F L ∧ ∃ c ∈ K, c ∈ Fm) (f : Finset V3 → M) :
    ∑ K ∈ s, f K = ∑ Fm ∈ families3 F L, ∑ K ∈ s.filter (fun K => ∃ c ∈ K, c ∈ Fm), f K := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun K hK => (sum_ite_unique (f K) (hs K hK)).symm

/-- The check of a bottom half-edge lies in a declared block. -/
theorem declared_bot (ny : ℕ) (t : Fin (T + 1)) (x : Fin (w + 1)) :
    declared3 ny (blockOf3 ((t, x, 0) : PVert3 T w h)) := by
  left
  simp [blockOf3, blockOf, PVert3.toV3]

/-- **The components of `E + C_0` by family, at the bottom boundary**: every bottom half-edge lies in exactly one
`compUnion3` of a family. -/
theorem pcls3_Fcfg {ny : ℕ} (E : PEdge3 T w h → ZMod 2) :
    pcls3 (S.Fcfg E) = ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
      pcls3 (edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm)) := by
  have hpt : ∀ t x, S.Fcfg E (.bot t x) = ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
      edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.bot t x) := by
    intro t x
    have hbot : ∀ Fm, edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.bot t x) =
        if (t, x, 0) ∈ compUnion3 (S.Fcfg E) Fm then S.Fcfg E (.bot t x) else 0 := fun Fm => by
      simp [edgesIn, PEdge3.ends]
    simp only [hbot]
    refine (sum_ite_unique _ ?_).symm
    have hb : blockOf3 ((t, x, 0) : PVert3 T w h) ∈ S.badSet ny E := S.badSet_hdeclF ny E _ (declared_bot ny t x)
    refine ⟨famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 ((t, x, 0) : PVert3 T w h)),
      ⟨famF_mem_families3 hb, compUnion3_contains _ _ _ (self_mem_famF hb)⟩, fun Fm ⟨hFm, hx⟩ => ?_⟩
    exact families3_eq_of_mem hFm (famF_mem_families3 hb)
      (mem_of_famQ (S.badSet_hlong ny E) hFm (families3_sub hFm) hx hb) (self_mem_famF hb)
  calc pcls3 (S.Fcfg E)
      = ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E),
          edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.bot t x) := by
        simp only [pcls3, hpt]
    _ = ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), ∑ t : Fin (T + 1), ∑ x : Fin (w + 1),
          edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.bot t x) := by
        rw [Finset.sum_congr rfl fun t _ => Finset.sum_comm]
        exact Finset.sum_comm
    _ = _ := rfl

/-- **Lemma B, class part**: the class of `E + C` is the class of `C_top` plus the classes of the `Y_𝓕`. -/
theorem pcls3_decomp {ny : ℕ} (E : PEdge3 T w h → ZMod 2) :
    pcls3 (E + dec3 S Z (psyn3 E)) = pcls3 (Z.solve Set.univ (omega3 (residD3 S (psyn3 E)))) +
      ∑ Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E), pcls3 (S.Yfam3 Z E Fm) := by
  have hdec : E + dec3 S Z (psyn3 E) = S.Fcfg E + ∑ K ∈ S.res0 E, S.corrK Z ((Const.a0 + 1) / 2) E K +
      ∑ K ∈ S.res1 E, S.corrK Z ((Const.a1 + 1) / 2) E K + Z.solve Set.univ (omega3 (residD3 S (psyn3 E))) := by
    simp only [dec3, Fcfg, levelSum3, res0, res1, corrK]
    abel
  rw [hdec, pcls3_add, pcls3_add, pcls3_add, pcls3_sum, pcls3_sum, S.pcls3_Fcfg (ny := ny) E,
    sum_by_family3 (S.res0 E) (fun K hK => res0_unique_family hK),
    sum_by_family3 (S.res1 E) (fun K hK => res1_unique_family hK)]
  simp only [Yfam3, pcls3_add, pcls3_sum, Finset.sum_add_distrib]
  abel

end Stage13

end QECD1
