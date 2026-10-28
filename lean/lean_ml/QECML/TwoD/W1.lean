import QECML.TwoD.Parity

/-!
# The 2D lemma, deterministic part: Lemma (W1) and the first part of (R)

Lemma (W0, W1, R) of the proof of the 2D lemma (parity witnesses), second and third items.

* `rows_of_clusterUnion`: the blocks of interior clusters lie in rows `2 + a0, …, n_y - 3 - a0` (a bad block
  closer to a declared row would join the declared cluster).
* `lev1_parity`: for a union `𝒰` of interior clusters, the level-1 residual (the residual on the blocks of the
  odd level-0 components) has even parity in `𝒰`: add to the components of `F` meeting `𝒰` the corrections of the
  resolved level-0 components inside `𝒰`; the sum has no half-edges, and its odd checks are the level-1 residual.
* `W1`: if every cluster meeting an odd level-1 component `K1` is interior, one of these clusters contains a flagged
  block of another level-1 component, at block distance at least `a1 + 1` from `K1`.
* `omega_mem_level1` ((R), first part): every check of `Ω` lies in a block of an unresolved (odd) level-1
  component.
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- A union of interior analysis clusters: bad blocks, closed under clusters, no declared block. -/
def ClusterUnion (E : G.Ed → ZMod 2) (a0 : ℕ) (U : Set G.Block) : Prop :=
  (∀ c ∈ U, S.badD E c ∧ S.cluster E a0 c ⊆ U) ∧ ∀ c ∈ U, ¬ G.declared c

/-- Blocks of a union of interior clusters lie in rows `2 + a0, …, n_y - 3 - a0`. -/
theorem rows_of_clusterUnion {E : G.Ed → ZMod 2} {a0 : ℕ} {U : Set G.Block} (hU : S.ClusterUnion E a0 U)
    {c : G.Block} (hc : c ∈ U) : 2 + a0 ≤ c.2.val ∧ c.2.val + 3 + a0 ≤ G.ny := by
  have hnd := hU.2 c hc
  simp only [S3Geom.declared, not_or, not_lt] at hnd
  obtain ⟨hbad, hcl⟩ := hU.1 c hc
  constructor
  · by_contra hlt
    let c' : G.Block := (c.1, ⟨1, by omega⟩)
    have hdecl : G.declared c' := Or.inl (by simp [c'])
    have hdist : G.blockDist c c' ≤ a0 := by
      simp only [S3Geom.blockDist, ndist, c']
      omega
    have hmem : c' ∈ S.cluster E a0 c := ⟨hbad, .single ⟨hbad, Or.inl hdecl, hdist⟩⟩
    exact hU.2 c' (hcl hmem) hdecl
  · by_contra hlt
    let c' : G.Block := (c.1, ⟨G.ny - 2, by omega⟩)
    have hdecl : G.declared c' := Or.inr (by simp [c']; omega)
    have hdist : G.blockDist c c' ≤ a0 := by
      simp only [S3Geom.blockDist, ndist, c']
      omega
    have hmem : c' ∈ S.cluster E a0 c := ⟨hbad, .single ⟨hbad, Or.inl hdecl, hdist⟩⟩
    exact hU.2 c' (hcl hmem) hdecl

/-- A check of a union of components of `F` that start in `U` and lies in a bad block lies in `U`. -/
theorem mem_of_reach {E : G.Ed → ZMod 2} {a0 : ℕ} (ha0 : 2 ≤ a0) {U : Set G.Block} (hU : S.ClusterUnion E a0 U)
    {w v : G.V} (hw : G.blockOf w ∈ U) (hwv : Relation.ReflTransGen (S.Fadj E) w v)
    (hbad : S.badD E (G.blockOf v)) : G.blockOf v ∈ U := by
  obtain ⟨hwbad, hwcl⟩ := hU.1 _ hw
  have h1 : S.cluster E a0 (G.blockOf v) = S.cluster E a0 (G.blockOf w) :=
    S.cluster_eq_of_reach ha0 hwv hwbad hbad
  have h3 : G.blockOf v ∈ S.cluster E a0 (G.blockOf v) := S3Geom.mem_comp_self hbad
  rw [h1] at h3
  exact hwcl h3

/-- The level-0 corrections of the resolved components meeting `U`. -/
noncomputable def corr0 (a0 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (U : Set G.Block) : G.Ed → ZMod 2 :=
  ∑ K ∈ (G.comps (S3Geom.flaggedSet (S.resid E)) a0).filter
      (fun K => G.resolved (S.resid E) ((a0 + 1) / 2) K ∧ ∃ c ∈ K, c ∈ U),
    Z.solve (G.region K ((a0 + 1) / 2)) (G.restrictTo K (S.resid E))

/-- **Level-1 residual parity**: in a union of interior clusters, the residual on the level-1 blocks has even
parity. -/
theorem lev1_parity {E : G.Ed → ZMod 2} {a0 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {U : Set G.Block}
    (hU : S.ClusterUnion E a0 U) :
    ∑ v, G.restrictTo (U ∩ S3Geom.level1Set (S.resid E) a0) (S.resid E) v = 0 := by
  set Q : Set G.V := {v | ∃ w, G.blockOf w ∈ U ∧ Relation.ReflTransGen (S.Fadj E) w v} with hQdef
  have hQ : ∀ u v, u ∈ Q → S.Fadj E u v → v ∈ Q := fun u v ⟨w, hw, hwu⟩ huv => ⟨w, hw, hwu.tail huv⟩
  have hQU : ∀ v ∈ Q, S.badD E (G.blockOf v) → G.blockOf v ∈ U := by
    rintro v ⟨w, hw, hwv⟩ hbad
    exact S.mem_of_reach ha0 hU hw hwv hbad
  have hFl : ∀ c ∈ S3Geom.flaggedSet (S.resid E), S.badD E c := by
    rintro c ⟨v, hv, hD⟩
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  -- a level-0 component meeting U lies in U
  have hKU : ∀ K ∈ G.comps (S3Geom.flaggedSet (S.resid E)) a0, (∃ c ∈ K, c ∈ U) → K ⊆ U := by
    intro K hK ⟨c, hcK, hcU⟩
    obtain ⟨c', hc', rfl⟩ := S3Geom.mem_comps_iff.1 hK
    have hsub : G.comp (S3Geom.flaggedSet (S.resid E)) a0 c' ⊆ S.cluster E a0 c' :=
      S.comp_flagged_subset_cluster
    have h1 : S.cluster E a0 c = S.cluster E a0 c' := S3Geom.comp_eq_of_mem (hsub hcK)
    intro x hx
    have := hsub hx
    rw [← h1] at this
    exact (hU.1 c hcU).2 this
  -- the sum Y has no half-edges
  have hcomp : ∀ x, S.compUnion E Q (.bot x) = 0 ∧ S.compUnion E Q (.top x) = 0 := by
    intro x
    constructor <;> simp only [compUnion] <;> split_ifs with hx <;> try rfl
    · obtain ⟨v, hv, hvQ⟩ := hx
      simp only [PEdge.ends, Finset.mem_singleton] at hv
      subst hv
      have hdecl := S3Geom.declared_of_rough (G := G) (v := (x, 0)) (Or.inl rfl)
      exact absurd hdecl (hU.2 _ (hQU _ hvQ (Or.inl hdecl)))
    · obtain ⟨v, hv, hvQ⟩ := hx
      simp only [PEdge.ends, Finset.mem_singleton] at hv
      subst hv
      have hdecl := S3Geom.declared_of_rough (G := G) (v := (x, Fin.last _)) (Or.inr rfl)
      exact absurd hdecl (hU.2 _ (hQU _ hvQ (Or.inl hdecl)))
  have hcorr : ∀ x, S.corr0 a0 Z E U (.bot x) = 0 ∧ S.corr0 a0 Z E U (.top x) = 0 := by
    intro x
    simp only [corr0, Finset.sum_apply]
    constructor <;> refine Finset.sum_eq_zero fun K hK => ?_ <;>
      obtain ⟨hK1, hres, hmeet⟩ := Finset.mem_filter.1 hK <;>
      obtain ⟨c', hc', rfl⟩ := S3Geom.mem_comps_iff.1 hK1 <;>
      have hins := Z.inside _ _ (S3Geom.realizable_resolved hc' hres) <;>
      by_contra hne
    · obtain ⟨k, hk, hkd⟩ := hins _ hne (x, 0) (by simp [PEdge.ends])
      have hrows := S.rows_of_clusterUnion hU (hKU _ hK1 hmeet hk)
      simp only [S3Geom.blockDist, S3Geom.blockOf, S3Geom.brow, ndist, max_le_iff] at hkd
      simp only [Fin.val_zero, Nat.zero_div] at hkd
      omega
    · obtain ⟨k, hk, hkd⟩ := hins _ hne (x, Fin.last _) (by simp [PEdge.ends])
      have hrows := S.rows_of_clusterUnion hU (hKU _ hK1 hmeet hk)
      simp only [S3Geom.blockDist, S3Geom.blockOf, S3Geom.brow, ndist, max_le_iff, Fin.val_last] at hkd
      have hL := G.hL
      have hh := G.h_succ
      have h1 : (G.ny - 1) * G.L ≤ G.h := by
        have : (G.ny - 1) * G.L = G.ny * G.L - G.L := by rw [Nat.sub_mul, one_mul]
        omega
      have h2 : G.ny - 1 ≤ G.h / G.L := (Nat.le_div_iff_mul_le (by omega)).2 h1
      have h3 : G.h / G.L < G.ny := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      generalize G.h / G.L = t at hkd h2 h3
      omega
  have hnohalf : ∀ x, (S.compUnion E Q + S.corr0 a0 Z E U) (.bot x) = 0 ∧
      (S.compUnion E Q + S.corr0 a0 Z E U) (.top x) = 0 := fun x =>
    ⟨by simp [(hcomp x).1, (hcorr x).1], by simp [(hcomp x).2, (hcorr x).2]⟩
  have hsum := sum_psyn_eq_zero hnohalf
  rw [← hsum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hcorrsyn : psyn G.w G.h (S.corr0 a0 Z E U) =
      ∑ K ∈ (G.comps (S3Geom.flaggedSet (S.resid E)) a0).filter
        (fun K => G.resolved (S.resid E) ((a0 + 1) / 2) K ∧ ∃ c ∈ K, c ∈ U), G.restrictTo K (S.resid E) := by
    rw [corr0, map_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    obtain ⟨hK1, hres, _⟩ := Finset.mem_filter.1 hK
    obtain ⟨c, hc, rfl⟩ := S3Geom.mem_comps_iff.1 hK1
    exact Z.correct _ _ (S3Geom.realizable_resolved hc hres)
  rw [map_add, Pi.add_apply, S.psyn_restrictQ E hQ v, hcorrsyn, Finset.sum_apply, S.psyn_Fcfg,
    S3Geom.sum_restrict_comps]
  by_cases hD : S.resid E v = 0
  · simp [S3Geom.restrictTo, hD]
  · have hb : G.blockOf v ∈ S3Geom.flaggedSet (S.resid E) := ⟨v, rfl, hD⟩
    have hbad := hFl _ hb
    have hQiff : v ∈ Q ↔ G.blockOf v ∈ U := ⟨fun h => hQU v h hbad, fun h => ⟨v, h, .refl⟩⟩
    have hmeet : (∃ c ∈ G.comp (S3Geom.flaggedSet (S.resid E)) a0 (G.blockOf v), c ∈ U) ↔
        G.blockOf v ∈ U := by
      constructor
      · rintro ⟨c, hc, hcU⟩
        exact hKU _ (S3Geom.mem_comps_iff.2 ⟨_, hb, rfl⟩) ⟨c, hc, hcU⟩ (S3Geom.mem_comp_self hb)
      · intro h
        exact ⟨_, S3Geom.mem_comp_self hb, h⟩
    by_cases hU' : G.blockOf v ∈ U
    · have hm : ∃ c ∈ G.comp (S3Geom.flaggedSet (S.resid E)) a0 (G.blockOf v), c ∈ U := hmeet.2 hU'
      have hQv : v ∈ Q := hQiff.2 hU'
      by_cases hres : G.resolved (S.resid E) ((a0 + 1) / 2) (G.comp (S3Geom.flaggedSet (S.resid E)) a0 (G.blockOf v))
      · have hn1 : G.blockOf v ∉ U ∩ S3Geom.level1Set (S.resid E) a0 := fun h => h.2.2 hres
        simp only [S3Geom.restrictTo, hn1, hQv, hb, hres, hm, ↓reduceIte]
        simp [zmod2_add_self]
      · have h1 : G.blockOf v ∈ U ∩ S3Geom.level1Set (S.resid E) a0 := ⟨hU', hb, hres⟩
        simp [S3Geom.restrictTo, h1, hQv, hres]
    · have hn1 : G.blockOf v ∉ U ∩ S3Geom.level1Set (S.resid E) a0 := fun h => hU' h.1
      have hQv : v ∉ Q := fun h => hU' (hQiff.1 h)
      have hm : ¬ ∃ c ∈ G.comp (S3Geom.flaggedSet (S.resid E)) a0 (G.blockOf v), c ∈ U :=
        fun h => hU' (hmeet.1 h)
      simp [S3Geom.restrictTo, hn1, hQv, hm]

/-- **Lemma (W1)**: if every cluster meeting an odd level-1 component `K1` is interior, one of these clusters
contains a flagged block of another level-1 component, at block distance at least `a1 + 1` from `K1`. -/
theorem W1 {E : G.Ed → ZMod 2} {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (Z : Solver G) {c1 : G.Block}
    (hint : ∀ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1, Interior (S.cluster E a0 k))
    (hodd : ∑ v, G.restrictTo (G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1) (S.resid E) v ≠ 0) :
    ∃ c'' ∈ S3Geom.level1Set (S.resid E) a0,
      (∃ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1, c'' ∈ S.cluster E a0 k) ∧
        ∀ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1, a1 < G.blockDist k c'' := by
  have hB1bad : ∀ c ∈ S3Geom.level1Set (S.resid E) a0, S.badD E c := by
    rintro c ⟨⟨v, hv, hD⟩, _⟩
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  set U : Set G.Block :=
    {c | ∃ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1, c ∈ S.cluster E a0 k} with hUdef
  have hU : S.ClusterUnion E a0 U := by
    refine ⟨fun c ⟨k, hk, hck⟩ => ⟨S3Geom.comp_subset hck, fun x hx => ⟨k, hk, ?_⟩⟩,
      fun c ⟨k, hk, hck⟩ => hint k hk c hck⟩
    have h : S.cluster E a0 c = S.cluster E a0 k := S3Geom.comp_eq_of_mem hck
    rw [← h]
    exact hx
  have hpar := S.lev1_parity ha0 Z hU
  have hK1sub : ∀ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1,
      k ∈ U ∩ S3Geom.level1Set (S.resid E) a0 := fun k hk =>
    ⟨⟨k, hk, S3Geom.mem_comp_self (hB1bad k (S3Geom.comp_subset hk))⟩, S3Geom.comp_subset hk⟩
  have hex : ∃ v, G.blockOf v ∈ U ∩ S3Geom.level1Set (S.resid E) a0 ∧
      G.blockOf v ∉ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1 ∧ S.resid E v ≠ 0 := by
    by_contra hne'
    have hne : ∀ v, G.blockOf v ∈ U ∩ S3Geom.level1Set (S.resid E) a0 →
        G.blockOf v ∉ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1 → S.resid E v = 0 := fun v h1 h2 => by
      by_contra h3
      exact hne' ⟨v, h1, h2, h3⟩
    apply hodd
    rw [← hpar]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv1 : G.blockOf v ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 c1
    · have hm := hK1sub _ hv1
      simp only [S3Geom.restrictTo, hv1, hm, ↓reduceIte]
    · by_cases hvU : G.blockOf v ∈ U ∩ S3Geom.level1Set (S.resid E) a0
      · simp only [S3Geom.restrictTo, hv1, hvU, ↓reduceIte, hne v hvU hv1]
      · simp only [S3Geom.restrictTo, hv1, hvU, ↓reduceIte]
  obtain ⟨v, ⟨hvU, hvB1⟩, hv1, hD⟩ := hex
  refine ⟨G.blockOf v, hvB1, hvU, fun k hk => ?_⟩
  by_contra hle'
  have hle : G.blockDist k (G.blockOf v) ≤ a1 := not_lt.1 hle'
  apply hv1
  obtain ⟨hroot, hreach⟩ := hk
  exact ⟨hroot, hreach.tail ⟨S3Geom.comp_subset ⟨hroot, hreach⟩, hvB1, hle⟩⟩

/-- **(R), first part**: every check of `Ω` lies in a block of an unresolved level-1 component. -/
theorem omega_mem_level1 {Dp : G.V → ZMod 2} {a0 a1 : ℕ} {v : G.V} (hv : S3Geom.omegaSyn Dp a0 a1 v ≠ 0) :
    G.blockOf v ∈ S3Geom.level1Set Dp a0 ∧
      ¬ G.resolved Dp ((a1 + 1) / 2) (G.comp (S3Geom.level1Set Dp a0) a1 (G.blockOf v)) := by
  simp only [S3Geom.omegaSyn] at hv
  split_ifs at hv with h
  · exact h
  · exact absurd rfl hv

end Stage1

end QECML
