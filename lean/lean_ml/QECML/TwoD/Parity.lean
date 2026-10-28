import QECML.TwoD.LemmaA

/-!
# The 2D lemma, deterministic part: residual parity of interior clusters and Lemma (W0)

Lemma (W0, W1, R) of the proof of the 2D lemma (parity witnesses, step (W) of the paper's outline), first item, for
any admissible stage-1 rule:

* `sum_psyn_eq_zero` (handshake): an edge set without half-edges has an even number of odd checks.
* `psyn_restrictQ`: the union of the components of `F` meeting a set closed under `F`-adjacency has, as odd checks,
  the odd checks of `F` in that set.
* `interior_parity`: the residual `D'` has even parity in every interior cluster (one without declared blocks): the
  components of `F` meeting it reach neither rough side (they would meet the declared cluster, Lemma A).
* `W0`: an odd level-0 component in an interior cluster has, in the same cluster, a flagged block at block distance
  at least `a0 + 1` from it.
-/

open Finset Classical

namespace QECML

section Edges

variable {w h : ℕ}

theorem PEdge.mem_ends_pair {e : PEdge w h} {u v : PVert w h} (hu : u ∈ e.ends) (hv : v ∈ e.ends) (hne : u ≠ v) :
    e.ends = {u, v} := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv ⊢
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact Finset.pair_comm _ _
    · exact absurd rfl hne
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact Finset.pair_comm _ _
    · exact absurd rfl hne
  · exact absurd (hu.trans hv.symm) hne
  · exact absurd (hu.trans hv.symm) hne

theorem PEdge.card_ends_bulk_hor (x : Fin w) (y : Fin (h + 1)) : (PEdge.hor x y : PEdge w h).ends.card = 2 := by
  simp only [PEdge.ends]
  rw [Finset.card_pair]
  intro heq
  have := congrArg (fun v : PVert w h => v.1.val) heq
  simp at this

theorem PEdge.card_ends_bulk_ver (x : Fin (w + 1)) (y : Fin h) : (PEdge.ver x y : PEdge w h).ends.card = 2 := by
  simp only [PEdge.ends]
  rw [Finset.card_pair]
  intro heq
  have := congrArg (fun v : PVert w h => v.2.val) heq
  simp at this

/-- **Handshake**: an edge set without half-edges has an even number of odd checks. -/
theorem sum_psyn_eq_zero {X : PEdge w h → ZMod 2} (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0) :
    ∑ v, psyn w h X v = 0 := by
  simp only [psyn_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [← Finset.sum_mul]
  have hcard : (∑ v, if v ∈ f.ends then (1 : ZMod 2) else 0) = (f.ends.card : ZMod 2) := by
    rw [Finset.sum_boole]
    congr 1
    congr 1
    ext v
    simp
  rw [hcard]
  rcases f with ⟨x, y⟩ | ⟨x, y⟩ | x | x
  · rw [PEdge.card_ends_bulk_hor]
    have : (2 : ZMod 2) = 0 := by decide
    simp [this]
  · rw [PEdge.card_ends_bulk_ver]
    have : (2 : ZMod 2) = 0 := by decide
    simp [this]
  · rw [(hX x).1, mul_zero]
  · rw [(hX x).2, mul_zero]

end Edges

namespace S3Geom

variable {G : S3Geom}

/-- Checks of the rough rows lie in declared block rows. -/
theorem declared_of_rough {v : G.V} (hv : v.2 = 0 ∨ v.2 = Fin.last _) : G.declared (G.blockOf v) := by
  have hL := G.hL
  have hny := G.hny
  have hh := G.h_succ
  simp only [declared, blockOf, brow]
  rcases hv with h0 | hl
  · left
    rw [h0]
    simp
  · right
    rw [hl, Fin.val_last]
    have h1 : (G.ny - 1) * G.L ≤ G.h := by
      have : (G.ny - 1) * G.L = G.ny * G.L - G.L := by rw [Nat.sub_mul, one_mul]
      omega
    have h2 : G.ny - 1 ≤ G.h / G.L := (Nat.le_div_iff_mul_le (by omega)).2 h1
    omega

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- The union of the components of `F` meeting `Q` (as an edge set). -/
noncomputable def compUnion (E : G.Ed → ZMod 2) (Q : Set G.V) : G.Ed → ZMod 2 :=
  fun e => if ∃ v ∈ e.ends, v ∈ Q then S.Fcfg E e else 0

/-- If `Q` is closed under `F`-adjacency, the odd checks of the union of the components of `F` meeting `Q` are the
odd checks of `F` in `Q`. -/
theorem psyn_restrictQ (E : G.Ed → ZMod 2) {Q : Set G.V} (hQ : ∀ u v, u ∈ Q → S.Fadj E u v → v ∈ Q)
    (v : G.V) : psyn G.w G.h (S.compUnion E Q) v = if v ∈ Q then psyn G.w G.h (S.Fcfg E) v else 0 := by
  rw [psyn_apply]
  split_ifs with hv
  · rw [psyn_apply]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : v ∈ f.ends
    · have hY : S.compUnion E Q f = S.Fcfg E f := by
        simp [compUnion, show ∃ u ∈ f.ends, u ∈ Q from ⟨v, hf, hv⟩]
      rw [hY]
    · simp [hf]
  · refine Finset.sum_eq_zero fun f _ => ?_
    by_cases hf : v ∈ f.ends
    · have hY : S.compUnion E Q f = 0 := by
        unfold compUnion
        split_ifs with hu
        · obtain ⟨u, hu, huQ⟩ := hu
          by_contra hF
          have hne : u ≠ v := fun h => hv (h ▸ huQ)
          exact hv (hQ u v huQ ⟨f, PEdge.mem_ends_pair hu hf hne, hne, hF⟩)
        · rfl
      rw [hY, mul_zero]
    · simp [hf]

/-- Level-0 components lie inside one analysis cluster. -/
theorem comp_flagged_subset_cluster {E : G.Ed → ZMod 2} {a0 : ℕ} {c : G.Block} :
    G.comp (S3Geom.flaggedSet (S.resid E)) a0 c ⊆ S.cluster E a0 c := by
  have hsub : ∀ x, x ∈ S3Geom.flaggedSet (S.resid E) → S.badD E x := by
    rintro x ⟨v, hv, hD⟩
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  rintro x ⟨hc, hx⟩
  refine ⟨hsub c hc, ?_⟩
  induction hx with
  | refl => exact .refl
  | tail _ hbx ih => exact ih.tail ⟨hsub _ hbx.1, hsub _ hbx.2.1, hbx.2.2⟩

/-- An analysis cluster is interior if it contains no declared block. -/
def Interior (K : Set G.Block) : Prop := ∀ c ∈ K, ¬ G.declared c

/-- **Residual parity of interior clusters**: `D'` has even parity in every interior cluster. -/
theorem interior_parity {E : G.Ed → ZMod 2} {a0 : ℕ} (ha0 : 2 ≤ a0) {c : G.Block}
    (hint : Interior (S.cluster E a0 c)) :
    ∑ v, G.restrictTo (S.cluster E a0 c) (S.resid E) v = 0 := by
  set K := S.cluster E a0 c with hK
  set Q : Set G.V := {v | ∃ w, G.blockOf w ∈ K ∧ Relation.ReflTransGen (S.Fadj E) w v}
  have hQ : ∀ u v, u ∈ Q → S.Fadj E u v → v ∈ Q := fun u v ⟨w, hw, hwu⟩ huv => ⟨w, hw, hwu.tail huv⟩
  -- a check of Q in a bad block lies in K (Lemma A)
  have hQK : ∀ v ∈ Q, S.badD E (G.blockOf v) → G.blockOf v ∈ K := by
    rintro v ⟨w, hw, hwv⟩ hbad
    have hwbad : S.badD E (G.blockOf w) := S3Geom.comp_subset hw
    have h1 : S.cluster E a0 (G.blockOf v) = S.cluster E a0 (G.blockOf w) :=
      S.cluster_eq_of_reach ha0 hwv hwbad hbad
    have h2 : S.cluster E a0 (G.blockOf w) = K := S3Geom.comp_eq_of_mem hw
    have h3 : G.blockOf v ∈ S.cluster E a0 (G.blockOf v) := S3Geom.mem_comp_self hbad
    rw [h1, h2] at h3
    exact h3
  -- the union of the components of F meeting K has no half-edges
  have hnohalf : ∀ x, S.compUnion E Q (.bot x) = 0 ∧ S.compUnion E Q (.top x) = 0 := by
    intro x
    constructor <;> simp only [compUnion] <;> split_ifs with hx <;> try rfl
    · obtain ⟨v, hv, hvQ⟩ := hx
      simp only [PEdge.ends, Finset.mem_singleton] at hv
      subst hv
      have hdecl := S3Geom.declared_of_rough (G := G) (v := (x, 0)) (Or.inl rfl)
      exact absurd hdecl (hint _ (hQK _ hvQ (Or.inl hdecl)))
    · obtain ⟨v, hv, hvQ⟩ := hx
      simp only [PEdge.ends, Finset.mem_singleton] at hv
      subst hv
      have hdecl := S3Geom.declared_of_rough (G := G) (v := (x, Fin.last _)) (Or.inr rfl)
      exact absurd hdecl (hint _ (hQK _ hvQ (Or.inl hdecl)))
  have hsum := sum_psyn_eq_zero hnohalf
  rw [← hsum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [S.psyn_restrictQ E hQ v, S.psyn_Fcfg]
  simp only [S3Geom.restrictTo]
  by_cases hD : S.resid E v = 0
  · simp [hD]
  · have hbad : S.badD E (G.blockOf v) := Or.inr (Or.inl ⟨v, rfl, hD⟩)
    by_cases hvK : G.blockOf v ∈ K
    · have hvQ : v ∈ Q := ⟨v, hvK, .refl⟩
      simp [hvK, hvQ]
    · have hvQ : v ∉ Q := fun h => hvK (hQK v h hbad)
      simp [hvK, hvQ]

/-- **Lemma (W0)**: an odd level-0 component in an interior cluster has, in the same cluster, a flagged block at block
distance at least `a0 + 1` from it. -/
theorem W0 {E : G.Ed → ZMod 2} {a0 : ℕ} (ha0 : 2 ≤ a0) {c : G.Block}
    (hc : c ∈ S3Geom.flaggedSet (S.resid E)) (hint : Interior (S.cluster E a0 c))
    (hodd : ∑ v, G.restrictTo (G.comp (S3Geom.flaggedSet (S.resid E)) a0 c) (S.resid E) v ≠ 0) :
    ∃ c'' ∈ S.cluster E a0 c, c'' ∈ S3Geom.flaggedSet (S.resid E) ∧
      ∀ k ∈ G.comp (S3Geom.flaggedSet (S.resid E)) a0 c, a0 < G.blockDist k c'' := by
  set K0 := G.comp (S3Geom.flaggedSet (S.resid E)) a0 c
  have hbad : S.badD E c := by
    obtain ⟨v, hv, hD⟩ := hc
    exact Or.inr (Or.inl ⟨v, hv, hD⟩)
  have hpar := S.interior_parity ha0 hint
  have hsub := S.comp_flagged_subset_cluster (E := E) (a0 := a0) (c := c)
  -- some residual defect lies in the cluster outside K0
  have hex : ∃ v, G.blockOf v ∈ S.cluster E a0 c ∧ G.blockOf v ∉ K0 ∧ S.resid E v ≠ 0 := by
    by_contra hne'
    have hne : ∀ v, G.blockOf v ∈ S.cluster E a0 c → G.blockOf v ∉ K0 → S.resid E v = 0 :=
      fun v h1 h2 => by
        by_contra h3
        exact hne' ⟨v, h1, h2, h3⟩
    apply hodd
    rw [← hpar]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [S3Geom.restrictTo]
    by_cases hv0 : G.blockOf v ∈ K0
    · simp [hv0, hsub hv0]
    · by_cases hvc : G.blockOf v ∈ S.cluster E a0 c
      · simp [hv0, hvc, hne v hvc hv0]
      · simp [hv0, hvc]
  obtain ⟨v, hvc, hv0, hD⟩ := hex
  refine ⟨G.blockOf v, hvc, ⟨v, rfl, hD⟩, fun k hk => ?_⟩
  by_contra hle'
  have hle : G.blockDist k (G.blockOf v) ≤ a0 := not_lt.1 hle'
  apply hv0
  obtain ⟨hroot, hreach⟩ := hk
  have hkF : k ∈ S3Geom.flaggedSet (S.resid E) := S3Geom.comp_subset ⟨hroot, hreach⟩
  exact ⟨hroot, hreach.tail ⟨hkF, ⟨v, rfl, hD⟩, hle⟩⟩

end Stage1

end QECML
