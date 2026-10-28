import QECML.S3.Decoder

/-!
# The 2D lemma, deterministic part: Lemma A

Lemma A of the proof of the 2D lemma (step (A) of the paper's outline; convention (i), analysis clusters), for any
admissible stage-1
rule. Components of `F = E + C_0` are taken on the checks through bulk edges (a half-edge belongs to the component
of its check; `b₁`, `b₂` join nothing).

* `confine` (Lemma A, first part): if block `c` is not bad, every check reachable through `F` from a check of `c`
  lies within `ℓ∞` distance `L - 1` of `c` (the first exit to distance `L` would make `c` long). Only unit steps
  are used.
* `psyn_Fcfg`, `flagged_of_odd` (Lemma A, second part): the odd checks of `F` are the residual defects, so they lie in
  flagged (hence bad) blocks.
* `cluster_eq_of_reach` (Lemma A, third part): for `a0 ≥ 2`, the checks of one component of `F` that lie in bad
  blocks (convention (i) included) all belong to the same analysis cluster.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable (G : S3Geom)

/-- Rows `0, 1, n_y - 2, n_y - 1` of blocks, declared bad by convention (i). -/
def declared (c : G.Block) : Prop := c.2.val < 2 ∨ G.ny ≤ c.2.val + 2

variable {G}

/-- One coordinate: within distance `L` of a block's interval means within one block. -/
theorem ndist_div_le_one {L x a : ℕ} (hL : 1 ≤ L) (h : dist1 x (a * L) (a * L + L - 1) ≤ L) :
    ndist (x / L) a ≤ 1 := by
  simp only [dist1] at h
  have h1 : x < a * L + 2 * L := by
    generalize a * L = A at h ⊢
    omega
  have h2 : x / L < a + 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [add_mul]; exact h1)
  have h3 : a - 1 ≤ x / L := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha]
      exact Nat.zero_le _
    · rw [Nat.le_div_iff_mul_le (by omega), Nat.sub_mul, one_mul]
      generalize a * L = A at h ⊢
      omega
  simp only [ndist]
  generalize x / L = t at h2 h3 ⊢
  omega

/-- A check within distance `L` of block `c` lies in a block of `N_1(c)`. -/
theorem blockDist_le_one_of_distVB {v : G.V} {c : G.Block} (h : G.distVB v c ≤ G.L) :
    G.blockDist (G.blockOf v) c ≤ 1 := by
  simp only [distVB, max_le_iff] at h
  simp only [blockDist, blockOf, bcol, brow, max_le_iff]
  exact ⟨ndist_div_le_one G.hL h.1, ndist_div_le_one G.hL h.2⟩

theorem dist1_lip {x x' a b : ℕ} (hxx : ndist x x' ≤ 1) : dist1 x' a b ≤ dist1 x a b + 1 := by
  simp only [dist1, ndist] at *
  omega

/-- Along an edge, the distance to a block changes by at most one. -/
theorem distVB_ends {e : G.Ed} {u u' : G.V} (hu : u ∈ e.ends) (hu' : u' ∈ e.ends) (c : G.Block) :
    G.distVB u' c ≤ G.distVB u c + 1 := by
  have hadj := G.ends_adjacent e hu hu'
  simp only [distVB]
  have h1 := dist1_lip (a := c.1.val * G.L) (b := c.1.val * G.L + G.L - 1) hadj.1
  have h2 := dist1_lip (a := c.2.val * G.L) (b := c.2.val * G.L + G.L - 1) hadj.2
  omega

/-- The blocks of the two ends of an edge are at block distance at most one. -/
theorem blockDist_ends {e : G.Ed} {u u' : G.V} (hu : u ∈ e.ends) (hu' : u' ∈ e.ends) :
    G.blockDist (G.blockOf u) (G.blockOf u') ≤ 1 := by
  have hadj := G.ends_adjacent e hu hu'
  have hL := G.hL
  simp only [ndist] at hadj
  simp only [blockDist, blockOf, bcol, brow, ndist, max_le_iff]
  constructor
  · rcases Nat.le_total u.1.val u'.1.val with h | h
    · have h1 := Nat.div_le_div_right (c := G.L) h
      have h2 : u'.1.val / G.L ≤ u.1.val / G.L + 1 :=
        (Nat.div_le_div_right (c := G.L) (show u'.1.val ≤ u.1.val + 1 by omega)).trans (div_succ_le hL _)
      omega
    · have h1 := Nat.div_le_div_right (c := G.L) h
      have h2 : u.1.val / G.L ≤ u'.1.val / G.L + 1 :=
        (Nat.div_le_div_right (c := G.L) (show u.1.val ≤ u'.1.val + 1 by omega)).trans (div_succ_le hL _)
      omega
  · rcases Nat.le_total u.2.val u'.2.val with h | h
    · have h1 := Nat.div_le_div_right (c := G.L) h
      have h2 : u'.2.val / G.L ≤ u.2.val / G.L + 1 :=
        (Nat.div_le_div_right (c := G.L) (show u'.2.val ≤ u.2.val + 1 by omega)).trans (div_succ_le hL _)
      omega
    · have h1 := Nat.div_le_div_right (c := G.L) h
      have h2 : u.2.val / G.L ≤ u'.2.val / G.L + 1 :=
        (Nat.div_le_div_right (c := G.L) (show u.2.val ≤ u'.2.val + 1 by omega)).trans (div_succ_le hL _)
      omega

theorem ndist_triangle (a b c : ℕ) : ndist a c ≤ ndist a b + ndist b c := by
  simp only [ndist]
  omega

theorem blockDist_triangle (c1 c2 c3 : G.Block) :
    G.blockDist c1 c3 ≤ G.blockDist c1 c2 + G.blockDist c2 c3 := by
  simp only [blockDist]
  have h1 := ndist_triangle c1.1.val c2.1.val c3.1.val
  have h2 := ndist_triangle c1.2.val c2.2.val c3.2.val
  exact max_le (h1.trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (h2.trans (add_le_add (le_max_right _ _) (le_max_right _ _)))

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- Adjacency through a bulk edge of `F`. -/
def Fadj (E : G.Ed → ZMod 2) (u v : G.V) : Prop :=
  ∃ e : G.Ed, e.ends = {u, v} ∧ u ≠ v ∧ S.Fcfg E e ≠ 0

theorem Fadj_symm {E : G.Ed → ZMod 2} {u v : G.V} (h : S.Fadj E u v) : S.Fadj E v u := by
  obtain ⟨e, he, hne, hF⟩ := h
  exact ⟨e, by rw [he, Finset.pair_comm], hne.symm, hF⟩

theorem Freach_symm {E : G.Ed → ZMod 2} {u v : G.V} (h : Relation.ReflTransGen (S.Fadj E) u v) :
    Relation.ReflTransGen (S.Fadj E) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (S.Fadj_symm hbc) ih

/-- **Lemma A, first part.** If `c` is not bad, every check reachable through `F` from a check of `c` lies within
distance `L - 1` of `c` (and is reached by a path inside `N_1(c)`). -/
theorem confine {E : G.Ed → ZMod 2} {c : G.Block} (hc : ¬ S.bad E c) {a : G.V} (ha : G.blockOf a = c)
    {u : G.V} (hu : Relation.ReflTransGen (S.Fadj E) a u) :
    G.distVB u c ≤ G.L - 1 ∧ Relation.ReflTransGen (S.stepIn E c) a u := by
  have hL := G.hL
  induction hu with
  | refl => exact ⟨by rw [← ha, G.distVB_blockOf]; exact Nat.zero_le _, .refl⟩
  | @tail b u' _ hstep ih =>
    obtain ⟨hd, hr⟩ := ih
    obtain ⟨e, he, hne, hF⟩ := hstep
    have hbm : b ∈ e.ends := by rw [he]; simp
    have hum : u' ∈ e.ends := by rw [he]; simp
    have hd' := G.distVB_ends hbm hum c
    have hb1 : G.blockDist (G.blockOf b) c ≤ 1 := G.blockDist_le_one_of_distVB (by omega)
    have hu1 : G.blockDist (G.blockOf u') c ≤ 1 := G.blockDist_le_one_of_distVB (by omega)
    have hst : S.stepIn E c b u' := ⟨hb1, hu1, e, he, hne, hF⟩
    refine ⟨?_, hr.tail hst⟩
    by_contra hcon
    exact hc (Or.inr ⟨a, u', ha, by omega, hr.tail hst⟩)

/-- **Lemma A, second part.** The odd checks of `F` are the residual defects. -/
theorem psyn_Fcfg (E : G.Ed → ZMod 2) : psyn G.w G.h (S.Fcfg E) = S.resid E := by
  simp only [Fcfg, resid, map_add]

theorem flagged_of_odd {E : G.Ed → ZMod 2} {v : G.V} (hv : psyn G.w G.h (S.Fcfg E) v ≠ 0) :
    S.flagged E (G.blockOf v) :=
  ⟨v, rfl, by rw [← S.psyn_Fcfg]; exact hv⟩

/-- Bad blocks with convention (i): declared rows or bad. -/
def badD (E : G.Ed → ZMod 2) (c : G.Block) : Prop := G.declared c ∨ S.bad E c

/-- The analysis cluster of `c`: its `a0`-component among the bad blocks (convention (i) included). -/
def cluster (E : G.Ed → ZMod 2) (a0 : ℕ) (c : G.Block) : Set G.Block := G.comp {c | S.badD E c} a0 c

/-- **Lemma A, third part.** For `a0 ≥ 2`, the checks of one component of `F` that lie in bad blocks all belong to
one analysis cluster. -/
theorem cluster_eq_of_reach {E : G.Ed → ZMod 2} {a0 : ℕ} (ha0 : 2 ≤ a0) {v1 v2 : G.V}
    (h12 : Relation.ReflTransGen (S.Fadj E) v1 v2) (h1 : S.badD E (G.blockOf v1))
    (h2 : S.badD E (G.blockOf v2)) : S.cluster E a0 (G.blockOf v2) = S.cluster E a0 (G.blockOf v1) := by
  set K1 := S.cluster E a0 (G.blockOf v1)
  have claim : ∀ u, Relation.ReflTransGen (S.Fadj E) v1 u → G.blockOf u ∈ K1 ∨
      ∃ c', ¬ S.badD E c' ∧ (∃ k ∈ K1, G.blockDist k c' ≤ 1) ∧
        ∃ a, G.blockOf a = c' ∧ Relation.ReflTransGen (S.Fadj E) a u := by
    intro u hu
    induction hu with
    | refl => exact Or.inl (S3Geom.mem_comp_self h1)
    | @tail b u' _ hstep ih =>
      have ⟨e, he, _, _⟩ := hstep
      have hbm : b ∈ e.ends := by rw [he]; simp
      have hum : u' ∈ e.ends := by rw [he]; simp
      have hbu := G.blockDist_ends hbm hum
      rcases ih with hK | ⟨c', hc', hk, a, ha, har⟩
      · by_cases hbad : S.badD E (G.blockOf u')
        · left
          have hb : G.blockOf b ∈ {c | S.badD E c} := S3Geom.comp_subset hK
          obtain ⟨hroot, hreach⟩ := hK
          exact ⟨hroot, hreach.tail ⟨hb, hbad, by omega⟩⟩
        · exact Or.inr ⟨G.blockOf u', hbad, ⟨G.blockOf b, hK, hbu⟩, u', rfl, .refl⟩
      · exact Or.inr ⟨c', hc', hk, a, ha, har.tail hstep⟩
  rcases claim v2 h12 with hK | ⟨c', hc', ⟨k, hk, hkc⟩, a, ha, har⟩
  · exact S3Geom.comp_eq_of_mem hK
  · have hgood : ¬ S.bad E c' := fun h => hc' (Or.inr h)
    have hconf := (S.confine hgood ha har).1
    have hv2 : G.blockDist (G.blockOf v2) c' ≤ 1 := G.blockDist_le_one_of_distVB (by omega)
    have hdist : G.blockDist k (G.blockOf v2) ≤ a0 := by
      have := G.blockDist_triangle k c' (G.blockOf v2)
      rw [G.blockDist_comm c' (G.blockOf v2)] at this
      omega
    obtain ⟨hroot, hreach⟩ := hk
    have hkb : k ∈ {c | S.badD E c} := S3Geom.comp_subset ⟨hroot, hreach⟩
    exact S3Geom.comp_eq_of_mem ⟨hroot, hreach.tail ⟨hkb, h2, hdist⟩⟩

end Stage1

end QECML
