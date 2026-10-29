import QECD1.ProbUnion3

/-!
# Restricting the bad events to the sampled rows

(H_eps) bounds the bad event only for the blocks in the sampled rows `R`, while `skel_prob_le` and
`skel_union_le_filter` ask for a bound for every block.
`rowBad R Bad b X := b ∈ R ∧ Bad b X` has the same support as `Bad b` (`rowBad_dep`) and is empty off `R`, so its
probability is at most `ε` for every block (`rowBad_le`); on `R` it is `Bad` by definition.
* `skel_prob_le_rows`: separated blocks, all in `R`, are all bad with probability at most `ε^{|B|}`;
* `skel_union_le_rows`: the union bound over lists whose blocks are separated and lie in `R`.

Both theorems take the membership of the listed blocks in `R` as a hypothesis. For the counted blocks of a skeleton
it is proved in `Cover3` (`famF_rows_bad`, `final_skeleton`): under the strip hypothesis `hnodecl` they are
undeclared, so they lie in any `R` that contains the undeclared blocks.
-/

namespace QECD1

open Classical

section Rows

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prob_congr {p : ℝ} {A B : (ι → Bool) → Prop} (h : ∀ X, A X ↔ B X) : prob p A = prob p B :=
  congrArg (prob p) (funext fun X => propext (h X))

theorem prob_false (p : ℝ) : prob p (fun _ : ι → Bool => False) = 0 := by
  unfold prob
  exact Finset.sum_eq_zero fun X _ => if_neg not_false

end Rows

/-- The bad event of block `b`, restricted to the blocks in `R`. -/
def rowBad {κ : Type} (R : Set V3) (Bad : V3 → κ → Prop) (b : V3) (X : κ) : Prop := b ∈ R ∧ Bad b X

theorem rowBad_dep {T w h : ℕ} (R : Set V3) (Bad : V3 → (PEdge3 T w h → Bool) → Prop)
    (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b)) (b : V3) : DependsOn (rowBad R Bad b) (Nbhd3 b) :=
  fun X Y hXY => and_congr Iff.rfl (hdep b X Y hXY)

theorem rowBad_le {T w h : ℕ} {p ε : ℝ} (hε0 : 0 ≤ ε) (R : Set V3) (Bad : V3 → (PEdge3 T w h → Bool) → Prop)
    (hε : ∀ b ∈ R, prob p (Bad b) ≤ ε) (b : V3) : prob p (rowBad R Bad b) ≤ ε := by
  by_cases hb : b ∈ R
  · rw [prob_congr (fun X => show rowBad R Bad b X ↔ Bad b X from and_iff_right hb)]
    exact hε b hb
  · rw [prob_congr (fun X => show rowBad R Bad b X ↔ False from iff_false_intro fun h => hb h.1), prob_false]
    exact hε0

/-- **The product bound with (H_eps) on the sampled rows only.** Pairwise `D`-separated blocks that all lie in `R`
are all bad with probability at most `ε^{|B|}`. -/
theorem skel_prob_le_rows {T w h : ℕ} {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    (R : Set V3) (hε : ∀ b ∈ R, prob p (Bad b) ≤ ε) {B : List V3}
    (hB : B.Pairwise (fun a b => Const.D ≤ dist3 a b)) (hBR : ∀ b ∈ B, b ∈ R) :
    prob p (fun X => ∀ b ∈ B, Bad b X) ≤ ε ^ B.length := by
  have h := skel_prob_le hp0 hp1 (rowBad R Bad) (rowBad_dep R Bad hdep) (rowBad_le hε0 R Bad hε) hB
  rwa [prob_congr (fun X => show (∀ b ∈ B, rowBad R Bad b X) ↔ ∀ b ∈ B, Bad b X from
    forall₂_congr fun b hb => and_iff_right (hBR b hb))] at h

/-- **The union bound with (H_eps) on the sampled rows only.** If each configuration in `A` makes all blocks of some
list `L k`, `k ∈ K`, bad, where the list is pairwise `D`-separated and lies in `R`, then `prob A` is at most the sum
of `ε^{|L k|}` over the separated `k ∈ K`. -/
theorem skel_union_le_rows {T w h : ℕ} {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    (R : Set V3) (hε : ∀ b ∈ R, prob p (Bad b) ≤ ε) {κ : Type} (K : Finset κ) (L : κ → List V3)
    {A : (PEdge3 T w h → Bool) → Prop}
    (hcov : ∀ X, A X → ∃ k ∈ K, (L k).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧ (∀ b ∈ L k, b ∈ R) ∧
      ∀ b ∈ L k, Bad b X) :
    prob p A ≤ ∑ k ∈ K.filter (fun k => (L k).Pairwise (fun a b => Const.D ≤ dist3 a b)), ε ^ (L k).length := by
  refine skel_union_le_filter hp0 hp1 (rowBad R Bad) (rowBad_dep R Bad hdep) (rowBad_le hε0 R Bad hε) K L
    fun X hX => ?_
  obtain ⟨k, hk, hsep, hR, hbad⟩ := hcov X hX
  exact ⟨k, hk, hsep, fun b hb => (⟨hR b hb, hbad b hb⟩ : b ∈ R ∧ Bad b X)⟩

end QECD1
