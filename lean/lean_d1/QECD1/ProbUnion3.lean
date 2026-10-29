import QECD1.ProbSkel3

/-!
# The union bound over skeletons

* `prob_mono`, `prob_or_le`, `prob_exists_le`: monotonicity of `prob` and the union bound over a finite index set.
* `DependsOn.mono`, `DependsOn.and`, `DependsOn.or`, `DependsOn.not`, `dependsOn_forall`, `dependsOn_exists`: an
  event built from events on known edge sets depends on their union. The locality of the decoder's bad events
  (locality) is to be assembled from these.
* `skel_union_le`: suppose every configuration in `A` makes all blocks of some list `L k` bad, for `k` in a finite set
  `K`, and each `L k` is pairwise `D`-separated. Then `prob A ≤ ∑_{k ∈ K} ε^{|L k|}`.
* `skel_union_le_filter`: the same when the separation is part of the cover, as in `gen_skel3_final`'s conclusion for
  `keyBlocks`; the sum then runs over the separated `k` only.
-/

namespace QECD1

open Classical

section Union

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prob_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : (ι → Bool) → Prop} (h : ∀ X, A X → B X) :
    prob p A ≤ prob p B := by
  unfold prob
  refine Finset.sum_le_sum fun X _ => ?_
  by_cases hA : A X
  · rw [if_pos hA, if_pos (h X hA)]
  · rw [if_neg hA]
    split_ifs
    · exact pw_nonneg hp0 hp1 X
    · exact le_rfl

theorem prob_or_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A B : (ι → Bool) → Prop) :
    prob p (fun X => A X ∨ B X) ≤ prob p A + prob p B := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun X _ => ?_
  have h0 := pw_nonneg hp0 hp1 X
  by_cases hA : A X <;> by_cases hB : B X
  · rw [if_pos (show (fun X => A X ∨ B X) X from Or.inl hA), if_pos hA, if_pos hB]
    linarith
  · rw [if_pos (show (fun X => A X ∨ B X) X from Or.inl hA), if_pos hA, if_neg hB]
    linarith
  · rw [if_pos (show (fun X => A X ∨ B X) X from Or.inr hB), if_neg hA, if_pos hB]
    linarith
  · rw [if_neg (show ¬ (fun X => A X ∨ B X) X from not_or.2 ⟨hA, hB⟩), if_neg hA, if_neg hB]
    linarith

/-- **The union bound** over a finite index set. -/
theorem prob_exists_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {κ : Type} (K : Finset κ)
    (B : κ → (ι → Bool) → Prop) :
    prob p (fun X => ∃ k ∈ K, B k X) ≤ ∑ k ∈ K, prob p (B k) := by
  induction K using Finset.induction_on with
  | empty =>
    have h : prob p (fun X : ι → Bool => ∃ k ∈ (∅ : Finset κ), B k X) = 0 := by
      unfold prob
      exact Finset.sum_eq_zero fun X _ => if_neg (by simp)
    rw [h, Finset.sum_empty]
  | @insert k K hk ih =>
    rw [Finset.sum_insert hk]
    have hins : (fun X => ∃ j ∈ insert k K, B j X) = (fun X => B k X ∨ ∃ j ∈ K, B j X) := by
      funext X
      refine propext ⟨fun ⟨j, hj, hB⟩ => ?_, fun h => ?_⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact Or.inl hB
        · exact Or.inr ⟨j, hj, hB⟩
      · rcases h with hB | ⟨j, hj, hB⟩
        · exact ⟨k, Finset.mem_insert_self k K, hB⟩
        · exact ⟨j, Finset.mem_insert_of_mem hj, hB⟩
    rw [hins]
    have hor := prob_or_le hp0 hp1 (B k) (fun X => ∃ j ∈ K, B j X)
    linarith

omit [Fintype ι] [DecidableEq ι] in
theorem DependsOn.mono {A : (ι → Bool) → Prop} {S S' : Finset ι} (h : DependsOn A S) (hS : S ⊆ S') :
    DependsOn A S' :=
  fun X Y hXY => h X Y fun e he => hXY e (hS he)

omit [Fintype ι] [DecidableEq ι] in
theorem DependsOn.and {A B : (ι → Bool) → Prop} {S : Finset ι} (hA : DependsOn A S) (hB : DependsOn B S) :
    DependsOn (fun X => A X ∧ B X) S :=
  fun X Y hXY => and_congr (hA X Y hXY) (hB X Y hXY)

omit [Fintype ι] [DecidableEq ι] in
theorem DependsOn.or {A B : (ι → Bool) → Prop} {S : Finset ι} (hA : DependsOn A S) (hB : DependsOn B S) :
    DependsOn (fun X => A X ∨ B X) S :=
  fun X Y hXY => or_congr (hA X Y hXY) (hB X Y hXY)

omit [Fintype ι] [DecidableEq ι] in
theorem DependsOn.not {A : (ι → Bool) → Prop} {S : Finset ι} (hA : DependsOn A S) :
    DependsOn (fun X => ¬ A X) S :=
  fun X Y hXY => not_congr (hA X Y hXY)

omit [Fintype ι] in
/-- All events of a finite family occur: this depends on the union of their supports. -/
theorem dependsOn_forall {β : Type} (P : β → (ι → Bool) → Prop) (sup : β → Finset ι)
    (hP : ∀ b, DependsOn (P b) (sup b)) (B : Finset β) :
    DependsOn (fun X => ∀ b ∈ B, P b X) (B.biUnion sup) :=
  fun X Y hXY => forall₂_congr fun b hb => hP b X Y fun e he => hXY e (Finset.mem_biUnion.2 ⟨b, hb, he⟩)

omit [Fintype ι] in
/-- Some event of a finite family occurs: this depends on the union of their supports. -/
theorem dependsOn_exists {β : Type} (P : β → (ι → Bool) → Prop) (sup : β → Finset ι)
    (hP : ∀ b, DependsOn (P b) (sup b)) (B : Finset β) :
    DependsOn (fun X => ∃ b ∈ B, P b X) (B.biUnion sup) :=
  fun X Y hXY => exists_congr fun b => and_congr_right fun hb =>
    hP b X Y fun e he => hXY e (Finset.mem_biUnion.2 ⟨b, hb, he⟩)

end Union

/-- **The union bound over skeletons.** Suppose each configuration in `A` makes all blocks of some list `L k` bad,
`k ∈ K`, with each `L k` pairwise `D`-separated, and each block's bad event depends only on `Nbhd3` and has
probability at most `ε` (H_eps). Then `prob A ≤ ∑_{k ∈ K} ε^{|L k|}`. -/
theorem skel_union_le {T w h : ℕ} {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    (hε : ∀ b, prob p (Bad b) ≤ ε) {κ : Type} (K : Finset κ) (L : κ → List V3)
    (hL : ∀ k ∈ K, (L k).Pairwise (fun a b => Const.D ≤ dist3 a b))
    {A : (PEdge3 T w h → Bool) → Prop} (hcov : ∀ X, A X → ∃ k ∈ K, ∀ b ∈ L k, Bad b X) :
    prob p A ≤ ∑ k ∈ K, ε ^ (L k).length :=
  calc prob p A ≤ prob p (fun X => ∃ k ∈ K, ∀ b ∈ L k, Bad b X) := prob_mono hp0 hp1 hcov
    _ ≤ ∑ k ∈ K, prob p (fun X => ∀ b ∈ L k, Bad b X) := prob_exists_le hp0 hp1 K _
    _ ≤ ∑ k ∈ K, ε ^ (L k).length :=
      Finset.sum_le_sum fun k hk => skel_prob_le hp0 hp1 Bad hdep hε (hL k hk)

/-- The union bound when the separation is part of the cover, as in `gen_skel3_final`'s conclusion
`(keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b)`: the sum runs over the separated `k ∈ K`. -/
theorem skel_union_le_filter {T w h : ℕ} {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    (hε : ∀ b, prob p (Bad b) ≤ ε) {κ : Type} (K : Finset κ) (L : κ → List V3)
    {A : (PEdge3 T w h → Bool) → Prop}
    (hcov : ∀ X, A X → ∃ k ∈ K, (L k).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧ ∀ b ∈ L k, Bad b X) :
    prob p A ≤ ∑ k ∈ K.filter (fun k => (L k).Pairwise (fun a b => Const.D ≤ dist3 a b)), ε ^ (L k).length := by
  refine skel_union_le hp0 hp1 Bad hdep hε _ L (fun k hk => (Finset.mem_filter.1 hk).2) fun X hX => ?_
  obtain ⟨k, hk, hsep, hbad⟩ := hcov X hX
  exact ⟨k, Finset.mem_filter.2 ⟨hk, hsep⟩, hbad⟩

end QECD1
