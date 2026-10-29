import QECD1.Nbhd3

/-!
# The probability side for skeletons: independence under product noise

Edges carry i.i.d. noise of rate `p`. A configuration `X : ι → Bool` has weight `pw p X = ∏ e, (p or 1 - p)`, and an
event `A` has probability `prob p A = ∑_X [A X] pw p X`.

* `indep_disjoint`: events that depend on disjoint sets of edges are independent,
  `prob (A ∧ A') = prob A * prob A'`. A configuration splits into its part on `S` and its part off `S`
  (`splitE`, `sum_split`), and the weight factorizes (`pw_split`).
* `prob_all_le`: suppose events `Bad b` (`b` in a list `B`) depend on pairwise disjoint edge sets and each has
  probability at most `ε` (H_eps). Then the probability that all occur is at most `ε^{|B|}`.
* `skel_prob_le`: on the 3D code, take `Nbhd3` as the supports and the counted blocks of a good skeleton as `B`; they
  are pairwise `D`-separated (`skel_nbhd_disjoint`). The probability that all counted blocks are bad is at most
  `ε^{|keyBlocks|}`.
-/

namespace QECD1

open Classical

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The weight of a configuration under i.i.d. noise of rate `p`. -/
noncomputable def pw (p : ℝ) (X : ι → Bool) : ℝ := ∏ e, if X e then p else 1 - p

/-- The probability of an event under i.i.d. noise of rate `p`. -/
noncomputable def prob (p : ℝ) (A : (ι → Bool) → Prop) : ℝ := ∑ X, if A X then pw p X else 0

/-- The event `A` depends only on the edges in `S`. -/
def DependsOn (A : (ι → Bool) → Prop) (S : Finset ι) : Prop :=
  ∀ X Y : ι → Bool, (∀ e ∈ S, X e = Y e) → (A X ↔ A Y)

theorem pw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : ι → Bool) : 0 ≤ pw p X := by
  unfold pw
  refine Finset.prod_nonneg fun e _ => ?_
  split_ifs <;> linarith

theorem prob_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : (ι → Bool) → Prop) : 0 ≤ prob p A := by
  unfold prob
  refine Finset.sum_nonneg fun X _ => ?_
  split_ifs
  · exact pw_nonneg hp0 hp1 X
  · exact le_rfl

/-- The weights of all configurations of a finite set of edges sum to 1. -/
theorem sum_prod_bool (p : ℝ) (κ : Type) [Fintype κ] [DecidableEq κ] :
    ∑ v : κ → Bool, ∏ e, (if v e then p else 1 - p) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : κ) (b : Bool) => if b then p else 1 - p)]
  simp

/-- Splitting a configuration into its part on `S` and its part off `S`. -/
noncomputable def splitE (S : Finset ι) : (ι → Bool) ≃ (({e // e ∈ S} → Bool) × ({e // e ∉ S} → Bool)) :=
  Equiv.piEquivPiSubtypeProd (fun e => e ∈ S) (fun _ => Bool)

theorem sum_split (S : Finset ι) (F : (ι → Bool) → ℝ) :
    ∑ X, F X = ∑ u : {e // e ∈ S} → Bool, ∑ v : {e // e ∉ S} → Bool, F ((splitE S).symm (u, v)) := by
  rw [Fintype.sum_equiv (splitE S) F (fun uv => F ((splitE S).symm uv)) (fun X => by simp)]
  exact Fintype.sum_prod_type' (fun u v => F ((splitE S).symm (u, v)))

theorem splitE_symm_in (S : Finset ι) (u : {e // e ∈ S} → Bool) (v : {e // e ∉ S} → Bool) {e : ι} (he : e ∈ S) :
    (splitE S).symm (u, v) e = u ⟨e, he⟩ := by
  simp [splitE, he]

theorem splitE_symm_out (S : Finset ι) (u : {e // e ∈ S} → Bool) (v : {e // e ∉ S} → Bool) {e : ι} (he : e ∉ S) :
    (splitE S).symm (u, v) e = v ⟨e, he⟩ := by
  simp [splitE, he]

/-- The weight of a partial configuration. -/
noncomputable def pwS (p : ℝ) {κ : Type} [Fintype κ] (u : κ → Bool) : ℝ := ∏ e, if u e then p else 1 - p

theorem sum_pwS (p : ℝ) (κ : Type) [Fintype κ] [DecidableEq κ] : ∑ v : κ → Bool, pwS p v = 1 :=
  sum_prod_bool p κ

/-- The weight factorizes over the two parts. -/
theorem pw_split (p : ℝ) (S : Finset ι) (u : {e // e ∈ S} → Bool) (v : {e // e ∉ S} → Bool) :
    pw p ((splitE S).symm (u, v)) = pwS p u * pwS p v := by
  unfold pw pwS
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun e => e ∈ S)]
  congr 1
  · exact Finset.prod_congr (Finset.eq_univ_iff_forall.2 fun x => by simp)
      fun e _ => by rw [splitE_symm_in S u v e.2]
  · exact Finset.prod_congr (Finset.eq_univ_iff_forall.2 fun x => by simp)
      fun e _ => by rw [splitE_symm_out S u v e.2]

/-- **Events on disjoint sets of edges are independent.** -/
theorem indep_disjoint (p : ℝ) {A A' : (ι → Bool) → Prop} {S S' : Finset ι} (hA : DependsOn A S)
    (hA' : DependsOn A' S') (hd : Disjoint S S') :
    prob p (fun X => A X ∧ A' X) = prob p A * prob p A' := by
  let v0 : {e // e ∉ S} → Bool := fun _ => false
  let u0 : {e // e ∈ S} → Bool := fun _ => false
  have hAu : ∀ u v, A ((splitE S).symm (u, v)) ↔ A ((splitE S).symm (u, v0)) := by
    intro u v
    refine hA _ _ fun e he => ?_
    rw [splitE_symm_in S u v he, splitE_symm_in S u v0 he]
  have hA'v : ∀ u v, A' ((splitE S).symm (u, v)) ↔ A' ((splitE S).symm (u0, v)) := by
    intro u v
    refine hA' _ _ fun e he => ?_
    have heS : e ∉ S := Finset.disjoint_right.1 hd he
    rw [splitE_symm_out S u v heS, splitE_symm_out S u0 v heS]
  have h1 : prob p (fun X => A X ∧ A' X) = ∑ u, ∑ v,
      (if A ((splitE S).symm (u, v0)) then pwS p u else 0) *
        (if A' ((splitE S).symm (u0, v)) then pwS p v else 0) := by
    unfold prob
    rw [sum_split S]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hAuv := hAu u v
    have hA'uv := hA'v u v
    by_cases h1 : A ((splitE S).symm (u, v0)) <;> by_cases h2 : A' ((splitE S).symm (u0, v))
    · rw [if_pos (show (fun X => A X ∧ A' X) ((splitE S).symm (u, v)) from ⟨hAuv.2 h1, hA'uv.2 h2⟩),
        if_pos h1, if_pos h2, pw_split]
    · rw [if_neg (show ¬ (fun X => A X ∧ A' X) ((splitE S).symm (u, v)) from
        fun h => h2 (hA'uv.1 h.2)), if_neg h2, mul_zero]
    · rw [if_neg (show ¬ (fun X => A X ∧ A' X) ((splitE S).symm (u, v)) from
        fun h => h1 (hAuv.1 h.1)), if_neg h1, zero_mul]
    · rw [if_neg (show ¬ (fun X => A X ∧ A' X) ((splitE S).symm (u, v)) from
        fun h => h1 (hAuv.1 h.1)), if_neg h1, zero_mul]
  have h2 : prob p A = ∑ u, (if A ((splitE S).symm (u, v0)) then pwS p u else 0) := by
    unfold prob
    rw [sum_split S]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : A ((splitE S).symm (u, v0))
    · rw [if_pos h]
      calc ∑ v, (if A ((splitE S).symm (u, v)) then pw p ((splitE S).symm (u, v)) else 0)
          = ∑ v, pwS p u * pwS p v :=
            Finset.sum_congr rfl fun v _ => by rw [if_pos ((hAu u v).2 h), pw_split]
        _ = pwS p u := by rw [← Finset.mul_sum, sum_pwS, mul_one]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun v _ => if_neg fun h' => h ((hAu u v).1 h')
  have h3 : prob p A' = ∑ v, (if A' ((splitE S).symm (u0, v)) then pwS p v else 0) := by
    unfold prob
    rw [sum_split S, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : A' ((splitE S).symm (u0, v))
    · rw [if_pos h]
      calc ∑ u, (if A' ((splitE S).symm (u, v)) then pw p ((splitE S).symm (u, v)) else 0)
          = ∑ u, pwS p u * pwS p v :=
            Finset.sum_congr rfl fun u _ => by rw [if_pos ((hA'v u v).2 h), pw_split]
        _ = pwS p v := by rw [← Finset.sum_mul, sum_pwS, one_mul]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun u _ => if_neg fun h' => h ((hA'v u v).1 h')
  rw [h1, h2, h3, Finset.sum_mul_sum]

/-- **The product bound**: events on pairwise disjoint supports, each of probability at most `ε`, all occur with
probability at most `ε^{|B|}`. -/
theorem prob_all_le {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {β : Type} (Bad : β → (ι → Bool) → Prop)
    (sup : β → Finset ι) (hdep : ∀ b, DependsOn (Bad b) (sup b)) (hε : ∀ b, prob p (Bad b) ≤ ε) :
    ∀ B : List β, B.Pairwise (fun a b => Disjoint (sup a) (sup b)) →
      prob p (fun X => ∀ b ∈ B, Bad b X) ≤ ε ^ B.length
  | [], _ => by
    have h : prob p (fun X : ι → Bool => ∀ b ∈ ([] : List β), Bad b X) = 1 := by
      unfold prob
      simp only [List.not_mem_nil, false_imp_iff, imp_true_iff, if_true]
      exact sum_prod_bool p ι
    rw [h, List.length_nil, pow_zero]
  | b :: B, hB => by
    rw [List.pairwise_cons] at hB
    obtain ⟨hbB, hB'⟩ := hB
    have ih := prob_all_le hp0 hp1 Bad sup hdep hε B hB'
    -- the tail event depends on the union of the tail's supports
    have hdepT : DependsOn (fun X => ∀ c ∈ B, Bad c X) (B.toFinset.biUnion sup) := by
      intro X Y hXY
      refine forall₂_congr fun c hc => hdep c X Y fun e he => hXY e ?_
      exact Finset.mem_biUnion.2 ⟨c, List.mem_toFinset.2 hc, he⟩
    have hdisj : Disjoint (sup b) (B.toFinset.biUnion sup) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun c hc => hbB c (List.mem_toFinset.1 hc)
    have hsplit : prob p (fun X => ∀ c ∈ b :: B, Bad c X) = prob p (fun X => Bad b X ∧ ∀ c ∈ B, Bad c X) :=
      congrArg (prob p) (funext fun X => propext List.forall_mem_cons)
    rw [hsplit, indep_disjoint p (hdep b) hdepT hdisj, List.length_cons, pow_succ']
    have hεn : 0 ≤ ε := le_trans (prob_nonneg hp0 hp1 _) (hε b)
    exact mul_le_mul (hε b) ih (prob_nonneg hp0 hp1 _) hεn

end Product

/-- **The counted blocks of a good skeleton are all bad with probability at most `ε^{|keyBlocks|}`** under i.i.d.
noise, if each block's bad event depends only on its neighbourhood (`Nbhd3`) and has probability at most `ε`
(H_eps). The blocks are pairwise `D`-separated, as `gen_skel3_final` gives. -/
theorem skel_prob_le {T w h : ℕ} {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    (hε : ∀ b, prob p (Bad b) ≤ ε) {B : List V3} (hB : B.Pairwise (fun a b => Const.D ≤ dist3 a b)) :
    prob p (fun X => ∀ b ∈ B, Bad b X) ≤ ε ^ B.length :=
  prob_all_le hp0 hp1 Bad Nbhd3 hdep hε B (skel_nbhd_disjoint hB)

end QECD1
