import QEC.Count.Defs

/-!
# i.i.d. noise: monotonicity, union bound, the probability of a labelled path, the tilt; ML decoding

* `PrIID_mono`, `PrIID_exists_le`: monotonicity and the union bound.
* `PrIID_inter_eq`: for `S ⊆ γ ⊆ Eg`, `Pr(E ∩ γ = S) = p^|S| (1 - p)^|γ \ S|`.
* `tilt_unif`: `p^nE (1 - p)^nC ≤ (p X)^nE ((1 - p)/X)^nC` for `X ≥ 1`, `nC ≤ nE`.
* `PfailML_le_PfailMW`: the ML failure probability is at most that of "some minimum-weight correction fails".
-/

namespace QEC

open Finset

section IID

variable {α : Type*} [DecidableEq α]

/-- The weight of one error set is nonnegative. -/
private theorem IID_wt_nonneg (Eg E : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p ^ #E * (1 - p) ^ #(Eg \ E) :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

open scoped Classical in
/-- `PrIID` as a sum over all error sets. -/
private theorem IID_eq_ite (Eg : Finset α) (p : ℝ) (A : Finset α → Prop) :
    PrIID Eg p A = ∑ E ∈ Eg.powerset, if A E then p ^ #E * (1 - p) ^ #(Eg \ E) else 0 := by
  unfold PrIID
  rw [Finset.sum_filter]

theorem PrIID_nonneg (Eg : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α → Prop) :
    0 ≤ PrIID Eg p A := by
  unfold PrIID
  exact Finset.sum_nonneg (fun E _ => IID_wt_nonneg Eg E hp0 hp1)

theorem PrIID_mono (Eg : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset α → Prop}
    (h : ∀ E ⊆ Eg, A E → B E) : PrIID Eg p A ≤ PrIID Eg p B := by
  unfold PrIID
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    exact ⟨hE.1, h E hE.1 hE.2⟩
  · intro E _ _
    exact IID_wt_nonneg Eg E hp0 hp1

/-- The union bound. -/
theorem PrIID_exists_le (Eg : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type*} (I : Finset ι)
    (A : ι → Finset α → Prop) : PrIID Eg p (fun E => ∃ i ∈ I, A i E) ≤ ∑ i ∈ I, PrIID Eg p (A i) := by
  classical
  rw [IID_eq_ite, Finset.sum_congr rfl (fun i _ => IID_eq_ite Eg p (A i)), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  have hw := IID_wt_nonneg Eg E hp0 hp1
  have hnn : ∀ j ∈ I, 0 ≤ (if A j E then p ^ #E * (1 - p) ^ #(Eg \ E) else 0) := by
    intro j _
    split_ifs
    · exact hw
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hA⟩ := h
    calc p ^ #E * (1 - p) ^ #(Eg \ E) = (if A i E then p ^ #E * (1 - p) ^ #(Eg \ E) else 0) := by
          simp [hA]
      _ ≤ ∑ j ∈ I, (if A j E then p ^ #E * (1 - p) ^ #(Eg \ E) else 0) :=
          Finset.single_le_sum (f := fun j => if A j E then p ^ #E * (1 - p) ^ #(Eg \ E) else 0) hnn hi
  · exact Finset.sum_nonneg hnn

/-- The probability that the error meets `γ` exactly in `S`. -/
theorem PrIID_inter_eq (Eg : Finset α) (p : ℝ) {γ S : Finset α} (hγ : γ ⊆ Eg) (hS : S ⊆ γ) :
    PrIID Eg p (fun E => E ∩ γ = S) = p ^ #S * (1 - p) ^ #(γ \ S) := by
  classical
  unfold PrIID
  have hsum : ∑ T ∈ (Eg \ γ).powerset, p ^ #T * (1 - p) ^ (#(Eg \ γ) - #T) = 1 := by
    rw [Finset.sum_pow_mul_eq_add_pow]
    simp
  have hrhs : p ^ #S * (1 - p) ^ #(γ \ S) = ∑ T ∈ (Eg \ γ).powerset,
      p ^ #S * (1 - p) ^ #(γ \ S) * (p ^ #T * (1 - p) ^ (#(Eg \ γ) - #T)) := by
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [hrhs]
  apply Finset.sum_nbij' (fun E => E \ γ) (fun T => S ∪ T)
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE
    simp only [Finset.mem_powerset]
    exact Finset.sdiff_subset_sdiff hE.1 le_rfl
  · intro T hT
    simp only [Finset.mem_powerset] at hT
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset (hS.trans hγ) (hT.trans Finset.sdiff_subset), ?_⟩
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxg⟩
      · exact hx
      · exact absurd hxg (Finset.mem_sdiff.mp (hT hx)).2
    · intro hx
      exact ⟨Or.inl hx, hS hx⟩
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · rw [← hE.2] at hx
        exact (Finset.mem_inter.mp hx).1
      · exact hx
    · intro hx
      by_cases hxg : x ∈ γ
      · left
        rw [← hE.2]
        exact Finset.mem_inter.mpr ⟨hx, hxg⟩
      · right
        exact ⟨hx, hxg⟩
  · intro T hT
    simp only [Finset.mem_powerset] at hT
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxg⟩
      · exact absurd (hS hx) hxg
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hT hx)).2⟩
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE
    obtain ⟨hEg, hEγ⟩ := hE
    -- `E` is the disjoint union of `S` and `E \ γ`
    have hEdecomp : E = S ∪ (E \ γ) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hx
        by_cases hxg : x ∈ γ
        · left
          rw [← hEγ]
          exact Finset.mem_inter.mpr ⟨hx, hxg⟩
        · right
          exact ⟨hx, hxg⟩
      · rintro (hx | ⟨hx, _⟩)
        · rw [← hEγ] at hx
          exact (Finset.mem_inter.mp hx).1
        · exact hx
    have hdisj1 : Disjoint S (E \ γ) := by
      rw [Finset.disjoint_left]
      intro x hxS hxE
      exact (Finset.mem_sdiff.mp hxE).2 (hS hxS)
    have hcardE : #E = #S + #(E \ γ) := by
      conv_lhs => rw [hEdecomp]
      exact Finset.card_union_of_disjoint hdisj1
    -- `Eg \ E` is the disjoint union of `γ \ S` and `(Eg \ γ) \ (E \ γ)`
    have hcompl : Eg \ E = (γ \ S) ∪ ((Eg \ γ) \ (E \ γ)) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxg, hxE⟩
        by_cases hxγ : x ∈ γ
        · left
          refine ⟨hxγ, fun hxS => hxE ?_⟩
          rw [← hEγ] at hxS
          exact (Finset.mem_inter.mp hxS).1
        · right
          exact ⟨⟨hxg, hxγ⟩, fun h => hxE h.1⟩
      · rintro (⟨hxγ, hxS⟩ | ⟨⟨hxg, hxγ⟩, hxE⟩)
        · refine ⟨hγ hxγ, fun hxE => hxS ?_⟩
          rw [← hEγ]
          exact Finset.mem_inter.mpr ⟨hxE, hxγ⟩
        · exact ⟨hxg, fun hx => hxE ⟨hx, hxγ⟩⟩
    have hdisj2 : Disjoint (γ \ S) ((Eg \ γ) \ (E \ γ)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx2).1).2 (Finset.mem_sdiff.mp hx1).1
    have hsub : E \ γ ⊆ Eg \ γ := Finset.sdiff_subset_sdiff hEg le_rfl
    have hcardC : #(Eg \ E) = #(γ \ S) + (#(Eg \ γ) - #(E \ γ)) := by
      rw [hcompl, Finset.card_union_of_disjoint hdisj2, Finset.card_sdiff_of_subset hsub]
    rw [hcardE, hcardC, pow_add, pow_add]
    ring

end IID

/-- The tilt with uniform weights. -/
theorem tilt_unif {p X : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hX : 1 ≤ X) {nE nC : ℕ} (h : nC ≤ nE) :
    p ^ nE * (1 - p) ^ nC ≤ (p * X) ^ nE * ((1 - p) / X) ^ nC := by
  have hX0 : 0 < X := by linarith
  have hX0' : X ≠ 0 := ne_of_gt hX0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : (p * X) ^ (nC + k) * ((1 - p) / X) ^ nC = p ^ (nC + k) * (1 - p) ^ nC * X ^ k := by
    rw [mul_pow, div_pow, pow_add X]
    field_simp
  rw [e]
  have h0 : 0 ≤ p ^ (nC + k) * (1 - p) ^ nC := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  calc p ^ (nC + k) * (1 - p) ^ nC = p ^ (nC + k) * (1 - p) ^ nC * 1 := by ring
    _ ≤ p ^ (nC + k) * (1 - p) ^ nC * X ^ k := mul_le_mul_of_nonneg_left (one_le_pow₀ hX) h0

section ML

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- ML decoding is at least as good as any minimum-weight decoder: `PfailML ≤ PfailMW`. -/
theorem PfailML_le_PfailMW (Eg : Finset (Sym2 (Vx V))) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    PfailML Eg p ≤ PfailMW Eg p := by
  classical
  -- a minimum-weight decoder with a syndrome-only tie rule (a chosen minimizer)
  let dec : Finset V → Bool := fun s =>
    if h : ∃ C, IsMinCorr Eg s C then decide (Odd (vdeg (Classical.choose h) .b1)) else false
  have hle : PfailML Eg p ≤ PfailDec Eg p dec := by
    unfold PfailML
    exact ciInf_le (Set.finite_range _).bddBelow dec
  refine le_trans hle (PrIID_mono Eg hp0 hp1 ?_)
  intro E hE hne
  -- the syndrome of `E` has a minimizer: `E` is a correction, and there are finitely many
  have hex : ∃ C, IsMinCorr Eg (bd E) C := by
    have hne' : (Eg.powerset.filter (fun C => bd C = bd E)).Nonempty :=
      ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE, rfl⟩⟩
    obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image _ (fun C => #C) hne'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    exact ⟨C, hC.1, hC.2, fun C' hC' hbd =>
      hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC', hbd⟩)⟩
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  have hdec : dec (bd E) = decide (Odd (vdeg (Classical.choose hex) .b1)) := by
    simp [dec, hex]
  rw [hdec] at hne
  intro hiff
  exact hne (decide_eq_decide.mpr hiff)

end ML

end QEC
