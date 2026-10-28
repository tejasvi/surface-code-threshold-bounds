import QECML.Defs

/-!
# Optimality of maximum-likelihood decoding

For any weight `P` (not even assumed nonnegative, except for correction decoders), the ML decoder minimises the
failure probability among deterministic decoders, decoders with a finite random seed, randomized decoders
(stochastic kernels) and decoders that output a correction. All ML decoders have the same failure probability.
-/

open Finset

namespace QECML

section ML

variable {Ω S C : Type*} [Fintype Ω] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
variable (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C)

/-- Regrouping a sum over configurations by syndrome and class. -/
theorem sum_mul_eq_sum_joint (f : S → C → ℝ) :
    ∑ ω, f (syn ω) (cls ω) * P ω = ∑ s, ∑ c, f s c * joint P syn cls s c := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ω => (syn ω, cls ω)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
  rw [joint, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun ω hω => ?_
  · ext ω
    simp [Prod.ext_iff]
  · have h' : syn ω = s ∧ cls ω = c := by simpa [Prod.ext_iff] using hω
    rw [h'.1, h'.2]

/-- The weight decoded correctly by `dec` is `∑ s, joint s (dec s)`. -/
theorem sum_success_eq (dec : S → C) :
    (∑ ω, if dec (syn ω) = cls ω then P ω else 0) = ∑ s, joint P syn cls s (dec s) := by
  have h := sum_mul_eq_sum_joint P syn cls (fun s c => if dec s = c then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Finset.sum_ite_eq]

theorem pFail_eq (dec : S → C) :
    pFail P syn cls dec = ∑ ω, P ω - ∑ s, joint P syn cls s (dec s) := by
  rw [← sum_success_eq, pFail, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

theorem pFailR_eq (D : RDecoder S C) :
    pFailR P syn cls D = ∑ ω, P ω - ∑ s, ∑ c, D.δ s c * joint P syn cls s c := by
  rw [← sum_mul_eq_sum_joint, pFailR, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

variable [Nonempty C]

omit [Fintype S] in
theorem mlDec_isML : IsML P syn cls (mlDec P syn cls) := fun s c =>
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (joint P syn cls s)
    Finset.univ_nonempty)).2 c (Finset.mem_univ c)

/-- Every ML decoder has the failure probability `pML`. -/
theorem pFail_eq_pML {dec : S → C} (h : IsML P syn cls dec) : pFail P syn cls dec = pML P syn cls := by
  rw [pML, pFail_eq, pFail_eq]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  exact le_antisymm (mlDec_isML P syn cls s (dec s)) (h s (mlDec P syn cls s))

/-- ML optimality among deterministic decoders. -/
theorem pML_le_pFail (dec : S → C) : pML P syn cls ≤ pFail P syn cls dec := by
  rw [pML, pFail_eq, pFail_eq]
  gcongr with s
  exact mlDec_isML P syn cls s (dec s)

/-- ML optimality among randomized decoders (stochastic kernels). -/
theorem pML_le_pFailR (D : RDecoder S C) : pML P syn cls ≤ pFailR P syn cls D := by
  rw [pML, pFail_eq, pFailR_eq]
  gcongr with s
  calc ∑ c, D.δ s c * joint P syn cls s c
      ≤ ∑ c, D.δ s c * joint P syn cls s (mlDec P syn cls s) := by
        gcongr with c
        · exact D.nonneg s c
        · exact mlDec_isML P syn cls s c
    _ = joint P syn cls s (mlDec P syn cls s) := by rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- ML optimality among decoders with a finite random seed `r ∼ ρ`. -/
theorem pML_le_pFailSeed {R : Type*} [Fintype R] (ρ : R → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hρ1 : ∑ r, ρ r = 1)
    (dec : R → S → C) : pML P syn cls ≤ pFailSeed P syn cls ρ dec := by
  have h : pFailSeed P syn cls ρ dec = ∑ r, ρ r * pFail P syn cls (dec r) := by
    rw [pFailSeed, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pFail, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [h]
  calc pML P syn cls = ∑ r, ρ r * pML P syn cls := by rw [← Finset.sum_mul, hρ1, one_mul]
    _ ≤ ∑ r, ρ r * pFail P syn cls (dec r) := by
        gcongr with r
        · exact hρ r
        · exact pML_le_pFail P syn cls (dec r)

/-- ML optimality among decoders that output a correction (for an additive class map and `P ≥ 0`). -/
theorem pML_le_pFailCorr [AddCommGroup Ω] [AddCommGroup C] (cls : Ω →+ C) (hP : ∀ ω, 0 ≤ P ω)
    (corr : S → Ω) : pML P syn cls ≤ pFailCorr P syn cls corr := by
  refine (pML_le_pFail P syn cls (fun s => -cls (corr s))).trans ?_
  rw [pFail, pFailCorr]
  gcongr with ω
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact hP ω
  · exfalso
    apply h1
    have h3 := h2.2
    rw [map_add] at h3
    exact neg_eq_of_add_eq_zero_left h3
  · exact le_rfl

end ML

end QECML
