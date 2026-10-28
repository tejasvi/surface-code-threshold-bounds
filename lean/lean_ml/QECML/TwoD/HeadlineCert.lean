import QECML.TwoD.HeadlineMain
import QECML.CPConfidence

/-!
# Theorem B tied to the certificate's confidence statement

`Hstat` says that the five reference blocks have true bad probability at most `5e-4` at `q = 0.100`. The certificate
(design A: `n = 1.2e5` samples per type, accept iff every type has at most `18` bad blocks) is modelled by the binomial
law of its counts with the true rates (`hlaw`). Then (`theoremB_certified`): either the bound of Theorem B holds, or the
certificate accepts with probability at most `1e-9`. With two registered certificates (a first and a second
experiment, each with a registered stage-1 program and its own `L`), the probability that some certificate accepts
while Theorem B fails for its program is at most `2e-9` (`theoremB_certified_familywise`).
-/

open Finset Classical

namespace QECML

/-- The conclusion of Theorem B (a1 = 12, Lean constants) for a block side `L`. -/
def TheoremBConcl (L : ℕ) : Prop :=
  ∀ (q : ℝ), q ≤ 0.100 → ∀ (W H : ℕ), 1 ≤ W → 32 * L ≤ H →
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf L W : ℝ) * Real.exp (-0.2155 * ((nyOf L H : ℝ) - 31)) +
        2e4 * (nxOf L W : ℝ) * Real.exp (-0.02 * ((nyOf L H : ℝ) - 31))

/-- The true bad probability of the reference block of type `t` at `q = 0.100`. -/
noncomputable def refRate (sp : S3Prog) (hV6 : sp.V6) (t : Fin 5) : ℝ :=
  prob (bernProd 0.100) (fun E => (sp.toFam hV6).refStage1.bad E ((sp.toFam hV6).refBlock t))

theorem refRate_le_one (sp : S3Prog) (hV6 : sp.V6) (t : Fin 5) : refRate sp hV6 t ≤ 1 := by
  unfold refRate prob
  calc (∑ E, if (sp.toFam hV6).refStage1.bad E ((sp.toFam hV6).refBlock t) then bernProd 0.100 E else 0)
      ≤ ∑ E, bernProd 0.100 E := Finset.sum_le_sum fun E _ => by
        split_ifs
        · exact le_rfl
        · exact bernProd_nonneg (by norm_num) (by norm_num) E
    _ = 1 := sum_bernProd _

/-- Without `Hstat`, some reference rate exceeds `5e-4`. -/
theorem exists_rate_gt (sp : S3Prog) (hV6 : sp.V6) (h : ¬ (sp.toFam hV6).Hstat 0.100 5e-4) :
    ∃ t, 5e-4 < refRate sp hV6 t := by
  unfold S3Fam.Hstat at h
  push Not at h
  exact h

/-- **Theorem B, certified.** Under the binomial model of the certificate's counts (design A) with the true reference
rates: either the bound of Theorem B holds, or the certificate accepts with probability at most `1e-9`. -/
theorem theoremB_certified (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : Fin 5 → Ω → ℕ)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp hV6 t ^ j * (1 - refRate sp hV6 t) ^ (120000 - j)) :
    TheoremBConcl sp.L ∨ (∑ ω, if (∀ t, K t ω ≤ 18) then P ω else 0) ≤ 1e-9 := by
  by_cases hstat : (sp.toFam hV6).Hstat 0.100 5e-4
  · exact Or.inl fun q hq W H hW hH => theoremB_a12_main sp hV6 hR hL2 hcov hstat hq hW hH
  · refine Or.inr ?_
    obtain ⟨t0, ht0⟩ := exists_rate_gt sp hV6 hstat
    have h := cert_confidence_A (T := Fin 5) (by simp) P hP K (refRate sp hV6) (refRate_le_one sp hV6) hlaw
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ω _ => ?_)) h
    by_cases hacc : ∀ t, K t ω ≤ 18
    · rw [ite_eq_left hacc, ite_eq_left ⟨hacc, t0, ht0⟩]
    · rw [ite_eq_right hacc, ite_eq_right fun h' => hacc h'.1]

/-- **Two certificates, family-wise.** For two registered stage-1 programs (e.g. a first experiment and a second
one at another `L`) and a joint model of both certificates' counts (binomial with the true reference rates of each
program), the probability that some certificate accepts while Theorem B fails for its program is at most `2e-9`. -/
theorem theoremB_certified_familywise (sp1 sp2 : S3Prog) (h1V6 : sp1.V6) (h2V6 : sp2.V6)
    (h1R : sp1.R = sp1.L - 1) (h2R : sp2.R = sp2.L - 1) (h1L : 2 ≤ sp1.L) (h2L : 2 ≤ sp2.L)
    (h1cov : (sp1.toFam h1V6).Hcov) (h2cov : (sp2.toFam h2V6).Hcov)
    {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K1 K2 : Fin 5 → Ω → ℕ)
    (h1law : ∀ t j, (∑ ω, if K1 t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp1 h1V6 t ^ j * (1 - refRate sp1 h1V6 t) ^ (120000 - j))
    (h2law : ∀ t j, (∑ ω, if K2 t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp2 h2V6 t ^ j * (1 - refRate sp2 h2V6 t) ^ (120000 - j)) :
    (∑ ω, if ((∀ t, K1 t ω ≤ 18) ∧ ¬ TheoremBConcl sp1.L) ∨ ((∀ t, K2 t ω ≤ 18) ∧ ¬ TheoremBConcl sp2.L)
      then P ω else 0) ≤ 2e-9 := by
  have hA : ∀ (sp : S3Prog) (hV6 : sp.V6), sp.R = sp.L - 1 → 2 ≤ sp.L → (sp.toFam hV6).Hcov →
      ∀ K : Fin 5 → Ω → ℕ, (∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
        ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp hV6 t ^ j * (1 - refRate sp hV6 t) ^ (120000 - j)) →
      (∑ ω, if (∀ t, K t ω ≤ 18) ∧ ¬ TheoremBConcl sp.L then P ω else 0) ≤ 1e-9 := by
    intro sp hV6 hR hL hcov K hlaw
    by_cases hB : TheoremBConcl sp.L
    · have : (∑ ω, if (∀ t, K t ω ≤ 18) ∧ ¬ TheoremBConcl sp.L then P ω else 0) = 0 :=
        Finset.sum_eq_zero fun ω _ => ite_eq_right fun h => h.2 hB
      rw [this]
      norm_num
    · rcases theoremB_certified sp hV6 hR hL hcov P hP K hlaw with h | h
      · exact absurd h hB
      · refine le_trans (Finset.sum_le_sum fun ω _ => ?_) h
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd h1.1 h2
        · exact hP ω
        · exact le_rfl
  have e1 := hA sp1 h1V6 h1R h1L h1cov K1 h1law
  have e2 := hA sp2 h2V6 h2R h2L h2cov K2 h2law
  have hu : (∑ ω, if ((∀ t, K1 t ω ≤ 18) ∧ ¬ TheoremBConcl sp1.L) ∨ ((∀ t, K2 t ω ≤ 18) ∧ ¬ TheoremBConcl sp2.L)
      then P ω else 0) ≤ (∑ ω, if (∀ t, K1 t ω ≤ 18) ∧ ¬ TheoremBConcl sp1.L then P ω else 0) +
        (∑ ω, if (∀ t, K2 t ω ≤ 18) ∧ ¬ TheoremBConcl sp2.L then P ω else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    split_ifs <;> first | linarith [hP ω] | (exfalso; tauto)
  linarith

end QECML
