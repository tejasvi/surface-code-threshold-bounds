import QECML.Bernoulli

/-!
# The simulation lemma

Problem 1 can simulate problem 2 if there are a seed space `R` with law `ρ` and a map `T : Ω₁ → R → Ω₂` that
pushes `P₁ ⊗ ρ` to `P₂`, such that the syndrome of `T ω r` is a function `g` of the syndrome of `ω` and of `r`, and
the class of `T ω r` is the class of `ω` shifted by `k r`. Then the randomized decoder
`r, s ↦ ML₂ (g s r) - k r` for problem 1 fails exactly when ML fails on problem 2, so `pML₁ ≤ pML₂`.

This one lemma gives the monotonicity in `q` (degradation) and both halves of the monotonicity in the code size
(restriction and extension).
-/

open Finset

namespace QECML

theorem pML_le_of_sim {Ω₁ Ω₂ R S₁ S₂ C : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype R]
    [Fintype S₁] [DecidableEq S₁] [Fintype S₂] [DecidableEq S₂]
    [Fintype C] [DecidableEq C] [AddCommGroup C] [Nonempty C]
    (P₁ : Ω₁ → ℝ) (syn₁ : Ω₁ → S₁) (cls₁ : Ω₁ → C)
    (P₂ : Ω₂ → ℝ) (syn₂ : Ω₂ → S₂) (cls₂ : Ω₂ → C)
    (ρ : R → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hρ1 : ∑ r, ρ r = 1)
    (T : Ω₁ → R → Ω₂)
    (hT : ∀ f : Ω₂ → ℝ, ∑ ω, ∑ r, P₁ ω * ρ r * f (T ω r) = ∑ ω', P₂ ω' * f ω')
    (g : S₁ → R → S₂) (hg : ∀ ω r, syn₂ (T ω r) = g (syn₁ ω) r)
    (k : R → C) (hk : ∀ ω r, cls₂ (T ω r) = cls₁ ω + k r) :
    pML P₁ syn₁ cls₁ ≤ pML P₂ syn₂ cls₂ := by
  set D₂ := mlDec P₂ syn₂ cls₂
  refine (pML_le_pFailSeed P₁ syn₁ cls₁ ρ hρ hρ1 (fun r s => D₂ (g s r) - k r)).trans (le_of_eq ?_)
  have key : ∀ ω r, (D₂ (g (syn₁ ω) r) - k r = cls₁ ω) ↔ (D₂ (syn₂ (T ω r)) = cls₂ (T ω r)) := by
    intro ω r
    rw [hg, hk, sub_eq_iff_eq_add]
  have h := hT (fun ω' => if D₂ (syn₂ ω') = cls₂ ω' then 0 else 1)
  rw [pML, pFail, pFailSeed]
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [key ω r]

end QECML
