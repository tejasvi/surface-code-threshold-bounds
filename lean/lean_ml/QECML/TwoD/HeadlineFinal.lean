import QECML.TwoD.HeadlineCov
import QECML.TwoD.T2Path

/-!
# Theorem B and the threshold with the 2D lemma entering through its T2 event

The 2D lemma enters only through its own T2 event (`H2D_T2ev`, module `T2Path`: the T1 term is proved and
Lemma C turns every failure into the T2 event), and the block types come from translation covariance (`Hcov`).
Remaining hypotheses: V6 and `Hcov` (properties of the registered program, tested by validations), `R = L - 1` and
`L ≥ 2` (the registered parameters), `H2D_T2ev` (the T2 bound), and `Hstat` (the statistical input).
-/

open Filter Topology

namespace QECML

/-- **Theorem B (a1 = 12 constants), the 2D lemma through its T2 event.** -/
theorem theoremB_a12_final (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2ev 4 12 Z constsA12 0.100 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_cov sp hV6 hR hL2 Z
    ((sp.toFam hV6).h2dT2_of_T2ev (by norm_num) Z constsA12 (by norm_num) (by norm_num) hT2) hcov hstat hq hW hH

/-- **Threshold ≥ 0.100, the 2D lemma through its T2 event.** -/
theorem threshold_a12_final (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2ev 4 12 Z constsA12 0.100 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12_cov sp hV6 hR hL2 Z
    ((sp.toFam hV6).h2dT2_of_T2ev (by norm_num) Z constsA12 (by norm_num) (by norm_num) hT2) hcov hstat hq0 hq

end QECML
