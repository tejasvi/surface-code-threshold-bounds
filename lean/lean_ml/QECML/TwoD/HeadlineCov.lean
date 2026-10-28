import QECML.TwoD.Headline
import QECML.S3.TypeFromCov

/-!
# Theorem B and the threshold with Htype replaced by translation covariance

`htype_of_hcov` (for `R < L`) turns the named hypothesis `Htype` (equality of block types, a probabilistic
statement) into the program property `Hcov` ((R2) translation covariance of the stage-1 rule, checked by V2). With
the T1 term proved, Theorem B and the threshold then rest on V6, `Hcov`, `R = L - 1`, `L ≥ 2`, `H2D_T2` and `Hstat`.
-/

open Filter Topology

namespace QECML

/-- **Theorem B (a1 = 12 constants) with the T1 term proved and Htype from covariance.** -/
theorem theoremB_a12_cov (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_T2 sp hV6 hR hL2 Z hT2
    ((sp.toFam hV6).htype_of_hcov (show sp.R < sp.L by omega) hcov 0.100) hstat hq hW hH

/-- **Threshold ≥ 0.100 with the T1 term proved and Htype from covariance.** -/
theorem threshold_a12_cov (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12_T2 sp hV6 hR hL2 Z hT2
    ((sp.toFam hV6).htype_of_hcov (show sp.R < sp.L by omega) hcov 0.100) hstat hq0 hq

end QECML
