import QECML.TwoD.HeadlineFinal
import QECML.TwoD.T2Count

/-!
# Theorem B and the threshold with the T2 term in counting form

`theoremB_a12_countB` and `threshold_a12_countB` replace `H2D_T2ev` of `theoremB_a12_final` by
* the solver weight bounds of the registered decoder (bulk weights in `[0.98, 1.02]`, half-edge weights in
  `[0, 1.02]`), and
* `H2D_T2count` (pure counting on block geometry: the `ε`-weighted number of counted-block sets of valid T2 skeletons
  with metric ratio `1.02 / 0.98` and boundary constant `2 · 1.02 / (0.98 L)`).
The reduction is `S3Fam.h2dT2ev_of_T2count` (T2 skeleton existence, proved). The other hypotheses are those of
`theoremB_a12_final`: V6, `Hcov`, `R = L - 1`, `L ≥ 2`, `Hstat`.
-/

open Filter Topology

namespace QECML

/-- **Theorem B (a1 = 12 constants), T2 term in counting form.** -/
theorem theoremB_a12_countB (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hcount : (sp.toFam hV6).H2D_T2count 4 12 (1.02 / 0.98) (2 * 1.02 / (0.98 * sp.L)) constsA12 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_final sp hV6 hR hL2 Z
    ((sp.toFam hV6).h2dT2ev_of_T2count constsA12 (by norm_num) (sp.D_eq_five' hR hL2).le (by norm_num) Z
      (wmin := 0.98) (wmax := 1.02) (wh := 1.02) (by norm_num) (by norm_num) (by norm_num) hw0
      (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).1) (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).2)
      (fun nx ny hnx hny x => (hwh nx ny hnx hny x).1) (fun nx ny hnx hny x => (hwh nx ny hnx hny x).2)
      (q := 0.100) (by norm_num) (by norm_num) hcount)
    hcov hstat hq hW hH

/-- **Threshold ≥ 0.100, T2 term in counting form.** -/
theorem threshold_a12_countB (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hcount : (sp.toFam hV6).H2D_T2count 4 12 (1.02 / 0.98) (2 * 1.02 / (0.98 * sp.L)) constsA12 5e-4)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12_final sp hV6 hR hL2 Z
    ((sp.toFam hV6).h2dT2ev_of_T2count constsA12 (by norm_num) (sp.D_eq_five' hR hL2).le (by norm_num) Z
      (wmin := 0.98) (wmax := 1.02) (wh := 1.02) (by norm_num) (by norm_num) (by norm_num) hw0
      (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).1) (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).2)
      (fun nx ny hnx hny x => (hwh nx ny hnx hny x).1) (fun nx ny hnx hny x => (hwh nx ny hnx hny x).2)
      (q := 0.100) (by norm_num) (by norm_num) hcount)
    hcov hstat hq0 hq

end QECML
