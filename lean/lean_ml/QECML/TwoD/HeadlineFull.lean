import QECML.TwoD.HeadlineProved
import QECML.TwoD.T2Enc

/-!
# Theorem B and the threshold with the whole 2D lemma proved

`S3Geom.famB_of` (module `T2Enc`): the family bound `FamB G 0.1935` holds on every code with `D = 5`
(families as words of the family automaton, witnesses as words of the witness automaton). Hence
`theoremB_a12_2Dproved` / `threshold_a12_2Dproved` carry no hypothesis on the 2D lemma: the remaining hypotheses are V6
and `Hcov` (program properties), `R = L - 1` and `L ≥ 2` (registered geometry), the solver weights (bulk in
`[0.98, 1.02]`, half-edges in `[0, 1.02]`; the registered decoder's weights), and `Hstat` (the statistical input).
The T2 constants are the Lean-proved ones (`2e4`, `0.02`); the numerically evaluated
`9.61e4`, `0.0351` are checked on paper only.
-/

open Filter Topology

namespace QECML

/-- **Theorem B (a1 = 12), the 2D lemma proved.** For the registered stage-1 program with `R = L - 1`, `L ≥ 2`: V6,
`Hcov`, the solver weight bounds and `Hstat` imply, for every `q ≤ 0.100`, `W ≥ 1`, `H ≥ 32 L`,
`P_ML,q(fail; W, H) ≤ 4.22e2 n_x e^{-0.2155 (n_y - 31)} + 2e4 n_x e^{-0.02 (n_y - 31)}`. -/
theorem theoremB_a12_2Dproved (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        2e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.02 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_proved sp hV6 hR hL2 Z hw0 hwb hwh
    (fun _ _ _ _ => S3Geom.famB_of (sp.D_eq_five' hR hL2)) hcov hstat hq hW hH

/-- **Threshold ≥ 0.100, the 2D lemma proved.** -/
theorem threshold_a12_2Dproved (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12_proved sp hV6 hR hL2 Z hw0 hwb hwh
    (fun _ _ _ _ => S3Geom.famB_of (sp.D_eq_five' hR hL2)) hcov hstat hq0 hq

end QECML
