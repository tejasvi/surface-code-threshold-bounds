import QECML.TwoD.HeadlineCount
import QECML.TwoD.T2Final

/-!
# Theorem B and the threshold with the whole 2D lemma proved, up to the family bound

The T2 term is proved from the family bound `FamB`: `S3Geom.t2Count_le` gives
`t2Count ≤ 2·10⁴ n_x e^{-0.02 (n_y - 31)}` at `κ ≤ 1.05`, `cH ≤ 1.05`, so `H2D_T2count` holds with the constants
`constsP = (C1, s1, C2, s2, H0, nyMin) = (4.22e2, 0.2155, 2e4, 0.02, 31, 32)`: the T1 term (proved), the
T2 term with the Lean-proved rate `0.02` (the numerically evaluated rate `0.0351` at `9.61e4` is checked on paper
only).

Hypotheses of `theoremB_a12_proved`: V6, `Hcov`, `R = L - 1`, `L ≥ 2`, the solver weights (bulk in `[0.98, 1.02]`,
half-edges in `[0, 1.02]`), `FamB` on every code (pure geometry; proved in `QECML.TwoD.T2Enc`), `Hstat`.
-/

open Filter Topology

namespace QECML

/-- The constants of the proved bound at `a1 = 12`. -/
noncomputable def constsP : BoundConsts := ⟨4.22e2, 0.2155, 2e4, 0.02, 31, 32⟩

namespace S3Fam

variable (fam : S3Fam)

theorem h2dT1count_P (hD : 4 + 2 * fam.R / fam.L = 5) : fam.H2D_T1count 4 12 constsP 5e-4 := by
  intro nx ny hnx hny hny1
  exact fam.h2dT1count_a12 hD nx ny hnx hny hny1

/-- **The T2 counting bound, from the family bound.** -/
theorem h2dT2count_P (hD : 4 + 2 * fam.R / fam.L = 5)
    (hFB : ∀ nx ny (hnx : 1 ≤ nx) (hny : 1 ≤ ny), (fam.geom nx ny hnx hny).FamB 0.1935) {κ cH : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1.05) (hcH : cH ≤ 1.05) : fam.H2D_T2count 4 12 κ cH constsP 5e-4 := by
  intro nx ny hnx hny hny1
  exact (fam.geom nx ny (by omega) hny1).t2Count_le hD (hFB _ _ _ _) hκ0 hκ hcH

end S3Fam

/-- **Theorem B (a1 = 12), the 2D lemma proved up to the family bound.** -/
theorem theoremB_a12_proved (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hFB : ∀ nx ny (hnx : 1 ≤ nx) (hny : 1 ≤ ny), ((sp.toFam hV6).geom nx ny hnx hny).FamB 0.1935)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        2e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.02 * ((nyOf sp.L H : ℝ) - 31)) := by
  have hD := sp.D_eq_five' hR hL2
  have hcH : 2 * 1.02 / (0.98 * (sp.L : ℝ)) ≤ 1.05 := by
    have hL : (2 : ℝ) ≤ sp.L := by exact_mod_cast hL2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcount := (sp.toFam hV6).h2dT2count_P hD hFB (κ := 1.02 / 0.98) (cH := 2 * 1.02 / (0.98 * sp.L))
    (by norm_num) (by norm_num) hcH
  have hT2ev := (sp.toFam hV6).h2dT2ev_of_T2count constsP (by norm_num) hD.le (by norm_num) Z
    (wmin := 0.98) (wmax := 1.02) (wh := 1.02) (by norm_num) (by norm_num) (by norm_num) hw0
    (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).1) (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).2)
    (fun nx ny hnx hny x => (hwh nx ny hnx hny x).1) (fun nx ny hnx hny x => (hwh nx ny hnx hny x).2)
    (q := 0.100) (by norm_num) (by norm_num) hcount
  have hT2 := (sp.toFam hV6).h2dT2_of_T2ev (by norm_num) Z constsP (by norm_num) (by norm_num) hT2ev
  have hT1 := (sp.toFam hV6).h2dT1_of_routes 4 12 constsP (q := 0.100) (by norm_num) (by norm_num)
    ((sp.toFam hV6).t1RouteExists constsP (by norm_num) hD.le (by norm_num)) ((sp.toFam hV6).h2dT1count_P hD)
  have h2d := (sp.toFam hV6).h2d_of_split 4 12 Z constsP (by norm_num) (by norm_num) hT1 hT2
  have htype := (sp.toFam hV6).htype_of_hcov (show sp.R < sp.L by omega) hcov 0.100
  exact (sp.toFam hV6).theoremB_S3 4 12 Z constsP (by norm_num) (by norm_num) (by norm_num [constsP]) h2d htype
    hstat hq hW hH

/-- **Threshold ≥ 0.100, the 2D lemma proved up to the family bound.** -/
theorem threshold_a12_proved (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hw0 : ∀ nx ny hnx hny e, 0 ≤ (Z nx ny hnx hny).wt e)
    (hwb : ∀ nx ny hnx hny e, S3Geom.isBulk e → 0.98 ≤ (Z nx ny hnx hny).wt e ∧ (Z nx ny hnx hny).wt e ≤ 1.02)
    (hwh : ∀ nx ny hnx hny x, (Z nx ny hnx hny).wt (.bot x) ≤ 1.02 ∧ (Z nx ny hnx hny).wt (.top x) ≤ 1.02)
    (hFB : ∀ nx ny (hnx : 1 ≤ nx) (hny : 1 ≤ ny), ((sp.toFam hV6).geom nx ny hnx hny).FamB 0.1935)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) := by
  have hD := sp.D_eq_five' hR hL2
  have hcH : 2 * 1.02 / (0.98 * (sp.L : ℝ)) ≤ 1.05 := by
    have hL : (2 : ℝ) ≤ sp.L := by exact_mod_cast hL2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcount := (sp.toFam hV6).h2dT2count_P hD hFB (κ := 1.02 / 0.98) (cH := 2 * 1.02 / (0.98 * sp.L))
    (by norm_num) (by norm_num) hcH
  have hT2ev := (sp.toFam hV6).h2dT2ev_of_T2count constsP (by norm_num) hD.le (by norm_num) Z
    (wmin := 0.98) (wmax := 1.02) (wh := 1.02) (by norm_num) (by norm_num) (by norm_num) hw0
    (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).1) (fun nx ny hnx hny e he => (hwb nx ny hnx hny e he).2)
    (fun nx ny hnx hny x => (hwh nx ny hnx hny x).1) (fun nx ny hnx hny x => (hwh nx ny hnx hny x).2)
    (q := 0.100) (by norm_num) (by norm_num) hcount
  have hT2 := (sp.toFam hV6).h2dT2_of_T2ev (by norm_num) Z constsP (by norm_num) (by norm_num) hT2ev
  have hT1 := (sp.toFam hV6).h2dT1_of_routes 4 12 constsP (q := 0.100) (by norm_num) (by norm_num)
    ((sp.toFam hV6).t1RouteExists constsP (by norm_num) hD.le (by norm_num)) ((sp.toFam hV6).h2dT1count_P hD)
  have h2d := (sp.toFam hV6).h2d_of_split 4 12 Z constsP (by norm_num) (by norm_num) hT1 hT2
  have htype := (sp.toFam hV6).htype_of_hcov (show sp.R < sp.L by omega) hcov 0.100
  exact (sp.toFam hV6).pML_square_tendsto_zero 4 12 Z constsP (by norm_num [constsP]) (by norm_num [constsP])
    (by norm_num [constsP]) (by norm_num [constsP]) (by norm_num) (by norm_num [constsP]) h2d htype hstat hq0 hq

end QECML
