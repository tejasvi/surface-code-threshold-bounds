import QECML.TwoD.RouteNum

/-!
# Theorem B and the threshold with the T1 term of the 2D lemma proved

For `D = 5` (the registered `R = L - 1`, `L ≥ 2`) the T1 term of the 2D lemma at `a1 = 12` is a theorem: route
existence (`S3Fam.t1RouteExists`) and the route count (`S3Fam.h2dT1count_a12`) give `H2D_T1`
(`S3Fam.h2dT1_a12`). The 2D lemma then reduces to its T2 term (`S3Fam.h2d_a12_of_T2`), and Theorem B and the
threshold hold with `H2D_T2`, `Htype` and `Hstat` as the only hypotheses besides V6 and `R = L - 1`
(`theoremB_a12_T2`, `threshold_a12_T2`).
-/

open Filter Topology

namespace QECML

namespace S3Fam

variable (fam : S3Fam)

/-- **The T1 term at a1 = 12 is proved** (for `D = 5`): Hypothesis (H) at `(q, 5e-4)` implies
`P(T1) ≤ 4.22e2 n_x e^{-0.2155 (n_y - 31)}`. -/
theorem h2dT1_a12 (hD : 4 + 2 * fam.R / fam.L = 5) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    fam.H2D_T1 4 12 constsA12 q 5e-4 :=
  fam.h2dT1_of_routes 4 12 constsA12 hq0 hq1
    (fam.t1RouteExists constsA12 (by norm_num) (by omega) (by norm_num)) (fam.h2dT1count_a12 hD)

/-- **The 2D lemma at a1 = 12 from its T2 term alone** (for `D = 5`). -/
theorem h2d_a12_of_T2 (hD : 4 + 2 * fam.R / fam.L = 5)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hT2 : fam.H2D_T2 4 12 Z constsA12 q 5e-4) : fam.H2D (fam.S3decFam 4 12 Z) constsA12 q 5e-4 :=
  fam.h2d_of_split 4 12 Z constsA12 hq0 hq1 (fam.h2dT1_a12 hD hq0 hq1) hT2

end S3Fam

theorem S3Prog.D_eq_five' (sp : S3Prog) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L) : 4 + 2 * sp.R / sp.L = 5 :=
  S3Geom.D_eq_five ⟨sp.L, sp.R, 5, 5, sp.hL, by norm_num, by norm_num⟩ hR hL2

/-- **Theorem B (a1 = 12 constants) with the T1 term proved.** For the registered stage-1 program with
`R = L - 1`, `L ≥ 2`: V6, the T2 term of the 2D lemma, Htype and Hstat imply the ML bound. -/
theorem theoremB_a12_T2 (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12 sp hV6 Z ((sp.toFam hV6).h2d_a12_of_T2 (sp.D_eq_five' hR hL2) Z (by norm_num) (by norm_num) hT2)
    htype hstat hq hW hH

/-- **Threshold ≥ 0.100 with the T1 term proved**: under the hypotheses of `theoremB_a12_T2`, `P_ML → 0` along
square codes for every `q ∈ [0, 0.100]`. -/
theorem threshold_a12_T2 (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12 sp hV6 Z ((sp.toFam hV6).h2d_a12_of_T2 (sp.D_eq_five' hR hL2) Z (by norm_num) (by norm_num) hT2)
    htype hstat hq0 hq

end QECML
