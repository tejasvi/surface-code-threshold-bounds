import QECML.TwoD.HeadlineFull

/-!
# Theorem B and the threshold for the registered stage-1 program, without any decoder hypothesis

The theorem bounds the ML failure probability, so the later stages of the auxiliary decoder S3' (the region and top
matchings) may use any minimum-weight solver. `S3Geom.minSolver G wt0` is a minimum-weight solver for any weights
`wt0` (a minimiser exists among the finitely many edge sets); with unit weights the solver weight bounds of
`theoremB_a12_2Dproved` hold trivially. Hence `theoremB_a12_main` / `threshold_a12_main` rest only on V6 and `Hcov`
(properties of the registered stage-1 program, tested by validations), `R = L - 1` and `L ≥ 2` (the registered
geometry), and `Hstat` (the certificate). The stage-1 program, which the certificate measures, is unchanged.
-/

open Filter Topology Finset Classical

namespace QECML

namespace S3Geom

variable (G : S3Geom)

/-- A minimiser of the weight among the edge sets inside `U` with syndrome `T` (when one exists). -/
theorem exists_min_solution (wt0 : G.Ed → ℝ) (U : Set G.V) (T : G.V → ZMod 2) (h : G.Realizable U T) :
    ∃ X, (G.Inside U X ∧ psyn G.w G.h X = T) ∧
      ∀ Y, G.Inside U Y → psyn G.w G.h Y = T →
        (∑ e, if X e ≠ 0 then wt0 e else 0) ≤ ∑ e, if Y e ≠ 0 then wt0 e else 0 := by
  have hne : (univ.filter fun X : G.Ed → ZMod 2 => G.Inside U X ∧ psyn G.w G.h X = T).Nonempty := by
    obtain ⟨X, hX⟩ := h
    exact ⟨X, Finset.mem_filter.2 ⟨Finset.mem_univ _, hX⟩⟩
  obtain ⟨X, hX, hmin⟩ := Finset.exists_min_image _ (fun X : G.Ed → ZMod 2 => ∑ e, if X e ≠ 0 then wt0 e else 0) hne
  exact ⟨X, (Finset.mem_filter.1 hX).2, fun Y hY hYT => hmin Y (Finset.mem_filter.2 ⟨Finset.mem_univ _, hY, hYT⟩)⟩

/-- **A minimum-weight solver for any weights.** -/
noncomputable def minSolver (wt0 : G.Ed → ℝ) : Solver G where
  solve U T := if h : G.Realizable U T then Classical.choose (G.exists_min_solution wt0 U T h) else 0
  wt := wt0
  correct U T h := by
    simp only [dite_eq_left h]
    exact (Classical.choose_spec (G.exists_min_solution wt0 U T h)).1.2
  inside U T h := by
    simp only [dite_eq_left h]
    exact (Classical.choose_spec (G.exists_min_solution wt0 U T h)).1.1
  minimal U T X hX hXT := by
    have h : G.Realizable U T := ⟨X, hX, hXT⟩
    simp only [dite_eq_left h]
    exact (Classical.choose_spec (G.exists_min_solution wt0 U T h)).2 X hX hXT

end S3Geom

/-- **Theorem B (a1 = 12) for the registered stage-1 program.** If the stage-1 program is syndrome-only (V6) and
translation covariant across code sizes (`Hcov`), the geometry is the registered one (`R = L - 1`, `L ≥ 2`), and the
five reference blocks have bad probability at most `5e-4` at `q = 0.100` (`Hstat`), then for every `q ≤ 0.100`,
`W ≥ 1`, `H ≥ 32 L`:
`P_ML,q(fail; W, H) ≤ 4.22e2 n_x e^{-0.2155 (n_y - 31)} + 2e4 n_x e^{-0.02 (n_y - 31)}`,
`n_x = max(5, ⌈W/L⌉)`, `n_y = ⌊H/L⌋`. -/
theorem theoremB_a12_main (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        2e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.02 * ((nyOf sp.L H : ℝ) - 31)) :=
  theoremB_a12_2Dproved sp hV6 hR hL2 (fun nx ny hnx hny => S3Geom.minSolver _ fun _ => 1)
    (fun _ _ _ _ _ => zero_le_one)
    (fun _ _ _ _ _ _ => ⟨by show (0.98 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 1.02; norm_num⟩)
    (fun _ _ _ _ _ => ⟨by show (1 : ℝ) ≤ 1.02; norm_num, by show (1 : ℝ) ≤ 1.02; norm_num⟩) hcov hstat hq hW hH

/-- **Threshold ≥ 0.100 for the registered stage-1 program**: under the hypotheses of `theoremB_a12_main`, for every
`q ∈ [0, 0.100]` the ML failure probability of the square planar code of side `H` tends to `0` as `H → ∞`. -/
theorem threshold_a12_main (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  threshold_a12_2Dproved sp hV6 hR hL2 (fun nx ny hnx hny => S3Geom.minSolver _ fun _ => 1)
    (fun _ _ _ _ _ => zero_le_one)
    (fun _ _ _ _ _ _ => ⟨by show (0.98 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 1.02; norm_num⟩)
    (fun _ _ _ _ _ => ⟨by show (1 : ℝ) ≤ 1.02; norm_num, by show (1 : ℝ) ≤ 1.02; norm_num⟩) hcov hstat hq0 hq

end QECML
