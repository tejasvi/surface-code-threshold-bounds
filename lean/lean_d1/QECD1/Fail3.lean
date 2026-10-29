import QECD1.T1Final3
import QECD1.Program3

/-!
# The failure bound of S3' from the named hypotheses (3D)

`fail_bound3` (T1Final3) assumes (H_eps) at `ε*` on the undeclared blocks. For a decoder family (`S3Fam3`), that
follows from the covariance hypothesis `Hcov3` and the statistical input `Hstat3` (`htype3_of_hcov3`,
`heps_of_types`). So on every code of `n_t × n_x × n_y ≥ 5 × 5 × 5` blocks, with a minimum-weight solver with unit
bulk weights and half-edge weights in `[0, wh]`:

  `P(S3' fails) ≤ n_t n_x (h_s + 1) · (α e^{-s1 (n_y - 47)} + RF (topB3ex + 8.3757 topB3) e^{λ (67 + 2 wh / 35)}
  e^{-s (n_y - 47)})` (`fail_bound_fam3`).

`fail_bound_prog3` states it for the registered stage-1 program under V6 (`S3Prog3.toFam3`).
-/

namespace QECD1

/-- **The failure bound of S3' for a decoder family**, from `Hcov3` and `Hstat3` at `ε*`. -/
theorem fail_bound_fam3 (fam : S3Fam3) (hcov : fam.Hcov3) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hstat : fam.Hstat3 p eps) {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx) (hny : 5 ≤ ny)
    (Z : Solver3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)) {wh : ℝ} (hwh0 : 0 ≤ wh) (hwt0 : ∀ e, 0 ≤ Z.wt e)
    (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1) (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) :
    prob p (fun X => failsOn3 (dec3 (fam.stage1 nt nx ny) Z) (toZ2 X)) ≤
      ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (alQ : ℝ) * Real.exp (-s1 * ((ny : ℝ) - 47)) +
        ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) *
          Real.exp (lam * (67 + 2 * wh / 35)) * Real.exp (-sT * ((ny : ℝ) - 47)) :=
  (fam.stage1 nt nx ny).fail_bound3 Z hp0 hp1 (by omega) (by omega) (by omega) hwh0 hwt0 hunit hwh
    {b | ¬ declared3 ny b} (fun _ hb => hb)
    (fun b hb => fam.heps_of_types hp0 hp1 (fam.htype3_of_hcov3 hcov p) hstat hnt hnx hny b hb)

/-- **The failure bound of S3' for the registered stage-1 program** (under V6), from `Hcov3` and `Hstat3` at `ε*`. -/
theorem fail_bound_prog3 (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hstat : (sp.toFam3 hV6).Hstat3 p eps) {nt nx ny : ℕ} (hnt : 5 ≤ nt) (hnx : 5 ≤ nx)
    (hny : 5 ≤ ny) (Z : Solver3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)) {wh : ℝ} (hwh0 : 0 ≤ wh)
    (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1) (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) :
    prob p (fun X => failsOn3 (dec3 ((sp.prog nt nx ny).toStage13 (hV6 nt nx ny)) Z) (toZ2 X)) ≤
      ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (alQ : ℝ) * Real.exp (-s1 * ((ny : ℝ) - 47)) +
        ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) *
          Real.exp (lam * (67 + 2 * wh / 35)) * Real.exp (-sT * ((ny : ℝ) - 47)) :=
  fail_bound_fam3 (sp.toFam3 hV6) hcov hp0 hp1 hstat hnt hnx hny Z hwh0 hwt0 hunit hwh

end QECD1
