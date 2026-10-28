import QECML.S3.Program
import QECML.CPConfidence

/-!
# Conditional statements with the numerically evaluated constants

* `constsA12`: the bound at `ε = 5e-4` with the level parameter `a1 = 12`:
  `4.22e2 n_x e^{-0.2155 (n_y - 31)} + 9.61e4 n_x e^{-0.0351 (n_y - 31)}`, `n_y ≥ 32`. The rates are the numerically
  evaluated values rounded down (s1 = 0.2155565…, s2 = 0.0351690…, C1 = 421.55…, C2 = 96077.0…), and
  `C1(0.2155) = 417.81 ≤ 422`, `C2(0.0351) = 91225.8 ≤ 96100`. These constants are not proved in Lean: the theorems
  of this module assume the 2D lemma with them (hypothesis `H2D`).
* `H2Dall`, `theoremB_every_a1`: the stage-1 hypotheses (`Htype`, `Hstat`) do not involve `a1`, so one certificate
  serves every admissible `a1`: with the 2D lemma for every admissible `a1` (constants `Kof a1`), Theorem B holds for
  every admissible `a1` at once.
* `theoremB_a12`: the conditional form, for the registered stage-1 program under V6 (syndrome-only), with S3'(a0 = 4,
  a1 = 12) and the constants `constsA12`, at `q* = 0.100`, `ε* = 5e-4`; `H ≥ 32 L`.
* `pML_square_tendsto_zero`, `threshold_a12`: along square codes the ML failure probability tends to `0` for every
  `q ≤ 0.100`, i.e. the optimal threshold of the planar code under i.i.d. bit flips is at least `0.100` (under the
  same hypotheses).
-/

open Filter Topology

namespace QECML

/-- The constants at `ε̂ = 5e-4`, `a1 = 12`: `C1 = 4.22e2`, `s1 = 0.2155`, `C2 = 9.61e4`, `s2 = 0.0351`, `H0 = 31`,
`n_y ≥ 32` (rates rounded down from the numerical evaluation). -/
noncomputable def constsA12 : BoundConsts := ⟨4.22e2, 0.2155, 9.61e4, 0.0351, 31, 32⟩

namespace S3Fam

variable (fam : S3Fam)

/-- **The 2D lemma for every admissible `a1`** (constants `Kof a1`, admissibility `adm`). -/
def H2Dall (a0 : ℕ) (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny))
    (adm : ℕ → Prop) (Kof : ℕ → BoundConsts) (q ε : ℝ) : Prop :=
  ∀ a1, adm a1 → fam.H2D (fam.S3decFam a0 a1 Z) (Kof a1) q ε

/-- **One certificate, every admissible `a1`**: Theorem B holds for every admissible `a1` at once. -/
theorem theoremB_every_a1 (a0 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (adm : ℕ → Prop)
    (Kof : ℕ → BoundConsts) {qs ε : ℝ} (hqs0 : 0 ≤ qs) (hqs : qs ≤ 1 / 2)
    (h2d : fam.H2Dall a0 Z adm Kof qs ε) (htype : fam.Htype qs) (hstat : fam.Hstat qs ε) :
    ∀ a1, adm a1 → 5 ≤ (Kof a1).nyMin → ∀ q, q ≤ qs → ∀ W H : ℕ, 1 ≤ W → (Kof a1).nyMin * fam.L ≤ H →
      pMLPlanar (W - 1) (H - 1) q ≤ (Kof a1).eval (nxOf fam.L W) (nyOf fam.L H) :=
  fun a1 ha1 hK _q hq _W _H hW hH =>
    fam.theoremB_S3 a0 a1 Z (Kof a1) hqs0 hqs hK (h2d a1 ha1) htype hstat hq hW hH

end S3Fam

/-- **Theorem B (a1 = 12, numerically evaluated constants)**, for the registered stage-1 program `sp`. Hypotheses:
V6 (the program is syndrome-only), the 2D lemma for the Lean decoder S3'(a0 = 4, a1 = 12) with `constsA12`, type
equality, and
the statistical input, at `q* = 0.100`, `ε* = 5e-4`. Conclusion: for every `q ≤ 0.100`, `W ≥ 1`, `H ≥ 32 L`,
`P_ML,q(fail) ≤ 4.22e2 n_x e^{-0.2155 (n_y - 31)} + 9.61e4 n_x e^{-0.0351 (n_y - 31)}`,
`n_x = max(5, ⌈W/L⌉)`, `n_y = ⌊H/L⌋`. -/
theorem theoremB_a12 (sp : S3Prog) (hV6 : sp.V6)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (h2d : (sp.toFam hV6).H2D ((sp.toFam hV6).S3decFam 4 12 Z) constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) :=
  (sp.toFam hV6).theoremB_S3 4 12 Z constsA12 (by norm_num) (by norm_num) (by norm_num [constsA12]) h2d htype
    hstat hq hW hH

/-! ## Square codes: the bound and the ML failure probability tend to 0 -/

theorem nxOf_le {L : ℕ} (hL : 1 ≤ L) (H : ℕ) : nxOf L H ≤ nyOf L H + 6 := by
  have h1 := Nat.lt_div_mul_add (a := H) (b := L) (by omega)
  have h2 : (H + L - 1) / L < H / L + 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), add_mul]
    omega
  simp only [nxOf, nyOf]
  generalize (H + L - 1) / L = b at h2 ⊢
  generalize H / L = a at h2 ⊢
  omega

/-- `(n + c) e^{-s n} → 0` along `ℕ` for `s > 0`. -/
theorem tendsto_lin_mul_exp_neg {s : ℝ} (c : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ((n : ℝ) + c) * Real.exp (-(s * n))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => s * (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop hs
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1
  have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h4 := (h2.const_mul (1 / s)).add (h3.const_mul c)
  simp only [mul_zero, add_zero] at h4
  refine h4.congr fun n => ?_
  simp only [Function.comp, pow_one]
  field_simp

/-- The bound tends to `0` along square codes (`W = H → ∞`), for nonnegative prefactors and positive rates. -/
theorem eval_tendsto_zero (K : BoundConsts) (hC1 : 0 ≤ K.C1) (hC2 : 0 ≤ K.C2) (hs1 : 0 < K.s1)
    (hs2 : 0 < K.s2) {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun H : ℕ => K.eval (nxOf L H) (nyOf L H)) atTop (𝓝 0) := by
  have hny : Tendsto (fun H : ℕ => nyOf L H) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  have t1 := ((tendsto_lin_mul_exp_neg 6 hs1).comp hny).const_mul (K.C1 * Real.exp (K.s1 * K.H0))
  have t2 := ((tendsto_lin_mul_exp_neg 6 hs2).comp hny).const_mul (K.C2 * Real.exp (K.s2 * K.H0))
  have hup := t1.add t2
  simp only [mul_zero, add_zero] at hup
  have key : ∀ (C s : ℝ) (H : ℕ), 0 ≤ C →
      C * (nxOf L H : ℝ) * Real.exp (-s * ((nyOf L H : ℝ) - K.H0)) ≤
        C * Real.exp (s * K.H0) * (((nyOf L H : ℕ) : ℝ) + 6) * Real.exp (-(s * ((nyOf L H : ℕ) : ℝ))) := by
    intro C s H hC
    have he : Real.exp (-s * ((nyOf L H : ℝ) - K.H0)) =
        Real.exp (s * K.H0) * Real.exp (-(s * ((nyOf L H : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have hnx : (nxOf L H : ℝ) ≤ ((nyOf L H : ℕ) : ℝ) + 6 := by exact_mod_cast nxOf_le hL H
    have e1 := Real.exp_pos (s * K.H0)
    have e2 := Real.exp_pos (-(s * ((nyOf L H : ℕ) : ℝ)))
    rw [he]
    calc C * (nxOf L H : ℝ) * (Real.exp (s * K.H0) * Real.exp (-(s * ((nyOf L H : ℕ) : ℝ))))
        = (C * Real.exp (s * K.H0)) * (nxOf L H : ℝ) * Real.exp (-(s * ((nyOf L H : ℕ) : ℝ))) := by ring
      _ ≤ (C * Real.exp (s * K.H0)) * (((nyOf L H : ℕ) : ℝ) + 6) *
            Real.exp (-(s * ((nyOf L H : ℕ) : ℝ))) := by
          gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun H => ?_) (Eventually.of_forall fun H => ?_)
  · simp only [BoundConsts.eval]
    have := Real.exp_pos (-K.s1 * ((nyOf L H : ℝ) - K.H0))
    have := Real.exp_pos (-K.s2 * ((nyOf L H : ℝ) - K.H0))
    positivity
  · simp only [BoundConsts.eval, Function.comp]
    have k1 := key K.C1 K.s1 H hC1
    have k2 := key K.C2 K.s2 H hC2
    linarith

theorem pMLPlanar_nonneg (w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ pMLPlanar w h q := by
  unfold pMLPlanar pML pFail
  refine Finset.sum_nonneg fun e _ => ?_
  split_ifs
  · exact le_rfl
  · exact bernProd_nonneg hq0 hq1 e

/-- Along square codes (`W = H`, distance `H + 1`), the ML failure probability tends to `0` at every `q ≤ q*`. -/
theorem S3Fam.pML_square_tendsto_zero (fam : S3Fam) (a0 a1 : ℕ)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver (fam.geom nx ny hnx hny)) (K : BoundConsts)
    (hC1 : 0 ≤ K.C1) (hC2 : 0 ≤ K.C2) (hs1 : 0 < K.s1) (hs2 : 0 < K.s2) {qs ε : ℝ} (hqs : qs ≤ 1 / 2)
    (hK : 5 ≤ K.nyMin) (h2d : fam.H2D (fam.S3decFam a0 a1 Z) K qs ε) (htype : fam.Htype qs)
    (hstat : fam.Hstat qs ε) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ qs) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (eval_tendsto_zero K hC1 hC2 hs1 hs2 fam.hL)
    (Eventually.of_forall fun H => pMLPlanar_nonneg _ _ hq0 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop (K.nyMin * fam.L + 1)] with H hH
  exact fam.theoremB_S3 a0 a1 Z K (hq0.trans hq) hqs hK h2d htype hstat hq (by omega) (by omega)

/-- **Threshold (a1 = 12 constants)**: under the hypotheses of `theoremB_a12`, for every `q ∈ [0, 0.100]` the ML
failure probability of the square planar code of side `H` tends to `0` as `H → ∞`. -/
theorem threshold_a12 (sp : S3Prog) (hV6 : sp.V6)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (h2d : (sp.toFam hV6).H2D ((sp.toFam hV6).S3decFam 4 12 Z) constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (H - 1) (H - 1) q) atTop (𝓝 0) :=
  (sp.toFam hV6).pML_square_tendsto_zero 4 12 Z constsA12 (by norm_num [constsA12]) (by norm_num [constsA12])
    (by norm_num [constsA12]) (by norm_num [constsA12]) (by norm_num) (by norm_num [constsA12]) h2d htype hstat
    hq0 hq

end QECML
