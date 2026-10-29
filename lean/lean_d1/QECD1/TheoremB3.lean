import QECD1.MonoSize3
import QECD1.Fail3

/-!
# The ML bound in Lean: the ML failure probability of the 3D code, from the failure bound of S3'

The bound on the ML failure probability and its proof (monotonicity, ML optimality, the bound on S3'), as the 2D
`TheoremB`:
* `P_ML,q ≤ P_ML,0.02` for `q ≤ 0.02` (monotonicity in `q`, `pML3_mono_q`);
* `P_ML,0.02(T, W, H) ≤ P_ML,0.02` on the code of `n_t × n_x × n_y` blocks with `n_t = max(5, ⌈(T + 1)/L⌉)`,
  `n_x = max(5, ⌈W/L⌉)`, `n_y = ⌊H/L⌋`, `L = 35` (monotonicity in the size, `pML3_mono_size`);
* `≤ Pr_{0.02}(S3' fails)` on that code, for the registered stage-1 program and the minimum-weight solver with unit
  weights (`Solver3.unit`) (ML optimality, `pML_le_pFailCorr`; `pFailCorr_eq_prob` identifies the two ways of
  writing the failure probability);
* `≤` the failure bound of S3' (`fail_bound_prog3`) from `Hcov3` and `Hstat3` at `p = 0.02`, `ε* = 1.85e-5`.

`d1B_lean` states the result with the constants of the Lean proof, `d1B_num` with rounded numbers:

  `P_ML,q(fail) ≤ 804 n_x n_t e^{-0.1008 (n_y - 47)} + 5.11e6 n_x n_t e^{-0.007 (n_y - 47)}`

for every `q ≤ 0.02`, `T ≥ 0`, `W ≥ 1`, `H ≥ 5 L`. (The constants of the paper's statement, `877, 0.1008, 6.21e6,
0.0077`, come from the registered computation. The Lean T1 term has the paper's rate `0.1008` with the smaller prefactor
804; the Lean T2 rate `s = 0.007` is smaller than the paper's, so the Lean bound does not imply the paper's numbers.)

`pML3_cube_tendsto_zero`: along cube codes (`T + 1 = W = H → ∞`) the ML failure probability tends to `0` for every
`q ∈ [0, 0.02]`, so the optimal threshold of the phenomenological model is at least `0.02`, under the same named
hypotheses (V6, `Hcov3`, `Hstat3`).
-/

open Filter Topology

namespace QECD1

section Bridge

variable {T w h : ℕ}

/-- Boolean configurations as `ZMod 2` configurations. -/
def toZ2Equiv : (PEdge3 T w h → Bool) ≃ (PEdge3 T w h → ZMod 2) where
  toFun := toZ2
  invFun E e := decide (E e = 1)
  left_inv X := by
    funext e
    unfold toZ2
    cases hX : X e <;> simp [hX, show (0 : ZMod 2) ≠ 1 by decide]
  right_inv E := by
    funext e
    unfold toZ2
    rcases zmod2_cases (E e) with h | h <;> simp [h]

theorem toZ2Equiv_apply (X : PEdge3 T w h → Bool) : toZ2Equiv X = toZ2 X := rfl

theorem pw_eq_bernProd (p : ℝ) (X : PEdge3 T w h → Bool) : pw p X = bernProd p (toZ2 X) := by
  unfold pw bernProd
  refine Finset.prod_congr rfl fun e _ => ?_
  unfold bern toZ2
  cases X e <;> simp [show (1 : ZMod 2) ≠ 0 by decide]

/-- The failure probability of a correction decoder, written as in 2D (`pFailCorr`) and as in the decoder
modules (`prob` of `failsOn3`), are equal. -/
theorem pFailCorr_eq_prob (p : ℝ) (dec : (PVert3 T w h → ZMod 2) → (PEdge3 T w h → ZMod 2)) :
    pFailCorr (bernProd p) psyn3 pcls3 dec = prob p (fun X => failsOn3 dec (toZ2 X)) := by
  unfold pFailCorr prob
  refine (Fintype.sum_equiv toZ2Equiv _ _ fun X => ?_).symm
  dsimp only
  rw [toZ2Equiv_apply]
  split_ifs with h1 h2 h2
  · exact absurd h2 h1
  · exact pw_eq_bernProd p X
  · rfl
  · exact (h1 h2).elim

end Bridge

/-! ## A minimum-weight solver with unit weights -/

section Unit

open Classical

variable {T w h : ℕ}

/-- The number of edges of `X`. -/
noncomputable def ecount (X : PEdge3 T w h → ZMod 2) : ℝ := ∑ e, if X e ≠ 0 then (1 : ℝ) else 0

/-- A fewest-edges edge set inside `U` with syndrome `S` (classical choice), or `0` if there is none. -/
noncomputable def solveUnit (U : Set (PVert3 T w h)) (S : PVert3 T w h → ZMod 2) : PEdge3 T w h → ZMod 2 :=
  if hR : Realizable3 U S then
    Classical.choose (Finset.exists_min_image (Finset.univ.filter fun X => Inside3 U X ∧ psyn3 X = S) ecount
      (by obtain ⟨X, hX⟩ := hR; exact ⟨X, by simpa using hX⟩))
  else 0

theorem solveUnit_spec {U : Set (PVert3 T w h)} {S : PVert3 T w h → ZMod 2} (hR : Realizable3 U S) :
    (Inside3 U (solveUnit U S) ∧ psyn3 (solveUnit U S) = S) ∧
      ∀ X, Inside3 U X → psyn3 X = S → ecount (solveUnit U S) ≤ ecount X := by
  unfold solveUnit
  simp only [hR, ↓reduceDIte]
  generalize_proofs hne
  obtain ⟨hmem, hmin⟩ := Classical.choose_spec hne
  exact ⟨by simpa using hmem, fun X hX hXS => hmin X (by simpa using And.intro hX hXS)⟩

/-- **A minimum-weight solver with unit weights** on every code (bulk edges and half-edges of weight 1). -/
noncomputable def Solver3.unit (T w h : ℕ) : Solver3 T w h where
  solve := solveUnit
  wt := fun _ => 1
  correct _ _ hR := (solveUnit_spec hR).1.2
  inside _ _ hR := (solveUnit_spec hR).1.1
  minimal _ _ X hX hXS := (solveUnit_spec ⟨X, hX, hXS⟩).2 X hX hXS

end Unit

/-! ## Block counts -/

/-- Rounded-up block count of a side of `m` checks: `max(5, ⌈m/35⌉)` (used for `W` and `T + 1`). -/
def blkUp (m : ℕ) : ℕ := max 5 ((m + 34) / 35)

theorem le_blkUp_mul (m : ℕ) : m ≤ blkUp m * 35 := by
  have h1 : m + 34 < (m + 34) / 35 * 35 + 35 := Nat.lt_div_mul_add (by norm_num)
  have h2 : (m + 34) / 35 * 35 ≤ blkUp m * 35 := Nat.mul_le_mul_right 35 (le_max_right _ _)
  omega

theorem five_le_blkUp (m : ℕ) : 5 ≤ blkUp m := le_max_left _ _

/-! ## The ML bound -/

/-- **The ML bound (Lean constants)**, for the registered stage-1 program `sp`. Hypotheses: V6 (the program is
syndrome-only), the covariance hypothesis `Hcov3` and the statistical input `Hstat3` at `p = 0.02`,
`ε* = 1.85e-5`. Conclusion: for every `q ≤ 0.02`, `T ≥ 0`, `W ≥ 1`, `H ≥ 5 · 35`, the ML failure probability of the
code with `T + 1` layers, `W` columns and `H` rows is at most
`12 n_t n_x (α e^{-s1 (n_y - 47)} + RF (topB3ex + 8.3757 topB3) e^{λ (67 + 2/35)} e^{-s (n_y - 47)})`, with
`n_t = max(5, ⌈(T + 1)/35⌉)`, `n_x = max(5, ⌈W/35⌉)`, `n_y = ⌊H/35⌋`. -/
theorem d1B_lean (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3)
    (hstat : (sp.toFam3 hV6).Hstat3 0.02 eps) {q : ℝ} (hq : q ≤ 0.02) {T W H : ℕ} (hW : 1 ≤ W)
    (hH : 5 * 35 ≤ H) :
    pML3 T (W - 1) (H - 1) q ≤
      ((blkUp (T + 1) * blkUp W * (hs3 + 1) : ℕ) : ℝ) * (alQ : ℝ) *
          Real.exp (-s1 * (((H / 35 : ℕ) : ℝ) - 47)) +
        ((blkUp (T + 1) * blkUp W * (hs3 + 1) : ℕ) : ℝ) * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) *
          Real.exp (lam * (67 + 2 * 1 / 35)) * Real.exp (-sT * (((H / 35 : ℕ) : ℝ) - 47)) := by
  have hnt5 := five_le_blkUp (T + 1)
  have hnx5 := five_le_blkUp W
  have hny5 : 5 ≤ H / 35 := (Nat.le_div_iff_mul_le (by norm_num)).2 hH
  have hTnt := le_blkUp_mul (T + 1)
  have hWnx := le_blkUp_mul W
  have hnyH : H / 35 * 35 ≤ H := Nat.div_mul_le_self H 35
  have hp0 : (0 : ℝ) ≤ 0.02 := by norm_num
  have hp1 : (0.02 : ℝ) ≤ 1 := by norm_num
  set nt := blkUp (T + 1)
  set nx := blkUp W
  set ny := H / 35
  set Z := Solver3.unit (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1)
  set S := (sp.prog nt nx ny).toStage13 (hV6 nt nx ny)
  calc pML3 T (W - 1) (H - 1) q
      ≤ pML3 T (W - 1) (H - 1) 0.02 := pML3_mono_q _ _ _ hq (by norm_num)
    _ ≤ pML3 (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1) 0.02 :=
        pML3_mono_size (by omega) (by omega) (by omega) hp0 hp1
    _ ≤ pFailCorr (bernProd 0.02) psyn3 pcls3 (dec3 S Z) :=
        pML_le_pFailCorr (bernProd 0.02) psyn3 (pcls3Hom (nt * 35 - 1) (nx * 35 - 1) (ny * 35 - 1))
          (bernProd_nonneg hp0 hp1) (dec3 S Z)
    _ = prob 0.02 (fun X => failsOn3 (dec3 S Z) (toZ2 X)) := pFailCorr_eq_prob _ _
    _ ≤ _ := fail_bound_prog3 sp hV6 hcov hp0 hp1 hstat hnt5 hnx5 hny5 Z zero_le_one (fun _ => zero_le_one)
        (fun _ _ => rfl) (fun _ _ => le_rfl)

/-! ## Numerical constants -/

theorem exp_c2_le : Real.exp (lam * (67 + 2 * 1 / 35)) ≤ 2.557 := by
  have e : lam * (67 + 2 * 1 / 35) = 2347 / 2500 := by norm_num [lam]
  rw [e]
  have h := Real.exp_bound (x := 2347 / 2500) (by norm_num [abs_of_pos]) (n := 14) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  linarith [h.1, h.2]

/-- `C1 = 12 α ≤ 804`. -/
theorem c1_le : 12 * (alQ : ℝ) ≤ 804 := by norm_num [alQ]

/-- `C2 = 12 RF (topB3ex + 8.3757 topB3) e^{λ (67 + 2/35)} ≤ 5.11e6` (value about `5.1063e6`). -/
theorem c2_le : 12 * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * Real.exp (lam * (67 + 2 * 1 / 35)) ≤ 5.11e6 := by
  have hpos : 0 ≤ 12 * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) := by
    have h1 := topB3ex_nonneg
    have h2 := topB3_nonneg
    have h3 : (0 : ℝ) ≤ RFq := by norm_num [RFq]
    positivity
  calc 12 * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * Real.exp (lam * (67 + 2 * 1 / 35))
      ≤ 12 * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * 2.557 := mul_le_mul_of_nonneg_left exp_c2_le hpos
    _ ≤ 5.11e6 := by
        unfold topB3ex topB3 JF2 Jbar2
        norm_num [RFq, qUpT, qLoT, qmUp, qmLo, qpUp, qpLo, eps]

/-- **The ML bound (rounded constants)**: under the hypotheses of `d1B_lean`, for every `q ≤ 0.02`, `T ≥ 0`,
`W ≥ 1`, `H ≥ 5 · 35`,
`P_ML,q(fail) ≤ 804 n_t n_x e^{-0.1008 (n_y - 47)} + 5.11e6 n_t n_x e^{-0.007 (n_y - 47)}`,
`n_t = max(5, ⌈(T + 1)/35⌉)`, `n_x = max(5, ⌈W/35⌉)`, `n_y = ⌊H/35⌋`. -/
theorem d1B_num (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3)
    (hstat : (sp.toFam3 hV6).Hstat3 0.02 eps) {q : ℝ} (hq : q ≤ 0.02) {T W H : ℕ} (hW : 1 ≤ W)
    (hH : 5 * 35 ≤ H) :
    pML3 T (W - 1) (H - 1) q ≤
      804 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-0.1008 * (((H / 35 : ℕ) : ℝ) - 47)) +
        5.11e6 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-0.007 * (((H / 35 : ℕ) : ℝ) - 47)) := by
  refine (d1B_lean sp hV6 hcov hstat hq hW hH).trans ?_
  have hm : (0 : ℝ) ≤ (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) := by positivity
  have e1 := Real.exp_pos (-s1 * (((H / 35 : ℕ) : ℝ) - 47))
  have e2 := Real.exp_pos (-sT * (((H / 35 : ℕ) : ℝ) - 47))
  have hs1 : s1 = 0.1008 := by norm_num [s1]
  have hsT : sT = 0.007 := by norm_num [sT]
  rw [hs1] at e1 ⊢
  rw [hsT] at e2 ⊢
  have hcast : ((blkUp (T + 1) * blkUp W * (hs3 + 1) : ℕ) : ℝ) = (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * 12 := by
    rw [hs3_val]
    push_cast
    ring
  rw [hcast]
  have k1 : (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * 12 * (alQ : ℝ) ≤ 804 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) := by
    nlinarith [c1_le]
  have k2 : (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * 12 * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) *
      Real.exp (lam * (67 + 2 * 1 / 35)) ≤ 5.11e6 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) := by
    have := c2_le
    nlinarith
  have := mul_le_mul_of_nonneg_right k1 e1.le
  have := mul_le_mul_of_nonneg_right k2 e2.le
  linarith

/-! ## Cube codes: the ML failure probability tends to 0 -/

theorem blkUp_le (m : ℕ) : blkUp m ≤ m / 35 + 6 := by
  have h1 := Nat.lt_div_mul_add (a := m) (b := 35) (by norm_num)
  have h2 : (m + 34) / 35 < m / 35 + 2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), add_mul]
    omega
  unfold blkUp
  omega

/-- `(n + c)^2 e^{-s n} → 0` along `ℕ` for `s > 0`. -/
theorem tendsto_sq_mul_exp_neg {s : ℝ} (c : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ((n : ℝ) + c) ^ 2 * Real.exp (-(s * n))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => s * (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop hs
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
  have h3 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1
  have h4 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h5 := ((h2.const_mul (1 / s ^ 2)).add (h3.const_mul (2 * c / s))).add (h4.const_mul (c ^ 2))
  simp only [mul_zero, add_zero] at h5
  refine h5.congr fun n => ?_
  simp only [Function.comp, pow_one]
  field_simp
  ring

theorem pML3_nonneg (T w h : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ pML3 T w h q := by
  unfold pML3 pML pFail
  refine Finset.sum_nonneg fun e _ => ?_
  split_ifs
  · exact le_rfl
  · exact bernProd_nonneg hq0 hq1 e

/-- **Threshold for the phenomenological model**: under the hypotheses of `d1B_lean`, for every `q ∈ [0, 0.02]` the
ML failure probability of the cube code (`T + 1 = W = H = n`) tends to `0` as `n → ∞`. By monotonicity in the size
the same holds for every code with `T + 1 ≤ H` and `W ≤ H`. -/
theorem pML3_cube_tendsto_zero (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3)
    (hstat : (sp.toFam3 hV6).Hstat3 0.02 eps) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.02) :
    Tendsto (fun n : ℕ => pML3 (n - 1) (n - 1) (n - 1) q) atTop (𝓝 0) := by
  have hny : Tendsto (fun n : ℕ => n / 35) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  have t1 := ((tendsto_sq_mul_exp_neg 6 (show (0 : ℝ) < 0.1008 by norm_num)).comp hny).const_mul
    (804 * Real.exp (0.1008 * 47))
  have t2 := ((tendsto_sq_mul_exp_neg 6 (show (0 : ℝ) < 0.007 by norm_num)).comp hny).const_mul
    (5.11e6 * Real.exp (0.007 * 47))
  have hup := t1.add t2
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => pML3_nonneg _ _ _ hq0 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop (5 * 35)] with n hn
  have hb := d1B_num sp hV6 hcov hstat hq (T := n - 1) (W := n) (H := n) (by omega) hn
  rw [show n - 1 + 1 = n by omega] at hb
  refine hb.trans ?_
  simp only [Function.comp]
  have hb1 : (blkUp n : ℝ) ≤ ((n / 35 : ℕ) : ℝ) + 6 := by exact_mod_cast blkUp_le n
  have hb0 : (0 : ℝ) ≤ blkUp n := Nat.cast_nonneg _
  have key : ∀ (C s : ℝ), 0 ≤ C →
      C * (blkUp n : ℝ) * (blkUp n : ℝ) * Real.exp (-s * (((n / 35 : ℕ) : ℝ) - 47)) ≤
        C * Real.exp (s * 47) * ((((n / 35 : ℕ) : ℝ) + 6) ^ 2 * Real.exp (-(s * ((n / 35 : ℕ) : ℝ)))) := by
    intro C s hC
    have he : Real.exp (-s * (((n / 35 : ℕ) : ℝ) - 47)) =
        Real.exp (s * 47) * Real.exp (-(s * ((n / 35 : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have hsq : (blkUp n : ℝ) * (blkUp n : ℝ) ≤ (((n / 35 : ℕ) : ℝ) + 6) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hb1 hb1 hb0 (by positivity)
    have e1 := Real.exp_pos (s * 47)
    have e2 := Real.exp_pos (-(s * ((n / 35 : ℕ) : ℝ)))
    rw [he]
    calc C * (blkUp n : ℝ) * (blkUp n : ℝ) * (Real.exp (s * 47) * Real.exp (-(s * ((n / 35 : ℕ) : ℝ))))
        = (C * Real.exp (s * 47) * Real.exp (-(s * ((n / 35 : ℕ) : ℝ)))) * ((blkUp n : ℝ) * (blkUp n : ℝ)) := by
          ring
      _ ≤ (C * Real.exp (s * 47) * Real.exp (-(s * ((n / 35 : ℕ) : ℝ)))) * (((n / 35 : ℕ) : ℝ) + 6) ^ 2 := by
          gcongr
      _ = C * Real.exp (s * 47) * ((((n / 35 : ℕ) : ℝ) + 6) ^ 2 * Real.exp (-(s * ((n / 35 : ℕ) : ℝ)))) := by
          ring
  have k1 := key 804 0.1008 (by norm_num)
  have k2 := key 5.11e6 0.007 (by norm_num)
  linarith

end QECD1
