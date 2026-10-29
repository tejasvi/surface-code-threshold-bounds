import QECD1.CertD1

/-!
# The threshold for codes whose width and number of rounds grow subexponentially

The threshold claim: `P_ML → 0` exponentially in `d` whenever `W` and `T` grow subexponentially in `d`. The cube-code
form is `pML3_cube_tendsto_zero` / `threshold_d1_certified`; this module proves the general form, for the code with
`T + 1` layers, `W` columns and `H` rows (`d = H + 1`).

* `SubExp f`: `f n e^{-c n} → 0` for every `c > 0` (indexing by `H` or by `d = H + 1` gives the same notion).
  `subExp_of_log`: if `f ≥ 1` eventually and `log f(n) / n → 0`, then `SubExp f`.
* `bound_term_le`: one term `C n_t n_x e^{-s (n_y - 47)}` of the ML bound is at most
  `C e^{48 s} · ((T + 7) e^{-c H}) · ((W + 6) e^{-c H}) · e^{-(s/35 - 2c) H}`.
* `pML3_tendsto_zero_of_concl`, `pML3_exp_decay_of_concl`: given the conclusion of the ML bound (`D1BConcl`), for
  `W, T : ℕ → ℕ` with `W ≥ 1`, `SubExp W` and `SubExp T`, at every `q ∈ [0, 0.02]` the ML failure probability tends
  to `0`, and eventually it is at most `e^{-H/28000}`.
* `pML3_tendsto_zero_subexp`, `pML3_exp_decay_subexp`: the same from the hypotheses of `d1B_num` (V6, `Hcov3`,
  `Hstat3`).
* `threshold_d1_general_certified`: the certified form, as `threshold_d1_certified`: both conclusions for all such
  `W, T`, or the certificate accepts with probability at most `1e-9`.
-/

open Filter Topology

namespace QECD1

/-- Subexponential growth: `f n e^{-c n} → 0` for every `c > 0`. -/
def SubExp (f : ℕ → ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => (f n : ℝ) * Real.exp (-(c * n))) atTop (𝓝 0)

theorem tendsto_exp_neg_mul_nat {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-(c * n))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)

/-- A sequence `f ≥ 1` with `log f(n) / n → 0` grows subexponentially. -/
theorem subExp_of_log {f : ℕ → ℕ} (h1 : ∀ᶠ n in atTop, 1 ≤ f n)
    (hlog : Tendsto (fun n : ℕ => Real.log (f n) / n) atTop (𝓝 0)) : SubExp f := by
  intro c hc
  have hlt := hlog.eventually_lt_const (half_pos hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_exp_neg_mul_nat (half_pos hc))
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [hlt, h1, eventually_gt_atTop 0] with n hn hf hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hfpos : (0 : ℝ) < f n := Nat.cast_pos.2 (Nat.lt_of_lt_of_le Nat.zero_lt_one hf)
  have hl : Real.log (f n) < c / 2 * n := (div_lt_iff₀ hn0').1 hn
  have hfe : (f n : ℝ) ≤ Real.exp (c / 2 * n) := by
    rw [← Real.exp_log hfpos]
    exact Real.exp_le_exp.2 hl.le
  calc (f n : ℝ) * Real.exp (-(c * n)) ≤ Real.exp (c / 2 * n) * Real.exp (-(c * n)) :=
        mul_le_mul_of_nonneg_right hfe (Real.exp_pos _).le
    _ = Real.exp (-(c / 2 * n)) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem subExp_add {f : ℕ → ℕ} (hf : SubExp f) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((f n : ℝ) + a) * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have h := (hf c hc).add ((tendsto_exp_neg_mul_nat hc).const_mul a)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  ring

/-- One term of the ML bound, for the code with `T + 1` layers, `W` columns and `H` rows. -/
theorem bound_term_le (C s c : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s) (T W H : ℕ) :
    C * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-s * (((H / 35 : ℕ) : ℝ) - 47)) ≤
      C * Real.exp (48 * s) * ((((T : ℝ) + 7) * Real.exp (-(c * H))) * (((W : ℝ) + 6) * Real.exp (-(c * H)))) *
        Real.exp (-((s / 35 - 2 * c) * H)) := by
  have hT : (blkUp (T + 1) : ℝ) ≤ (T : ℝ) + 7 := by
    have h1 := blkUp_le (T + 1)
    have h2 : (T + 1) / 35 ≤ T + 1 := Nat.div_le_self _ _
    exact_mod_cast (by omega : blkUp (T + 1) ≤ T + 7)
  have hW : (blkUp W : ℝ) ≤ (W : ℝ) + 6 := by
    have h1 := blkUp_le W
    have h2 : W / 35 ≤ W := Nat.div_le_self _ _
    exact_mod_cast (by omega : blkUp W ≤ W + 6)
  have hH : (H : ℝ) / 35 - 1 ≤ ((H / 35 : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := H) (b := 35) (by norm_num)
    have h1' : (H : ℝ) < ((H / 35 : ℕ) : ℝ) * 35 + 35 := by exact_mod_cast h1
    linarith
  have he : Real.exp (-s * (((H / 35 : ℕ) : ℝ) - 47)) ≤
      Real.exp (48 * s) * (Real.exp (-(c * H)) * Real.exp (-(c * H))) * Real.exp (-((s / 35 - 2 * c) * H)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hH hs
    nlinarith
  have hbT0 : (0 : ℝ) ≤ blkUp (T + 1) := Nat.cast_nonneg _
  have hbW0 : (0 : ℝ) ≤ blkUp W := Nat.cast_nonneg _
  have hE0 := Real.exp_pos (-s * (((H / 35 : ℕ) : ℝ) - 47))
  calc C * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-s * (((H / 35 : ℕ) : ℝ) - 47))
      ≤ C * ((T : ℝ) + 7) * ((W : ℝ) + 6) *
          (Real.exp (48 * s) * (Real.exp (-(c * H)) * Real.exp (-(c * H))) *
            Real.exp (-((s / 35 - 2 * c) * H))) := by
        gcongr
    _ = _ := by ring

/-- The rate used in the decay bounds: `c = 1/56000`, so that `s/35 - 2c ≥ 3/28000` for `s ≥ 0.007`. -/
theorem rate_facts : (0 : ℝ) < 1 / 56000 ∧ (3 / 28000 : ℝ) ≤ 0.1008 / 35 - 2 * (1 / 56000) ∧
    (3 / 28000 : ℝ) ≤ 0.007 / 35 - 2 * (1 / 56000) := by
  norm_num

/-- **The threshold for subexponentially growing codes**, given the conclusion of the ML bound: for `W, T : ℕ → ℕ`
with `W ≥ 1`, `SubExp W` and `SubExp T`, at every `q ∈ [0, 0.02]` the ML failure probability of the code with
`T H + 1` layers, `W H` columns and `H` rows tends to `0`. -/
theorem pML3_tendsto_zero_of_concl (hB : D1BConcl) {W T : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W)
    (hTs : SubExp T) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.02) :
    Tendsto (fun H : ℕ => pML3 (T H) (W H - 1) (H - 1) q) atTop (𝓝 0) := by
  obtain ⟨hc, h1, h2⟩ := rate_facts
  have tT := subExp_add hTs 7 hc
  have tW := subExp_add hWs 6 hc
  have hup := ((tT.mul tW).const_mul (804 * Real.exp (48 * 0.1008))).add
    ((tT.mul tW).const_mul (5.11e6 * Real.exp (48 * 0.007)))
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun H => pML3_nonneg _ _ _ hq0 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop (5 * 35)] with H hH
  have hb := hB q hq (T H) (W H) H (hW1 H) hH
  have k1 := bound_term_le 804 0.1008 (1 / 56000) (by norm_num) (by norm_num) (T H) (W H) H
  have k2 := bound_term_le 5.11e6 0.007 (1 / 56000) (by norm_num) (by norm_num) (T H) (W H) H
  have hx0 : (0 : ℝ) ≤ ((T H : ℝ) + 7) * Real.exp (-(1 / 56000 * (H : ℝ))) := by positivity
  have hy0 : (0 : ℝ) ≤ ((W H : ℝ) + 6) * Real.exp (-(1 / 56000 * (H : ℝ))) := by positivity
  have e1 : Real.exp (-((0.1008 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have e2 : Real.exp (-((0.007 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have hxy := mul_nonneg hx0 hy0
  have m1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg (by positivity : (0 : ℝ) ≤ 804 * Real.exp (48 * 0.1008)) hxy)
  have m2 := mul_le_mul_of_nonneg_left e2
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 5.11e6 * Real.exp (48 * 0.007)) hxy)
  simp only [mul_one] at m1 m2
  linarith

/-- **Exponential decay for subexponentially growing codes**, given the conclusion of the ML bound: under the
hypotheses of `pML3_tendsto_zero_of_concl`, eventually `P_ML ≤ e^{-H/28000}`. -/
theorem pML3_exp_decay_of_concl (hB : D1BConcl) {W T : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W)
    (hTs : SubExp T) {q : ℝ} (hq : q ≤ 0.02) :
    ∀ᶠ H in atTop, pML3 (T H) (W H - 1) (H - 1) q ≤ Real.exp (-(1 / 28000 * (H : ℝ))) := by
  obtain ⟨hc, h1, h2⟩ := rate_facts
  set K : ℝ := 804 * Real.exp (48 * 0.1008) + 5.11e6 * Real.exp (48 * 0.007) with hK
  have hK0 : 0 ≤ K := by positivity
  have tT := (subExp_add hTs 7 hc).eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have tW := (subExp_add hWs 6 hc).eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have tK0 := (tendsto_exp_neg_mul_nat (show (0 : ℝ) < 2 / 28000 by norm_num)).const_mul K
  rw [mul_zero] at tK0
  have tK := tK0.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [tT, tW, tK, eventually_ge_atTop (5 * 35)] with H hx hy hk hH
  have hb := hB q hq (T H) (W H) H (hW1 H) hH
  have k1 := bound_term_le 804 0.1008 (1 / 56000) (by norm_num) (by norm_num) (T H) (W H) H
  have k2 := bound_term_le 5.11e6 0.007 (1 / 56000) (by norm_num) (by norm_num) (T H) (W H) H
  have hHn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hx0 : (0 : ℝ) ≤ ((T H : ℝ) + 7) * Real.exp (-(1 / 56000 * (H : ℝ))) := by positivity
  have hy0 : (0 : ℝ) ≤ ((W H : ℝ) + 6) * Real.exp (-(1 / 56000 * (H : ℝ))) := by positivity
  have hxy : ((T H : ℝ) + 7) * Real.exp (-(1 / 56000 * (H : ℝ))) *
      (((W H : ℝ) + 6) * Real.exp (-(1 / 56000 * (H : ℝ)))) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hx hy hy0 zero_le_one
      _ = 1 := one_mul 1
  have hxy0 := mul_nonneg hx0 hy0
  -- both exponential factors are at most e^{-(3/28000) H}
  have e1 : Real.exp (-((0.1008 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤ Real.exp (-(3 / 28000 * (H : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-((0.007 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤ Real.exp (-(3 / 28000 * (H : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have E0 := Real.exp_pos (-(3 / 28000 * (H : ℝ)))
  have c1 : (0 : ℝ) ≤ 804 * Real.exp (48 * 0.1008) := by positivity
  have c2 : (0 : ℝ) ≤ 5.11e6 * Real.exp (48 * 0.007) := by positivity
  have m1 : 804 * Real.exp (48 * 0.1008) * (((T H : ℝ) + 7) * Real.exp (-(1 / 56000 * (H : ℝ))) *
      (((W H : ℝ) + 6) * Real.exp (-(1 / 56000 * (H : ℝ))))) *
        Real.exp (-((0.1008 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤
      804 * Real.exp (48 * 0.1008) * Real.exp (-(3 / 28000 * (H : ℝ))) := by
    calc _ ≤ 804 * Real.exp (48 * 0.1008) * 1 * Real.exp (-(3 / 28000 * (H : ℝ))) := by
          gcongr
      _ = _ := by ring
  have m2 : 5.11e6 * Real.exp (48 * 0.007) * (((T H : ℝ) + 7) * Real.exp (-(1 / 56000 * (H : ℝ))) *
      (((W H : ℝ) + 6) * Real.exp (-(1 / 56000 * (H : ℝ))))) *
        Real.exp (-((0.007 / 35 - 2 * (1 / 56000)) * (H : ℝ))) ≤
      5.11e6 * Real.exp (48 * 0.007) * Real.exp (-(3 / 28000 * (H : ℝ))) := by
    calc _ ≤ 5.11e6 * Real.exp (48 * 0.007) * 1 * Real.exp (-(3 / 28000 * (H : ℝ))) := by
          gcongr
      _ = _ := by ring
  -- K e^{-(3/28000) H} = (K e^{-(2/28000) H}) e^{-(1/28000) H} ≤ e^{-(1/28000) H}
  have hsplit : Real.exp (-(3 / 28000 * (H : ℝ))) =
      Real.exp (-(2 / 28000 * (H : ℝ))) * Real.exp (-(1 / 28000 * (H : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have E1 := Real.exp_pos (-(1 / 28000 * (H : ℝ)))
  have hfin : K * Real.exp (-(3 / 28000 * (H : ℝ))) ≤ Real.exp (-(1 / 28000 * (H : ℝ))) := by
    rw [hsplit, ← mul_assoc]
    calc K * Real.exp (-(2 / 28000 * (H : ℝ))) * Real.exp (-(1 / 28000 * (H : ℝ)))
        ≤ 1 * Real.exp (-(1 / 28000 * (H : ℝ))) := mul_le_mul_of_nonneg_right hk E1.le
      _ = _ := one_mul _
  have hKe : K * Real.exp (-(3 / 28000 * (H : ℝ))) =
      804 * Real.exp (48 * 0.1008) * Real.exp (-(3 / 28000 * (H : ℝ))) +
        5.11e6 * Real.exp (48 * 0.007) * Real.exp (-(3 / 28000 * (H : ℝ))) := by
    rw [hK]
    ring
  linarith

/-- **The threshold for subexponentially growing codes**, from the hypotheses of `d1B_num`. -/
theorem pML3_tendsto_zero_subexp (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3)
    (hstat : (sp.toFam3 hV6).Hstat3 0.02 eps) {W T : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W)
    (hTs : SubExp T) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.02) :
    Tendsto (fun H : ℕ => pML3 (T H) (W H - 1) (H - 1) q) atTop (𝓝 0) :=
  pML3_tendsto_zero_of_concl (fun _q hq _T _W _H hW hH => d1B_num sp hV6 hcov hstat hq hW hH) hW1 hWs hTs hq0 hq

/-- **Exponential decay for subexponentially growing codes**, from the hypotheses of `d1B_num`. -/
theorem pML3_exp_decay_subexp (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3)
    (hstat : (sp.toFam3 hV6).Hstat3 0.02 eps) {W T : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W)
    (hTs : SubExp T) {q : ℝ} (hq : q ≤ 0.02) :
    ∀ᶠ H in atTop, pML3 (T H) (W H - 1) (H - 1) q ≤ Real.exp (-(1 / 28000 * (H : ℝ))) :=
  pML3_exp_decay_of_concl (fun _q hq _T _W _H hW hH => d1B_num sp hV6 hcov hstat hq hW hH) hW1 hWs hTs hq

/-- **The threshold, certified, for subexponentially growing codes.** For the registered stage-1 program under V6
and `Hcov3`, and the binomial model of the certificate's counts with the true reference rates: either, for all
`W, T : ℕ → ℕ` with `W ≥ 1`, `SubExp W`, `SubExp T` and every `q ∈ [0, 0.02]`, the ML failure probability tends to
`0` and is eventually at most `e^{-H/28000}`, or the certificate accepts with probability at most `1e-9`. -/
theorem threshold_d1_general_certified (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3) {Ω : Type*}
    [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : Fin 5 × Fin 5 → Ω → ℕ)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 3000000 j : ℕ) : ℝ) * refRate3 sp hV6 t ^ j * (1 - refRate3 sp hV6 t) ^ (3000000 - j)) :
    (∀ W T : ℕ → ℕ, (∀ H, 1 ≤ W H) → SubExp W → SubExp T → ∀ q : ℝ, 0 ≤ q → q ≤ 0.02 →
      Tendsto (fun H : ℕ => pML3 (T H) (W H - 1) (H - 1) q) atTop (𝓝 0) ∧
        ∀ᶠ H in atTop, pML3 (T H) (W H - 1) (H - 1) q ≤ Real.exp (-(1 / 28000 * (H : ℝ)))) ∨
      (∑ ω, if (∀ t, K t ω ≤ 14) then P ω else 0) ≤ 1e-9 :=
  (d1B_certified sp hV6 hcov P hP K hlaw).imp
    (fun hB _W _T hW1 hWs hTs _q hq0 hq =>
      ⟨pML3_tendsto_zero_of_concl hB hW1 hWs hTs hq0 hq, pML3_exp_decay_of_concl hB hW1 hWs hTs hq⟩) id

end QECD1
