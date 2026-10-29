import QECML.TwoD.HeadlineCert

/-!
# The threshold for planar codes whose width grows subexponentially in the distance

`theoremB_a12_main` bounds the ML failure probability of the planar code with `W` columns and `H` rows for every
`W ≥ 1` and `H ≥ 32 L`; `threshold_a12_main` takes the limit along square codes. This module takes the limit along
every width that grows subexponentially (in particular polynomially) in `H`, with an explicit exponential rate, and
gives the certified form under one acceptance event.

* `SubExp f`: `f n e^{-c n} → 0` for every `c > 0` (indexing by `H` or by the distance `H + 1` gives the same
  notion). `subExp_of_log`: if `f ≥ 1` eventually and `log f(n) / n → 0`, then `SubExp f`. `subExp_of_le_poly`:
  a sequence bounded by a polynomial, `f n ≤ a n^k + b`, is `SubExp`. `SubExp.of_le`: eventual domination.
* `planar_term_le`: one term `C n_x e^{-s (n_y - 31)}` of the bound of Theorem B is at most
  `C e^{32 s} · ((W + L + 5) e^{-c H}) · e^{-(s/L - c) H}`.
* `pMLPlanar_tendsto_zero_of_concl`, `pMLPlanar_exp_decay_of_concl`: given the conclusion of Theorem B
  (`TheoremBConcl L`, `L ≥ 1`), for `W : ℕ → ℕ` with `W ≥ 1` and `SubExp W`, at every `q ∈ [0, 0.100]` the ML failure
  probability tends to `0`, and eventually it is at most `e^{-H/(100 L)}` (`e^{-H/28000}` for `L = 280`).
* `pMLPlanar_tendsto_zero_subexp`, `pMLPlanar_exp_decay_subexp`, `pMLPlanar_tendsto_zero_poly`: the same from the
  hypotheses of `theoremB_a12_main` (V6, `Hcov`, `R = L - 1`, `L ≥ 2`, `Hstat`); the last one for widths bounded by
  a polynomial in `H`.
* `threshold_a12_general_certified`: the certified form, as `theoremB_certified`: both conclusions for all such
  `W`, or the certificate accepts with probability at most `1e-9`.
* `ThresholdConcl`, `threshold_a12_general_familywise`: for two registered stage-1 programs, the probability that some
  certificate accepts while the threshold conclusion fails for its program is at most `2e-9`.
-/

open Filter Topology Finset Classical

namespace QECML

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

/-- Eventual domination by a subexponential sequence is subexponential. -/
theorem SubExp.of_le {f g : ℕ → ℕ} (hg : SubExp g) (h : ∀ᶠ n in atTop, f n ≤ g n) : SubExp f := by
  intro c hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hg c hc)
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [h] with n hn
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.exp_pos _).le

/-- Polynomial growth is subexponential: `f n ≤ a n^k + b` for all `n` gives `SubExp f`. -/
theorem subExp_of_le_poly {f : ℕ → ℕ} (a b k : ℕ) (hf : ∀ n, f n ≤ a * n ^ k + b) : SubExp f := by
  intro c hc
  have hck : (0 : ℝ) < c ^ k := pow_pos hc k
  have h1 : Tendsto (fun n : ℕ => (c * n) ^ k * Real.exp (-(c * n))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h2 := (h1.const_mul ((a : ℝ) / c ^ k)).add ((tendsto_exp_neg_mul_nat hc).const_mul (b : ℝ))
  simp only [mul_zero, add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => by positivity) (fun n => ?_)
  have hfn : (f n : ℝ) ≤ a * (n : ℝ) ^ k + b := by exact_mod_cast hf n
  have he := Real.exp_pos (-(c * n))
  calc (f n : ℝ) * Real.exp (-(c * n)) ≤ (a * (n : ℝ) ^ k + b) * Real.exp (-(c * n)) :=
        mul_le_mul_of_nonneg_right hfn he.le
    _ = (a : ℝ) / c ^ k * ((c * n) ^ k * Real.exp (-(c * n))) + b * Real.exp (-(c * n)) := by
        rw [mul_pow]
        field_simp

theorem subExp_add {f : ℕ → ℕ} (hf : SubExp f) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((f n : ℝ) + a) * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have h := (hf c hc).add ((tendsto_exp_neg_mul_nat hc).const_mul a)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  ring

/-- One term of the bound of Theorem B, for the planar code with `W` columns and `H` rows and block side `L ≥ 1`. -/
theorem planar_term_le (C s c : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s) {L : ℕ} (hL : 1 ≤ L) (W H : ℕ) :
    C * (nxOf L W : ℝ) * Real.exp (-s * ((nyOf L H : ℝ) - 31)) ≤
      C * Real.exp (32 * s) * (((W : ℝ) + ((L : ℝ) + 5)) * Real.exp (-(c * H))) *
        Real.exp (-((s * (1 / (L : ℝ)) - c) * H)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hnx : (nxOf L W : ℝ) ≤ (W : ℝ) + ((L : ℝ) + 5) := by
    have h1 : (W + L - 1) / L ≤ W + L - 1 := Nat.div_le_self _ _
    have h2 : nxOf L W ≤ W + L + 5 := by
      simp only [nxOf]
      exact max_le (by omega) (by omega)
    have h3 : ((nxOf L W : ℕ) : ℝ) ≤ ((W + L + 5 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hny : (H : ℝ) * (1 / (L : ℝ)) - 1 ≤ (nyOf L H : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := H) (b := L) (by omega)
    have h1' : (H : ℝ) < ((H / L : ℕ) : ℝ) * L + L := by exact_mod_cast h1
    simp only [nyOf]
    rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hLpos]
    nlinarith
  have he : Real.exp (-s * ((nyOf L H : ℝ) - 31)) ≤
      Real.exp (32 * s) * Real.exp (-(c * H)) * Real.exp (-((s * (1 / (L : ℝ)) - c) * H)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hny hs
    nlinarith
  have hnx0 : (0 : ℝ) ≤ nxOf L W := Nat.cast_nonneg _
  calc C * (nxOf L W : ℝ) * Real.exp (-s * ((nyOf L H : ℝ) - 31))
      ≤ C * ((W : ℝ) + ((L : ℝ) + 5)) * (Real.exp (32 * s) * Real.exp (-(c * H)) *
          Real.exp (-((s * (1 / (L : ℝ)) - c) * H))) := by
        gcongr
    _ = _ := by ring

/-- **The threshold for subexponentially growing widths**, given the conclusion of Theorem B for block side
`L ≥ 1`: for `W : ℕ → ℕ` with `W ≥ 1` and `SubExp W`, at every `q ∈ [0, 0.100]` the ML failure probability of the
planar code with `W H` columns and `H` rows tends to `0`. -/
theorem pMLPlanar_tendsto_zero_of_concl {L : ℕ} (hL : 1 ≤ L) (hB : TheoremBConcl L) {W : ℕ → ℕ}
    (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (W H - 1) (H - 1) q) atTop (𝓝 0) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hu0 : (0 : ℝ) < 1 / (L : ℝ) := one_div_pos.2 hL0
  have hc : (0 : ℝ) < 1 / (L : ℝ) / 200 := by positivity
  have tW := subExp_add hWs ((L : ℝ) + 5) hc
  have hup := (tW.const_mul (4.22e2 * Real.exp (32 * 0.2155))).add
    (tW.const_mul (2e4 * Real.exp (32 * 0.02)))
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun H => pMLPlanar_nonneg _ _ hq0 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop (32 * L)] with H hH
  have hb := hB q hq (W H) H (hW1 H) hH
  have k1 := planar_term_le 4.22e2 0.2155 (1 / (L : ℝ) / 200) (by norm_num) (by norm_num) hL (W H) H
  have k2 := planar_term_le 2e4 0.02 (1 / (L : ℝ) / 200) (by norm_num) (by norm_num) hL (W H) H
  have hHn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have huH : (0 : ℝ) ≤ 1 / (L : ℝ) * H := mul_nonneg hu0.le hHn
  have hx0 : (0 : ℝ) ≤ ((W H : ℝ) + ((L : ℝ) + 5)) * Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ))) := by positivity
  have e1 : Real.exp (-((0.2155 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have e2 : Real.exp (-((0.02 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have m1 := mul_le_mul_of_nonneg_left e1
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 4.22e2 * Real.exp (32 * 0.2155)) hx0)
  have m2 := mul_le_mul_of_nonneg_left e2
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2e4 * Real.exp (32 * 0.02)) hx0)
  simp only [mul_one] at m1 m2
  linarith

/-- **Exponential decay for subexponentially growing widths**, given the conclusion of Theorem B for block side
`L ≥ 1`: under the hypotheses of `pMLPlanar_tendsto_zero_of_concl`, eventually `P_ML ≤ e^{-H/(100 L)}`. -/
theorem pMLPlanar_exp_decay_of_concl {L : ℕ} (hL : 1 ≤ L) (hB : TheoremBConcl L) {W : ℕ → ℕ}
    (hW1 : ∀ H, 1 ≤ W H) (hWs : SubExp W) {q : ℝ} (hq : q ≤ 0.100) :
    ∀ᶠ H in atTop, pMLPlanar (W H - 1) (H - 1) q ≤ Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hu0 : (0 : ℝ) < 1 / (L : ℝ) := one_div_pos.2 hL0
  have hc : (0 : ℝ) < 1 / (L : ℝ) / 200 := by positivity
  set K : ℝ := 4.22e2 * Real.exp (32 * 0.2155) + 2e4 * Real.exp (32 * 0.02) with hK
  have hK0 : 0 ≤ K := by positivity
  have tW := (subExp_add hWs ((L : ℝ) + 5) hc).eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have tK0 := (tendsto_exp_neg_mul_nat hc).const_mul K
  rw [mul_zero] at tK0
  have tK := tK0.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [tW, tK, eventually_ge_atTop (32 * L)] with H hx hk hH
  have hb := hB q hq (W H) H (hW1 H) hH
  have k1 := planar_term_le 4.22e2 0.2155 (1 / (L : ℝ) / 200) (by norm_num) (by norm_num) hL (W H) H
  have k2 := planar_term_le 2e4 0.02 (1 / (L : ℝ) / 200) (by norm_num) (by norm_num) hL (W H) H
  have hHn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have huH : (0 : ℝ) ≤ 1 / (L : ℝ) * H := mul_nonneg hu0.le hHn
  have hx0 : (0 : ℝ) ≤ ((W H : ℝ) + ((L : ℝ) + 5)) * Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ))) := by positivity
  -- both exponential factors are at most e^{-(3/200) H / L}
  have e1 : Real.exp (-((0.2155 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤
      Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-((0.02 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤
      Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have c1 : (0 : ℝ) ≤ 4.22e2 * Real.exp (32 * 0.2155) := by positivity
  have c2 : (0 : ℝ) ≤ 2e4 * Real.exp (32 * 0.02) := by positivity
  have m1 : 4.22e2 * Real.exp (32 * 0.2155) *
      (((W H : ℝ) + ((L : ℝ) + 5)) * Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ)))) *
        Real.exp (-((0.2155 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤
      4.22e2 * Real.exp (32 * 0.2155) * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) := by
    calc _ ≤ 4.22e2 * Real.exp (32 * 0.2155) * 1 * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) := by
          gcongr
      _ = _ := by ring
  have m2 : 2e4 * Real.exp (32 * 0.02) *
      (((W H : ℝ) + ((L : ℝ) + 5)) * Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ)))) *
        Real.exp (-((0.02 * (1 / (L : ℝ)) - 1 / (L : ℝ) / 200) * (H : ℝ))) ≤
      2e4 * Real.exp (32 * 0.02) * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) := by
    calc _ ≤ 2e4 * Real.exp (32 * 0.02) * 1 * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) := by
          gcongr
      _ = _ := by ring
  -- K e^{-(3/200) H/L} = (K e^{-(1/200) H/L}) e^{-H/(100 L)} ≤ e^{-H/(100 L)}
  have hsplit : Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) =
      Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ))) * Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have E1 := Real.exp_pos (-(1 / (100 * (L : ℝ)) * (H : ℝ)))
  have hfin : K * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) ≤
      Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ))) := by
    rw [hsplit, ← mul_assoc]
    calc K * Real.exp (-(1 / (L : ℝ) / 200 * (H : ℝ))) * Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ)))
        ≤ 1 * Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ))) := mul_le_mul_of_nonneg_right hk E1.le
      _ = _ := one_mul _
  have hKe : K * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) =
      4.22e2 * Real.exp (32 * 0.2155) * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) +
        2e4 * Real.exp (32 * 0.02) * Real.exp (-(3 / 200 * (1 / (L : ℝ)) * (H : ℝ))) := by
    rw [hK]
    ring
  linarith

/-- **The threshold for subexponentially growing widths**, from the hypotheses of `theoremB_a12_main`. -/
theorem pMLPlanar_tendsto_zero_subexp (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4) {W : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H)
    (hWs : SubExp W) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (W H - 1) (H - 1) q) atTop (𝓝 0) :=
  pMLPlanar_tendsto_zero_of_concl (by omega)
    (fun _q hq _W _H hW hH => theoremB_a12_main sp hV6 hR hL2 hcov hstat hq hW hH) hW1 hWs hq0 hq

/-- **Exponential decay for subexponentially growing widths**, from the hypotheses of `theoremB_a12_main`:
eventually `P_ML ≤ e^{-H/(100 L)}`. -/
theorem pMLPlanar_exp_decay_subexp (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4) {W : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H)
    (hWs : SubExp W) {q : ℝ} (hq : q ≤ 0.100) :
    ∀ᶠ H in atTop, pMLPlanar (W H - 1) (H - 1) q ≤ Real.exp (-(1 / (100 * (sp.L : ℝ)) * (H : ℝ))) :=
  pMLPlanar_exp_decay_of_concl (by omega)
    (fun _q hq _W _H hW hH => theoremB_a12_main sp hV6 hR hL2 hcov hstat hq hW hH) hW1 hWs hq

/-- **The threshold for widths bounded by a polynomial**, from the hypotheses of `theoremB_a12_main`: if
`1 ≤ W H ≤ a H^k + b` for all `H`, the ML failure probability tends to `0` at every `q ∈ [0, 0.100]`. -/
theorem pMLPlanar_tendsto_zero_poly (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4) {W : ℕ → ℕ} (hW1 : ∀ H, 1 ≤ W H)
    (a b k : ℕ) (hWp : ∀ H, W H ≤ a * H ^ k + b) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.100) :
    Tendsto (fun H : ℕ => pMLPlanar (W H - 1) (H - 1) q) atTop (𝓝 0) :=
  pMLPlanar_tendsto_zero_subexp sp hV6 hR hL2 hcov hstat hW1 (subExp_of_le_poly a b k hWp) hq0 hq

/-- **The threshold, certified, for subexponentially growing widths.** For the registered stage-1 program under
V6 and `Hcov` (with `R = L - 1`, `L ≥ 2`), and the binomial model of the certificate's counts (design A) with the
true reference rates: either, for all `W : ℕ → ℕ` with `W ≥ 1`, `SubExp W` and every `q ∈ [0, 0.100]`, the ML
failure probability tends to `0` and is eventually at most `e^{-H/(100 L)}`, or the certificate accepts with
probability at most `1e-9`. -/
theorem threshold_a12_general_certified (sp : S3Prog) (hV6 : sp.V6) (hR : sp.R = sp.L - 1) (hL2 : 2 ≤ sp.L)
    (hcov : (sp.toFam hV6).Hcov) {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : Fin 5 → Ω → ℕ)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp hV6 t ^ j * (1 - refRate sp hV6 t) ^ (120000 - j)) :
    (∀ W : ℕ → ℕ, (∀ H, 1 ≤ W H) → SubExp W → ∀ q : ℝ, 0 ≤ q → q ≤ 0.100 →
      Tendsto (fun H : ℕ => pMLPlanar (W H - 1) (H - 1) q) atTop (𝓝 0) ∧
        ∀ᶠ H in atTop, pMLPlanar (W H - 1) (H - 1) q ≤ Real.exp (-(1 / (100 * (sp.L : ℝ)) * (H : ℝ)))) ∨
      (∑ ω, if (∀ t, K t ω ≤ 18) then P ω else 0) ≤ 1e-9 :=
  (theoremB_certified sp hV6 hR hL2 hcov P hP K hlaw).imp
    (fun hB _W hW1 hWs _q hq0 hq =>
      ⟨pMLPlanar_tendsto_zero_of_concl (by omega) hB hW1 hWs hq0 hq,
        pMLPlanar_exp_decay_of_concl (by omega) hB hW1 hWs hq⟩) id

/-- The threshold conclusion for block side `L`: for every `W : ℕ → ℕ` with `W ≥ 1` and `SubExp W` and every
`q ∈ [0, 0.100]`, the ML failure probability tends to `0` and is eventually at most `e^{-H/(100 L)}`. -/
def ThresholdConcl (L : ℕ) : Prop :=
  ∀ W : ℕ → ℕ, (∀ H, 1 ≤ W H) → SubExp W → ∀ q : ℝ, 0 ≤ q → q ≤ 0.100 →
    Tendsto (fun H : ℕ => pMLPlanar (W H - 1) (H - 1) q) atTop (𝓝 0) ∧
      ∀ᶠ H in atTop, pMLPlanar (W H - 1) (H - 1) q ≤ Real.exp (-(1 / (100 * (L : ℝ)) * (H : ℝ)))

theorem thresholdConcl_of_theoremBConcl {L : ℕ} (hL : 1 ≤ L) (hB : TheoremBConcl L) : ThresholdConcl L :=
  fun _W hW1 hWs _q hq0 hq =>
    ⟨pMLPlanar_tendsto_zero_of_concl hL hB hW1 hWs hq0 hq, pMLPlanar_exp_decay_of_concl hL hB hW1 hWs hq⟩

/-- **Two certificates, family-wise, for the threshold.** For two registered stage-1 programs and a joint model of
both certificates' counts (binomial with the true reference rates of each program), the probability that some
certificate accepts while the threshold conclusion fails for its program is at most `2e-9`. -/
theorem threshold_a12_general_familywise (sp1 sp2 : S3Prog) (h1V6 : sp1.V6) (h2V6 : sp2.V6)
    (h1R : sp1.R = sp1.L - 1) (h2R : sp2.R = sp2.L - 1) (h1L : 2 ≤ sp1.L) (h2L : 2 ≤ sp2.L)
    (h1cov : (sp1.toFam h1V6).Hcov) (h2cov : (sp2.toFam h2V6).Hcov)
    {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K1 K2 : Fin 5 → Ω → ℕ)
    (h1law : ∀ t j, (∑ ω, if K1 t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp1 h1V6 t ^ j * (1 - refRate sp1 h1V6 t) ^ (120000 - j))
    (h2law : ∀ t j, (∑ ω, if K2 t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * refRate sp2 h2V6 t ^ j * (1 - refRate sp2 h2V6 t) ^ (120000 - j)) :
    (∑ ω, if ((∀ t, K1 t ω ≤ 18) ∧ ¬ ThresholdConcl sp1.L) ∨ ((∀ t, K2 t ω ≤ 18) ∧ ¬ ThresholdConcl sp2.L)
      then P ω else 0) ≤ 2e-9 := by
  have i1 : ¬ ThresholdConcl sp1.L → ¬ TheoremBConcl sp1.L := fun h hB =>
    h (thresholdConcl_of_theoremBConcl (by omega) hB)
  have i2 : ¬ ThresholdConcl sp2.L → ¬ TheoremBConcl sp2.L := fun h hB =>
    h (thresholdConcl_of_theoremBConcl (by omega) hB)
  refine le_trans (Finset.sum_le_sum fun ω _ => ?_)
    (theoremB_certified_familywise sp1 sp2 h1V6 h2V6 h1R h2R h1L h2L h1cov h2cov P hP K1 K2 h1law h2law)
  by_cases ha : ((∀ t, K1 t ω ≤ 18) ∧ ¬ ThresholdConcl sp1.L) ∨ ((∀ t, K2 t ω ≤ 18) ∧ ¬ ThresholdConcl sp2.L)
  · have hb : ((∀ t, K1 t ω ≤ 18) ∧ ¬ TheoremBConcl sp1.L) ∨ ((∀ t, K2 t ω ≤ 18) ∧ ¬ TheoremBConcl sp2.L) :=
      ha.imp (fun h => ⟨h.1, i1 h.2⟩) (fun h => ⟨h.1, i2 h.2⟩)
    rw [ite_eq_left ha, ite_eq_left hb]
  · rw [ite_eq_right ha]
    split_ifs
    · exact hP ω
    · exact le_rfl

end QECML
