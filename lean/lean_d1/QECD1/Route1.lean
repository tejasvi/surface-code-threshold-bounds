import QECD1.Top

/-!
# The 3D T1 route factor at the y-tilt `s1 = 0.1008`

This is the numeric core of the T1 term in 3D, the analogue of the 2D `RouteNum` and `RouteCount.Wsum_le` (2D,
tilt 0.2155). T1 routes are words of the route grammar (`rToks`, `rNext`: `A` steps/links, `B` steps/leaves, `C`
links). Steps and links weigh `ε e^{s1 v_y}`, leaves `ε`, and every state has end weight 1.

* One-move bounds with rational exponentials (`exp_s1_mul_le`) and box factorization:
  * steps `Σ_{S0} ε e^{s1 v_y} ≤ u0 ≈ 0.08844`;
  * links `Σ_{S1} ε e^{s1 v_y} ≤ u1 ≈ 5.1545`;
  * leaves `ε |S0| = 0.077404`.
* `fix_ok`: `(α, β, γ) = (66.953, 11.6463, 61.0319)` satisfies the three fixed-point inequalities of the 2D proof
  `α ≥ 1 + u0 α + u1 β`, `β ≥ 1 + u0 α + l0 γ`, `γ ≥ 1 + u1 β` (kernel check).
* `route1_V_le`: route words from `A` weigh at most `α = 66.953` for every word length; `route1_words_le` gives the
  same for every finite set of allowed words.

At `s1 = 0.12` there is no fixed point. The T1 rate of the registered computation is 0.10087; here `s1` is the
paper's 0.1008. The geometric count (routes from the strip, `n_t n_x (h_s + 1) α e^{-s1 (n_y - H0)}`, the 2D
`routeCount_le`) is `t1_bound3_count` (T1Final3).
-/

namespace QECD1

open QECD1.Tab

noncomputable def s1 : ℝ := 63 / 625
def s1Up : ℚ := 110606 / 100000
def s1Inv : ℚ := 90412 / 100000

theorem exp_s1_le : Real.exp s1 ≤ (s1Up : ℝ) := by
  have h := Real.exp_bound (x := 63 / 625) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [s1Up, s1]
  linarith [h.1, h.2]

theorem exp_neg_s1_le : Real.exp (-s1) ≤ (s1Inv : ℝ) := by
  have h := Real.exp_bound (x := -(63 / 625)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [s1Inv, s1]
  linarith [h.1, h.2]

/-- The rational bound of `e^{s1 c}`. -/
def sy1 (c : ℤ) : ℚ := if 0 ≤ c then s1Up ^ c.natAbs else s1Inv ^ c.natAbs

theorem exp_s1_mul_le (c : ℤ) : Real.exp (s1 * c) ≤ (sy1 c : ℝ) := by
  unfold sy1
  split_ifs with hc
  · have hcast : (c : ℝ) = ((c.natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact (abs_of_nonneg (by exact_mod_cast hc)).symm
    rw [hcast, mul_comm, Real.exp_nat_mul]
    push_cast
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_s1_le _
  · have hcast : s1 * (c : ℝ) = ((c.natAbs : ℕ) : ℝ) * (-s1) := by
      have h0' : ((c.natAbs : ℕ) : ℝ) = -(c : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact abs_of_neg (by exact_mod_cast (not_le.1 hc))
      rw [h0']
      ring
    rw [hcast, Real.exp_nat_mul]
    push_cast
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_s1_le _

theorem sy1_nonneg (c : ℤ) : 0 ≤ sy1 c := by
  unfold sy1
  split_ifs
  · exact pow_nonneg (by norm_num [s1Up]) _
  · exact pow_nonneg (by norm_num [s1Inv]) _

/-- The 1D tilted sum. -/
def T1y (K : ℕ) : ℚ := ∑ c ∈ Finset.Icc (-(K : ℤ)) K, sy1 c

theorem sum_box_sy1 (K : ℕ) : ∑ v ∈ box K, (sy1 v.2.2 : ℝ) = ((2 * K + 1 : ℕ) : ℝ) ^ 2 * (T1y K : ℝ) := by
  have h := sum_box_prod (fun _ => (1 : ℝ)) (fun c => (sy1 c : ℝ)) K
  simp only [one_mul] at h
  rw [h]
  have hc : ∑ _a ∈ Finset.Icc (-(K : ℤ)) K, (1 : ℝ) = ((2 * K + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    have : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
    rw [this]
  rw [hc, T1y]
  push_cast
  ring

theorem S0_eq_sdiff : S0 = box 8 \ box 4 := by
  ext v
  simp only [S0, Finset.mem_filter, Finset.mem_sdiff, mem_box]
  omega

def u0Q : ℚ := epsQ * (17 ^ 2 * T1y 8 - 9 ^ 2 * T1y 4)
def u1Q : ℚ := epsQ * (49 ^ 2 * T1y 24 - 9 ^ 2 * T1y 4)
def l0Q : ℚ := epsQ * 4184
def alQ : ℚ := 66953 / 1000
def beQ : ℚ := 116463 / 10000
def gaQ : ℚ := 610319 / 10000

/-- **The fixed point** of the T1 transfer inequalities. -/
theorem fix_ok : 1 + u0Q * alQ + u1Q * beQ ≤ alQ ∧ 1 + u0Q * alQ + l0Q * gaQ ≤ beQ ∧ 1 + u1Q * beQ ≤ gaQ := by
  decide +kernel

/-- The T1 weight of a step or link offset: `ε e^{s1 v_y}`. -/
noncomputable def t1w (v : V3) : ℝ := eps * Real.exp (s1 * v.2.2)

theorem t1w_le (v : V3) : t1w v ≤ (epsQ : ℝ) * (sy1 v.2.2 : ℝ) := by
  unfold t1w
  rw [eps_eq]
  exact mul_le_mul_of_nonneg_left (exp_s1_mul_le _) (by norm_num [epsQ])

theorem shell_sum (K K' : ℕ) (hK : K' ≤ K) :
    ∑ v ∈ box K \ box K', (sy1 v.2.2 : ℝ) = ((2 * K + 1 : ℕ) : ℝ) ^ 2 * (T1y K : ℝ) -
      ((2 * K' + 1 : ℕ) : ℝ) ^ 2 * (T1y K' : ℝ) := by
  rw [Finset.sum_sdiff_eq_sub (box_mono hK), sum_box_sy1, sum_box_sy1]

theorem S0_sy1_sum : ∑ v ∈ S0, (sy1 v.2.2 : ℝ) =
    ((2 * 8 + 1 : ℕ) : ℝ) ^ 2 * (T1y 8 : ℝ) - ((2 * 4 + 1 : ℕ) : ℝ) ^ 2 * (T1y 4 : ℝ) := by
  have h := shell_sum 8 4 (by norm_num)
  rw [← S0_eq_sdiff] at h
  exact h

theorem S1off_sy1_sum : ∑ v ∈ S1off, (sy1 v.2.2 : ℝ) =
    ((2 * 24 + 1 : ℕ) : ℝ) ^ 2 * (T1y 24 : ℝ) - ((2 * 4 + 1 : ℕ) : ℝ) ^ 2 * (T1y 4 : ℝ) := by
  have h := shell_sum 24 4 (by norm_num)
  rw [← S1off_eq] at h
  exact h

theorem u0_dom : ∑ v ∈ S0, t1w v ≤ (u0Q : ℝ) := by
  have h1 : ∑ v ∈ S0, t1w v ≤ ∑ v ∈ S0, (epsQ : ℝ) * (sy1 v.2.2 : ℝ) := Finset.sum_le_sum fun v _ => t1w_le v
  have h2 : ∑ v ∈ S0, (epsQ : ℝ) * (sy1 v.2.2 : ℝ) = (u0Q : ℝ) := by
    rw [← Finset.mul_sum, S0_sy1_sum]
    unfold u0Q
    push_cast
    ring
  linarith

theorem u1_dom : ∑ v ∈ S1off, t1w v ≤ (u1Q : ℝ) := by
  have h1 : ∑ v ∈ S1off, t1w v ≤ ∑ v ∈ S1off, (epsQ : ℝ) * (sy1 v.2.2 : ℝ) :=
    Finset.sum_le_sum fun v _ => t1w_le v
  have h2 : ∑ v ∈ S1off, (epsQ : ℝ) * (sy1 v.2.2 : ℝ) = (u1Q : ℝ) := by
    rw [← Finset.mul_sum, S1off_sy1_sum]
    unfold u1Q
    push_cast
    ring
  linarith

/-- T1 token weights. -/
noncomputable def t1Tok : Tok → ℝ
  | .step v => t1w v
  | .leaf _ => eps
  | .link v => t1w v
  | .mark => 0

theorem t1Tok_nonneg (t : Tok) : 0 ≤ t1Tok t := by
  cases t with
  | step v => exact mul_nonneg eps_nonneg (Real.exp_pos _).le
  | leaf v => exact eps_nonneg
  | link v => exact mul_nonneg eps_nonneg (Real.exp_pos _).le
  | mark => exact le_refl 0

/-- The T1 route automaton (end weight 1 in every state). -/
noncomputable def route1 : WA ℕ Tok where
  toks := rToks
  next := rNext
  g _ := t1Tok
  e _ := 1

/-- The Bellman vector: `β` at `B` (0), `α` at `A` (1), `γ` at `C` (2). -/
noncomputable def r1B (q : ℕ) : ℝ := if q = 0 then (beQ : ℝ) else if q = 1 then (alQ : ℝ) else (gaQ : ℝ)

theorem route1_bellman (q : ℕ) (hq : q ≤ 2) :
    route1.e q + ∑ t ∈ route1.toks q, route1.g q t * r1B (route1.next q t) ≤ r1B q := by
  show 1 + ∑ t ∈ rToks q, t1Tok t * r1B (rNext q t) ≤ r1B q
  have ha : (0 : ℝ) ≤ alQ := by norm_num [alQ]
  have hb : (0 : ℝ) ≤ beQ := by norm_num [beQ]
  have hg : (0 : ℝ) ≤ gaQ := by norm_num [gaQ]
  obtain ⟨f1, f2, f3⟩ := fix_ok
  have F1 : (1 : ℝ) + (u0Q : ℝ) * alQ + (u1Q : ℝ) * beQ ≤ alQ := by exact_mod_cast f1
  have F2 : (1 : ℝ) + (u0Q : ℝ) * alQ + (l0Q : ℝ) * gaQ ≤ beQ := by exact_mod_cast f2
  have F3 : (1 : ℝ) + (u1Q : ℝ) * beQ ≤ gaQ := by exact_mod_cast f3
  have hstep : ∑ t ∈ S0.image Tok.step, t1Tok t * r1B (rNext q t) = (∑ v ∈ S0, t1w v) * alQ := by
    rw [Finset.sum_image step_inj, Finset.sum_mul]
    rfl
  have hlink : ∑ t ∈ S1off.image Tok.link, t1Tok t * r1B (rNext q t) = (∑ v ∈ S1off, t1w v) * beQ := by
    rw [Finset.sum_image link_inj, Finset.sum_mul]
    rfl
  have hleaf : ∑ t ∈ S0.image Tok.leaf, t1Tok t * r1B (rNext q t) = (∑ _v ∈ S0, eps) * gaQ := by
    rw [Finset.sum_image leaf_inj, Finset.sum_mul]
    rfl
  have hl0 : ∑ _v ∈ S0, eps = (l0Q : ℝ) := by
    rw [sum_eps_S0, eps_eq]
    unfold l0Q
    push_cast
    ring
  have h0 := mul_le_mul_of_nonneg_right u0_dom ha
  have h1 := mul_le_mul_of_nonneg_right u1_dom hb
  interval_cases q
  · rw [rToks, if_pos rfl, Finset.sum_union disj_step_leaf, hstep, hleaf, hl0]
    show _ ≤ (beQ : ℝ)
    linarith
  · rw [rToks, if_neg (by norm_num), if_pos rfl, Finset.sum_union disj_step_link, hstep, hlink]
    show _ ≤ (alQ : ℝ)
    linarith
  · rw [rToks, if_neg (by norm_num), if_neg (by norm_num), hlink]
    show _ ≤ (gaQ : ℝ)
    linarith

/-- **The T1 route factor**: route words from `A` weigh at most `α = 66.953`. -/
theorem route1_V_le (N : ℕ) : route1.V N 1 ≤ (alQ : ℝ) := by
  have h := route1.V_le (fun _ t => t1Tok_nonneg t) (fun q => q ≤ 2)
    (fun q _ t _ => by
      show rNext q t ≤ 2
      cases t <;> simp [rNext] <;> omega)
    r1B (fun q hq => route1_bellman q hq)
    (fun q _ => by unfold r1B; split_ifs <;> norm_num [alQ, beQ, gaQ]) N 1 (by norm_num)
  simpa [r1B] using h

/-- **T1 route words**: every finite set of allowed route words from `A` weighs at most `α`. -/
theorem route1_words_le (R : Finset (List Tok)) (hR : ∀ r ∈ R, route1.Gram 1 r) :
    ∑ r ∈ R, route1.wt 1 r ≤ (alQ : ℝ) :=
  le_trans (route1.sum_wt_le (fun _ t => t1Tok_nonneg t) (fun _ => zero_le_one) (R.sup List.length) 1 R
    fun r hr => ⟨hR r hr, Finset.le_sup hr⟩) (route1_V_le _)

end QECD1
