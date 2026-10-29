import QECD1.CPGen
import QECD1.TheoremB3

/-!
# The ML bound tied to the certificate's confidence statement

The certificate for measurement errors (the registered run, accepted) samples the 25 reference block types `(i, j)`
(time type `i`, space type `j`; `refBlock i j` on the code of `5 × 5 × 5` blocks) with `n = 3,000,000` samples per
type, and accepts iff every count of bad samples is at most `14`. The level is `ε* = 1.85e-5` (`eps`), the per-type
Clopper–Pearson level `4e-11` (Bonferroni over 25 types: `1e-9`). As the 2D `D1Observed`, `CertObserved` and
`TwoD/HeadlineCert`:

* `d1K`, `d1_accept`: the observed counts satisfy the rule (kernel `decide`).
* `d1_rule_tail`: `F(14; 3e6, 1.85e-5) ≤ 4e-11` (kernel evaluation), so `d1_cp`: every type's exact one-sided
  Clopper–Pearson upper bound at level `4e-11` is at most `ε*`.
* `d1_cp_upper_k4`, `d1_cp_tight_k4`: the largest quoted upper bound, `1.1706e-5` for `k = 4`, is valid and
  correctly rounded up (`F(4; 3e6, 1.1706e-5) ≤ 4e-11 < F(4; 3e6, 1.1705e-5)`; kernel evaluations).
* `cert_confidence_D1`: under the binomial model of the counts (`hlaw`), whatever the true rates, the probability of
  accepting while some true rate exceeds `ε*` is at most `1e-9`.
* `d1B_certified`: with the true reference rates of the registered program (`refRate3`), either the bound on
  the ML failure probability holds (`D1BConcl`), or the certificate accepts with probability at most `1e-9`.
  The other inputs stay named hypotheses: V6 and `Hcov3`.
* `cube_tendsto_of_concl`, `threshold_d1_certified`: either the ML failure probability of the cube codes tends to
  `0` at every `q ∈ [0, 0.02]`, or the certificate accepts with probability at most `1e-9`.
-/

open Finset Classical Filter Topology

namespace QECD1

/-- The observed counts of the D1 certificate: row = time type, column = space type. -/
def d1K : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 3, 3, 0], ![2, 1, 1, 1, 2], ![2, 1, 1, 2, 0], ![1, 0, 0, 2, 2], ![0, 4, 1, 2, 1]]

/-- The number of samples per type. -/
def d1N : ℕ := 3000000

/-- **The observed counts satisfy the acceptance rule** (at most `14` bad samples of `3,000,000` per type). -/
theorem d1_accept : ∀ i j, d1K i j ≤ 14 := by decide

/-- The rule's binomial tail at the cutoff: `F(14; 3e6, 1.85e-5) ≤ 4e-11`. -/
theorem d1_rule_tail : binomCDF d1N 14 (185 / 10000000) ≤ 4 / 100000000000 := by
  have h := cpCheck_sound (n := 3000000) (k := 14) (a := 185) (b := 10000000) (c := 4) (d := 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

/-- **Each type's Clopper–Pearson condition**: `F(k_t; 3e6, 1.85e-5) ≤ 4e-11`. -/
theorem d1_cp : ∀ i j, binomCDF d1N (d1K i j) (185 / 10000000) ≤ 4 / 100000000000 := fun i j =>
  (binomCDF_mono_k (d1_accept i j) (by norm_num) (by norm_num)).trans d1_rule_tail

/-- The largest quoted upper bound (`k = 4`) is valid: `F(4; 3e6, 1.1706e-5) ≤ 4e-11`. -/
theorem d1_cp_upper_k4 : binomCDF d1N 4 (11706 / 1000000000) ≤ 4 / 100000000000 := by
  have h := cpCheck_sound (n := 3000000) (k := 4) (a := 11706) (b := 1000000000) (c := 4) (d := 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

/-- ... and correctly rounded up: `4e-11 < F(4; 3e6, 1.1705e-5)`. -/
theorem d1_cp_tight_k4 : 4 / 100000000000 < binomCDF d1N 4 (11705 / 1000000000) := by
  have h := cpCheckGt_sound (n := 3000000) (k := 4) (a := 11705) (b := 1000000000) (c := 4) (d := 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

/-- **Confidence of the D1 certificate** (25 types, `n = 3e6`, accept iff every count is at most `14`,
`ε* = 1.85e-5`, `4e-11` per type): under the binomial model `hlaw`, whatever the true rates `ε t`, the probability
of accepting while some true rate exceeds `ε*` is at most `1e-9`. -/
theorem cert_confidence_D1 {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (K : Fin 5 × Fin 5 → Ω → ℕ) (ε : Fin 5 × Fin 5 → ℝ) (hε : ∀ t, ε t ≤ 1)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 3000000 j : ℕ) : ℝ) * ε t ^ j * (1 - ε t) ^ (3000000 - j)) :
    (∑ ω, if (∀ t, K t ω ≤ 14) ∧ (∃ t, eps < ε t) then P ω else 0) ≤ 1e-9 := by
  have hcp : binomCDF 3000000 14 eps ≤ 4 / 100000000000 := by
    have h := d1_rule_tail
    have e : (185 / 10000000 : ℝ) = eps := by norm_num [eps]
    rw [e] at h
    exact h
  have h := cp_confidence P hP (n := 3000000) (k := 14) (by norm_num) K ε hε hlaw (εhat := eps)
    (α := 4 / 100000000000) (by norm_num [eps]) (by norm_num [eps]) hcp
  have hcard : Fintype.card (Fin 5 × Fin 5) = 25 := by simp
  rw [hcard] at h
  refine (accept_bad_le P hP K ε 14 eps).trans (h.trans ?_)
  norm_num

/-- The conclusion of the ML bound (rounded constants). -/
def D1BConcl : Prop :=
  ∀ (q : ℝ), q ≤ 0.02 → ∀ (T W H : ℕ), 1 ≤ W → 5 * 35 ≤ H →
    pML3 T (W - 1) (H - 1) q ≤
      804 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-0.1008 * (((H / 35 : ℕ) : ℝ) - 47)) +
        5.11e6 * (blkUp (T + 1) : ℝ) * (blkUp W : ℝ) * Real.exp (-0.007 * (((H / 35 : ℕ) : ℝ) - 47))

/-- The true bad probability of the reference block of type `t` at `p = 0.02`, for the registered program. -/
noncomputable def refRate3 (sp : S3Prog3) (hV6 : sp.V6) (t : Fin 5 × Fin 5) : ℝ :=
  prob 0.02 (fun X => ((sp.toFam3 hV6).stage1 5 5 5).bad (toZ2 X) (refBlock t.1 t.2))

theorem refRate3_le_one (sp : S3Prog3) (hV6 : sp.V6) (t : Fin 5 × Fin 5) : refRate3 sp hV6 t ≤ 1 :=
  prob_le_one3 (by norm_num) (by norm_num) _

/-- Without `Hstat3`, some reference rate exceeds `ε*`. -/
theorem exists_rate_gt3 (sp : S3Prog3) (hV6 : sp.V6) (h : ¬ (sp.toFam3 hV6).Hstat3 0.02 eps) :
    ∃ t, eps < refRate3 sp hV6 t := by
  unfold S3Fam3.Hstat3 at h
  push Not at h
  obtain ⟨i, j, hij⟩ := h
  exact ⟨(i, j), hij⟩

/-- **The ML bound, certified.** For the registered stage-1 program under V6 and `Hcov3`, and the binomial model of
the certificate's counts with the true reference rates: either the ML bound holds, or the certificate
accepts with probability at most `1e-9`. -/
theorem d1B_certified (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3) {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : Fin 5 × Fin 5 → Ω → ℕ)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 3000000 j : ℕ) : ℝ) * refRate3 sp hV6 t ^ j * (1 - refRate3 sp hV6 t) ^ (3000000 - j)) :
    D1BConcl ∨ (∑ ω, if (∀ t, K t ω ≤ 14) then P ω else 0) ≤ 1e-9 := by
  by_cases hstat : (sp.toFam3 hV6).Hstat3 0.02 eps
  · exact Or.inl fun q hq T W H hW hH => d1B_num sp hV6 hcov hstat hq hW hH
  · refine Or.inr ?_
    obtain ⟨t0, ht0⟩ := exists_rate_gt3 sp hV6 hstat
    have h := cert_confidence_D1 P hP K (refRate3 sp hV6) (refRate3_le_one sp hV6) hlaw
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ω _ => ?_)) h
    by_cases hacc : ∀ t, K t ω ≤ 14
    · rw [ite_eq_left hacc, ite_eq_left ⟨hacc, t0, ht0⟩]
    · rw [ite_eq_right hacc, ite_eq_right fun h' => hacc h'.1]

/-- Along cube codes (`T + 1 = W = H = n`) the ML failure probability tends to `0` at every `q ∈ [0, 0.02]`, given the
conclusion of the ML bound. -/
theorem cube_tendsto_of_concl (hB : D1BConcl) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.02) :
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
  have hb := hB q hq (n - 1) n n (by omega) hn
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

/-- **Threshold, certified.** For the registered stage-1 program under V6 and `Hcov3`, and the binomial model of
the certificate's counts with the true reference rates: either the ML failure probability of the cube codes tends
to `0` at every `q ∈ [0, 0.02]`, or the certificate accepts with probability at most `1e-9`. -/
theorem threshold_d1_certified (sp : S3Prog3) (hV6 : sp.V6) (hcov : (sp.toFam3 hV6).Hcov3) {Ω : Type*}
    [Fintype Ω] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : Fin 5 × Fin 5 → Ω → ℕ)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 3000000 j : ℕ) : ℝ) * refRate3 sp hV6 t ^ j * (1 - refRate3 sp hV6 t) ^ (3000000 - j)) :
    (∀ q : ℝ, 0 ≤ q → q ≤ 0.02 → Tendsto (fun n : ℕ => pML3 (n - 1) (n - 1) (n - 1) q) atTop (𝓝 0)) ∨
      (∑ ω, if (∀ t, K t ω ≤ 14) then P ω else 0) ≤ 1e-9 :=
  (d1B_certified sp hV6 hcov P hP K hlaw).imp (fun hB _q hq0 hq => cube_tendsto_of_concl hB hq0 hq) id

/-- The observed outcome lies in the acceptance event of `d1B_certified` (types indexed by pairs). -/
theorem d1K_accept_pairs : ∀ t : Fin 5 × Fin 5, d1K t.1 t.2 ≤ 14 := fun t => d1_accept t.1 t.2

end QECD1
