import QECML.TwoD.HeadlineCert

/-!
# The accepted q = 0.100 certificate: the observed counts satisfy the registered acceptance rule

The registered experiment (L = 280, R = 279, design A, n = 120000 samples per type) accepted with the bad-block
counts bulk 6, L0 3, L1 8, R0 9, R1 6. In the indexing of the reference blocks (`S3Fam.refBlock t`, column `t` of the
5 × 5-block reference code: 0 = L0, 1 = L1, 2 = bulk, 3 = R1, 4 = R0) the counts are `obsK = ![3, 8, 6, 6, 9]`, each of
`obsN t = 120000`.

* `obs_accept`: the observed pairs satisfy the acceptance rule of design A (`n = 120000`, `k ≤ 18`), so the observed
  outcome lies in the acceptance event `∀ t, K t ≤ 18` of `theoremB_certified` (kernel evaluation).
* `obs_cp`: for every type, `F(k_t; 1.2e5, 5e-4) ≤ 2e-10`: the exact one-sided Clopper–Pearson upper bound at level
  `2e-10` is at most `ε* = 5e-4` (the registered analysis's condition), from `cp_accept_A` (the rule's tail at the
  cutoff, `F(18; 1.2e5, 5e-4) ≤ 2e-10`, a kernel evaluation) and the monotonicity of the lower tail in `k`.
-/

open Finset

namespace QECML

/-- The observed bad-block counts of the accepted certificate, indexed by reference column. -/
def obsK : Fin 5 → ℕ := ![3, 8, 6, 6, 9]

/-- The observed numbers of samples per type. -/
def obsN : Fin 5 → ℕ := fun _ => 120000

/-- The acceptance rule of design A for one type: `n = 120000` samples and at most `18` bad blocks. -/
def accA (n k : ℕ) : Bool := n == 120000 && decide (k ≤ 18)

/-- **The observed pairs satisfy the acceptance rule.** -/
theorem obs_accept : ∀ t, accA (obsN t) (obsK t) = true := by decide

/-- The observed outcome lies in the acceptance event of `theoremB_certified`. -/
theorem obsK_le : ∀ t, obsK t ≤ 18 := by decide

/-- The binomial lower tail is monotone in `k`. -/
theorem binomCDF_mono_k {n k k' : ℕ} {p : ℝ} (hk : k ≤ k') (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binomCDF n k p ≤ binomCDF n k' p := by
  unfold binomCDF
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (by omega)
  · intro j _ _
    have : 0 ≤ 1 - p := by linarith
    positivity

/-- **Each type's Clopper–Pearson condition**: `F(k_t; 1.2e5, 5e-4) ≤ 2e-10`. -/
theorem obs_cp : ∀ t, binomCDF 120000 (obsK t) 5e-4 ≤ 2e-10 := fun t =>
  (binomCDF_mono_k (obsK_le t) (by norm_num) (by norm_num)).trans cp_accept_A

/-! ## The quoted Clopper–Pearson upper bounds

For `k = 3, 6, 8, 9` the exact one-sided upper bound `p_U` at level `2e-10` (the root of `F(k; 1.2e5, p) = 2e-10`) is
quoted rounded up to four digits: `2.578e-4, 3.142e-4, 3.483e-4, 3.647e-4`. Since `F(k; n, ·)` is antitone on
`[0, 1]`, `F(k; n, u) ≤ 2e-10` gives `p_U ≤ u`, and `2e-10 < F(k; n, u - 1e-7)` gives `p_U > u - 1e-7`: the quoted
values are the correctly rounded-up bounds. Kernel evaluations (`decide +kernel`). -/

theorem cp_upper_k3 : binomCDF 120000 3 (2578 / 10000000) ≤ 2 / 10000000000 := by
  have h := cpCheck_sound (n := 120000) (k := 3) (a := 2578) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_upper_k6 : binomCDF 120000 6 (3142 / 10000000) ≤ 2 / 10000000000 := by
  have h := cpCheck_sound (n := 120000) (k := 6) (a := 3142) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_upper_k8 : binomCDF 120000 8 (3483 / 10000000) ≤ 2 / 10000000000 := by
  have h := cpCheck_sound (n := 120000) (k := 8) (a := 3483) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_upper_k9 : binomCDF 120000 9 (3647 / 10000000) ≤ 2 / 10000000000 := by
  have h := cpCheck_sound (n := 120000) (k := 9) (a := 3647) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_tight_k3 : 2 / 10000000000 < binomCDF 120000 3 (2577 / 10000000) := by
  have h := cpCheckGt_sound (n := 120000) (k := 3) (a := 2577) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_tight_k6 : 2 / 10000000000 < binomCDF 120000 6 (3141 / 10000000) := by
  have h := cpCheckGt_sound (n := 120000) (k := 6) (a := 3141) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_tight_k8 : 2 / 10000000000 < binomCDF 120000 8 (3482 / 10000000) := by
  have h := cpCheckGt_sound (n := 120000) (k := 8) (a := 3482) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

theorem cp_tight_k9 : 2 / 10000000000 < binomCDF 120000 9 (3646 / 10000000) := by
  have h := cpCheckGt_sound (n := 120000) (k := 9) (a := 3646) (b := 10000000) (c := 2) (d := 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h ⊢
  exact h

end QECML
