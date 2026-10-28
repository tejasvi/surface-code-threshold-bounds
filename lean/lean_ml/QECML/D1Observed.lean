import QECML.TwoD.CertObserved

/-!
# The accepted measurement-error certificate (phenomenological noise, p = 0.02): the observed counts satisfy the
# acceptance rule

This module supports a remark in the paper's discussion only. The deduction of the threshold statement for measurement
errors from the counts is proved on paper and is not formalized here; this module checks the arithmetic of the
accepted counts.

The certificate samples 25 block types (time type × space type, each one of five), with `n = 3,000,000` samples per
type, and accepts iff every count is at most `14`; the bound that its deduction uses is `ε* = 1.85e-5`, and the
per-type Clopper–Pearson level is `1e-9/25 = 4e-11`. It accepted with the counts `d1K` (rows: time type,
columns: space type).

* `d1_accept`: every observed count satisfies the rule (kernel `decide`).
* `d1_rule_tail`: `F(14; 3e6, 1.85e-5) ≤ 4e-11`, so a count of at most `14` has its exact one-sided Clopper–Pearson
  upper bound at level `4e-11` at most `ε*` (kernel evaluation).
* `d1_cp`: for each type, `F(k_t; 3e6, 1.85e-5) ≤ 4e-11`.
* `d1_cp_upper_k4`, `d1_cp_tight_k4`: the largest quoted upper bound, `1.1706e-5` for `k = 4`, is valid and
  correctly rounded up (`F(4; 3e6, 1.1706e-5) ≤ 4e-11 < F(4; 3e6, 1.1705e-5)`; kernel evaluation).
-/

namespace QECML

/-- The observed counts of the measurement-error certificate: row = time type, column = space type. -/
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

end QECML
