import QEC.Checks.R10.All
import QEC.Count.RotFinalA

/-!
# Theorem B: the rotated surface code at `p ≤ 93/2000 = 0.0465` (augmented certificate R10: windows of up to 10 edges)

The rotated surface code of odd distance `d`, one error sector (Z errors, X checks), code capacity, as defined at the
qubit level in `QEC/Count/RotLayout.lean` (`PfailRot`, `PfailRotML`). The certificate is the augmented
certificate `cc2d/rot10/r10_p0465` (FULL rules in the bulk, region-aware rules with exact heights within `HC = 24` of
the top smooth side, strict bottom side). The axioms of `rotated_B` and `rotated_B_ML`: the three standard ones and the
`native_decide` certificates of `QEC/Checks/R10`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem B.** For the rotated surface code of odd distance `d ≥ 11` at `p ≤ 0.0465`, some minimum-weight
correction fails with probability at most `2d · 366183771.98 · λ^(d - 11) / (1 - λ)`,
`λ = 0.998 √(p (1 - p) / (0.0465 · 0.9535))`. -/
theorem rotated_B (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailRot d p ≤
      2 * d * (36618377198 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (d - 11) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) := by
  have hb := rot_bound_of_certA PR10 nkR10 nGR10 bkR10 bHR10 QECChecks.R10.certOK d (by omega) hodd
    465 10000 30910 10000 (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by simp [PR10]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PR10.K0n : ℕ) : ℝ) / (PR10.K0d : ℕ) = 36618377198 / 100 := by norm_num [PR10]
  have e2 : ((PR10.lamN : ℕ) : ℝ) / (PR10.lamD : ℕ) = 499 / 500 := by norm_num [PR10]
  have e3 : ((465 : ℕ) : ℝ) / (10000 : ℕ) = 93 / 2000 := by norm_num
  have e4 : d - 2 - PR10.K = d - 11 := by simp [PR10]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem B for maximum-likelihood decoding.** -/
theorem rotated_B_ML (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailRotML d p ≤
      2 * d * (36618377198 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (d - 11) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) :=
  le_trans (PfailRotML_le d p hp0.le (by linarith)) (rotated_B d hd hodd hp0 hp)

end QEC
