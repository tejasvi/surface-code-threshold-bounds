import QEC.Checks.S10.All

/-!
# Theorem B (SAFE rules): the rotated surface code at `p ≤ 11/250 = 0.044` (certificate S10: windows of up to 10 edges)

The rotated surface code of odd distance `d`, one error sector (Z errors, X checks), code capacity, as defined at the
qubit level in `QEC/Count/RotLayout.lean` (`PfailRot`, `PfailRotML`). The certificate is the SAFE certificate
`cc2d/cert/s10_p044`. The axioms of `rotated_S10` and `rotated_S10_ML`: the three standard ones and the
`native_decide` certificates of `QEC/Checks/S10`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem B (SAFE).** For the rotated surface code of odd distance `d ≥ 11` at `p ≤ 0.044`, some minimum-weight
correction fails with probability at most `2d · 212.88 · λ^(d - 11) / (1 - λ)`,
`λ = 0.997 √(p (1 - p) / (0.044 · 0.956))`. -/
theorem rotated_S10 (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailRot d p ≤
      2 * d * (21288 / 100) * (997 / 1000 * rhoOf (11 / 250) p) ^ (d - 11) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) := by
  have hb := QECChecks.S10.bound d (by omega) hodd (by simp [PS10]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PS10.K0n : ℕ) : ℝ) / (PS10.K0d : ℕ) = 21288 / 100 := by norm_num [PS10]
  have e2 : ((PS10.lamN : ℕ) : ℝ) / (PS10.lamD : ℕ) = 997 / 1000 := by norm_num [PS10]
  have e3 : ((11 : ℕ) : ℝ) / (250 : ℕ) = 11 / 250 := by norm_num
  have e4 : d - 2 - PS10.K = d - 11 := by simp [PS10]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem B (SAFE) for maximum-likelihood decoding.** -/
theorem rotated_S10_ML (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailRotML d p ≤
      2 * d * (21288 / 100) * (997 / 1000 * rhoOf (11 / 250) p) ^ (d - 11) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) :=
  le_trans (PfailRotML_le d p hp0.le (by linarith)) (rotated_S10 d hd hodd hp0 hp)

end QEC
