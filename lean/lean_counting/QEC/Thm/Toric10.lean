import QEC.Checks.T10.All
import QEC.Count.TorFinal

/-!
# Theorem A′ at `p ≤ 23/500 = 0.046`: the toric code (seam-aware certificate T10: windows of up to 10 edges)

The `L × L` toric code of `QEC/Thm/Toric.lean`, with the M = 10 seam certificate `cc2d/seam10/t10_p046`
(tie-break `φ = x_rep`, seam-aware rules, `L0 = 1201`, `p** = 23/500`, `X = 312228/100000`, `λ = 997/1000`). The axioms
of `toric_A'_10` and `toric_A'_10_ML`: the three standard ones and the `native_decide` certificates of
`QEC/Checks/T10`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem A′ at `p ≤ 0.046`.** On the `L × L` torus with `L ≥ 1201`, at `p ≤ 0.046`, some minimum-weight
correction fails with probability at most `L² · 428572391.6 · λ^(L - 10) / (1 - λ)`,
`λ = 0.997 √(p (1 - p) / (0.046 · 0.954))`. -/
theorem toric_A'_10 (L : ℕ) (hL : 1201 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 23 / 500) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * (4285723916 / 10) * (997 / 1000 * rhoOf (23 / 500) p) ^ (L - 10) /
      (1 - 997 / 1000 * rhoOf (23 / 500) p) := by
  have hb := tor_bound_of_cert PT10 nkT10 nGT10 bkT10 bHT10 QECChecks.T10.certOK 46 1000 312228 100000
    (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (L := L) (by simp [PT10]; omega) (by simp [PT10]; omega) hp0
    (by norm_num; linarith)
  have e1 : ((PT10.K0n : ℕ) : ℝ) / (PT10.K0d : ℕ) = 4285723916 / 10 := by norm_num [PT10]
  have e2 : ((PT10.lamN : ℕ) : ℝ) / (PT10.lamD : ℕ) = 997 / 1000 := by norm_num [PT10]
  have e3 : ((46 : ℕ) : ℝ) / (1000 : ℕ) = 23 / 500 := by norm_num
  have e4 : L - 1 - PT10.K = L - 10 := by simp [PT10]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem A′ at `p ≤ 0.046` for maximum-likelihood decoding.** -/
theorem toric_A'_10_ML (L : ℕ) (hL : 1201 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 23 / 500) :
    PfailTorML L p ≤ (L : ℝ) ^ 2 * (4285723916 / 10) * (997 / 1000 * rhoOf (23 / 500) p) ^ (L - 10) /
      (1 - 997 / 1000 * rhoOf (23 / 500) p) :=
  le_trans (PfailTorML_le L hp0.le (by linarith)) (toric_A'_10 L hL hp0 hp)

end QEC
