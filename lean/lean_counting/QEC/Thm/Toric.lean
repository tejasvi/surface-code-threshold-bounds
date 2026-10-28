import QEC.Checks.T8.All
import QEC.Count.TorFinal

/-!
# Theorem A′: the toric code at `p ≤ 9/200 = 0.045` (seam-aware certificate T8: windows of up to 8 edges)

The `L × L` toric code, one error sector at code capacity (`QEC/Count/Torus.lean`): checks at the points of the torus,
qubits on its edges, every qubit flipped independently with probability `p`; a correction fails iff the residual
crosses one of the two seams an odd number of times (homologically nontrivial). The certificate is
`cc2d/seam/s8_p045` (tie-break `φ = x_rep`, seam-aware rules, `L0 = 769`, `p** = 9/200`, `X = 31943/10000`,
`λ = 249/250`). The axioms of `toric_A'` and `toric_A'_ML`: the three standard ones and the `native_decide`
certificates of `QEC/Checks/T8`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem A′.** On the `L × L` torus with `L ≥ 769`, at `p ≤ 0.045`, some minimum-weight correction fails with
probability at most `L² · 383157811 · λ^(L - 8) / (1 - λ)`, `λ = 0.996 √(p (1 - p) / (0.045 · 0.955))`. -/
theorem toric_A' (L : ℕ) (hL : 769 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * 383157811 * (249 / 250 * rhoOf (9 / 200) p) ^ (L - 8) /
      (1 - 249 / 250 * rhoOf (9 / 200) p) := by
  have hb := tor_bound_of_cert PT8 nkT8 nGT8 bkT8 bHT8 QECChecks.T8.certOK 45 1000 31943 10000
    (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (L := L) (by simp [PT8]; omega) (by simp [PT8]; omega) hp0
    (by norm_num; linarith)
  have e1 : ((PT8.K0n : ℕ) : ℝ) / (PT8.K0d : ℕ) = 383157811 := by norm_num [PT8]
  have e2 : ((PT8.lamN : ℕ) : ℝ) / (PT8.lamD : ℕ) = 249 / 250 := by norm_num [PT8]
  have e3 : ((45 : ℕ) : ℝ) / (1000 : ℕ) = 9 / 200 := by norm_num
  have e4 : L - 1 - PT8.K = L - 8 := by simp [PT8]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem A′ for maximum-likelihood decoding.** -/
theorem toric_A'_ML (L : ℕ) (hL : 769 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailTorML L p ≤ (L : ℝ) ^ 2 * 383157811 * (249 / 250 * rhoOf (9 / 200) p) ^ (L - 8) /
      (1 - 249 / 250 * rhoOf (9 / 200) p) :=
  le_trans (PfailTorML_le L hp0.le (by linarith)) (toric_A' L hL hp0 hp)

end QEC
