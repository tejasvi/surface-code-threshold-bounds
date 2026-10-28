import QEC.KChecks.T10P.All
import QEC.Count.TorFinalK

/-!
# Theorem A′ at `p ≤ 0.046`, kernel-checked (seam certificate T10, kernel route, packed trees)

The statement of `toric_A'_10` (`QEC/Thm/Toric10.lean`), proved from the same certificate (certificate `t10_p046`)
through the kernel route for seam certificates (`QECCountComp/KernT.lean`, packed trees `QECCountComp/KernP.lean`,
soundness `QEC/Count/CertSoundTK.lean`, `QEC/Count/TorFinalK.lean`; check modules `QEC/KChecks/T10P`): the axioms of
`toric_A'_10_kernel` and `toric_A'_10_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Theorem A′ at `p ≤ 0.046`, kernel-checked.** On the `L × L` torus with `L ≥ 1201`, at `p ≤ 0.046`, some
minimum-weight correction fails with probability at most `L² · 428572391.6 · λ^(L - 10) / (1 - λ)`,
`λ = 0.997 √(p (1 - p) / (0.046 · 0.954))`. -/
theorem toric_A'_10_kernel (L : ℕ) (hL : 1201 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 23 / 500) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * (4285723916 / 10) * (997 / 1000 * rhoOf (23 / 500) p) ^ (L - 10) /
      (1 - 997 / 1000 * rhoOf (23 / 500) p) := by
  have hb := tor_bound_of_certK PT10P (tNT10P.find pwNT10P) (tBT10P.find pwBT10P) (tNT10P.toList pwNT10P)
    (tBT10P.toList pwBT10P) QECKChecks.T10P.cert 46 1000 312228 100000
    (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (L := L) (by simp [PT10P]; omega) (by simp [PT10P]; omega) hp0
    (by norm_num; linarith)
  have e1 : ((PT10P.K0n : ℕ) : ℝ) / (PT10P.K0d : ℕ) = 4285723916 / 10 := by norm_num [PT10P]
  have e2 : ((PT10P.lamN : ℕ) : ℝ) / (PT10P.lamD : ℕ) = 997 / 1000 := by norm_num [PT10P]
  have e3 : ((46 : ℕ) : ℝ) / (1000 : ℕ) = 23 / 500 := by norm_num
  have e4 : L - 1 - PT10P.K = L - 10 := by simp [PT10P]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem A′ at `p ≤ 0.046` for maximum-likelihood decoding, kernel-checked.** -/
theorem toric_A'_10_kernel_ML (L : ℕ) (hL : 1201 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 23 / 500) :
    PfailTorML L p ≤ (L : ℝ) ^ 2 * (4285723916 / 10) * (997 / 1000 * rhoOf (23 / 500) p) ^ (L - 10) /
      (1 - 997 / 1000 * rhoOf (23 / 500) p) :=
  le_trans (PfailTorML_le L hp0.le (by linarith)) (toric_A'_10_kernel L hL hp0 hp)

end QEC
