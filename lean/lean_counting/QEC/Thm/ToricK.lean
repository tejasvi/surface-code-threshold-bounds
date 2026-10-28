import QEC.KChecks.T8K.All
import QEC.Count.TorFinalK

/-!
# Theorem A′, kernel-checked: the toric code at `p ≤ 9/200 = 0.045` (seam certificate T8, kernel route)

The statement of `toric_A'` (`QEC/Thm/Toric.lean`), proved from the same certificate (certificate `cc2d/seam/s8_p045`)
through the kernel route for seam certificates (`QECCountComp/KernT.lean`, soundness `QEC/Count/CertSoundTK.lean`,
`QEC/Count/TorFinalK.lean`; check modules `QEC/KChecks/T8K`): the axioms of `toric_A'_kernel` and `toric_A'_kernel_ML`
are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Theorem A′, kernel-checked.** On the `L × L` torus with `L ≥ 769`, at `p ≤ 0.045`, some minimum-weight
correction fails with probability at most `L² · 383157811 · λ^(L - 8) / (1 - λ)`,
`λ = 0.996 √(p (1 - p) / (0.045 · 0.955))`. -/
theorem toric_A'_kernel (L : ℕ) (hL : 769 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * 383157811 * (249 / 250 * rhoOf (9 / 200) p) ^ (L - 8) /
      (1 - 249 / 250 * rhoOf (9 / 200) p) := by
  have hb := tor_bound_of_certK PT8K tNT8K.find tBT8K.find tNT8K.toList tBT8K.toList QECKChecks.T8K.cert
    45 1000 31943 10000 (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide) (L := L) (by simp [PT8K]; omega) (by simp [PT8K]; omega) hp0
    (by norm_num; linarith)
  have e1 : ((PT8K.K0n : ℕ) : ℝ) / (PT8K.K0d : ℕ) = 383157811 := by norm_num [PT8K]
  have e2 : ((PT8K.lamN : ℕ) : ℝ) / (PT8K.lamD : ℕ) = 249 / 250 := by norm_num [PT8K]
  have e3 : ((45 : ℕ) : ℝ) / (1000 : ℕ) = 9 / 200 := by norm_num
  have e4 : L - 1 - PT8K.K = L - 8 := by simp [PT8K]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem A′ for maximum-likelihood decoding, kernel-checked.** -/
theorem toric_A'_kernel_ML (L : ℕ) (hL : 769 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailTorML L p ≤ (L : ℝ) ^ 2 * 383157811 * (249 / 250 * rhoOf (9 / 200) p) ^ (L - 8) /
      (1 - 249 / 250 * rhoOf (9 / 200) p) :=
  le_trans (PfailTorML_le L hp0.le (by linarith)) (toric_A'_kernel L hL hp0 hp)

end QEC
