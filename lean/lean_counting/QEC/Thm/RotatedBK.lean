import QEC.KChecks.R10P.All
import QEC.Count.RotFinalAK

/-!
# Theorem B, kernel-checked: the rotated surface code at `p ≤ 93/2000 = 0.0465` (augmented certificate R10, kernel
route, packed trees)

The statement of `rotated_B` (`QEC/Thm/RotatedB.lean`), proved from the same certificate (certificate
`cc2d/rot10/r10_p0465`) through the kernel route for augmented certificates (`QECCountComp/KernA.lean`, packed trees
`QECCountComp/KernP.lean`, soundness `QEC/Count/CertSoundAK.lean`, `QEC/Count/RotFinalAK.lean`; check modules
`QEC/KChecks/R10P`): the axioms of `rotated_B_kernel` and `rotated_B_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Theorem B, kernel-checked.** For the rotated surface code of odd distance `d ≥ 11` at `p ≤ 0.0465`, some
minimum-weight correction fails with probability at most `2d · 366183771.98 · λ^(d - 11) / (1 - λ)`,
`λ = 0.998 √(p (1 - p) / (0.0465 · 0.9535))`. -/
theorem rotated_B_kernel (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailRot d p ≤
      2 * d * (36618377198 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (d - 11) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) := by
  have hb := rot_bound_of_certAK PR10P (tNR10P.find pwNR10P) (tBR10P.find pwBR10P) (tNR10P.toList pwNR10P)
    (tBR10P.toList pwBR10P) QECKChecks.R10P.cert d (by omega) hodd
    465 10000 30910 10000 (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by simp [PR10P]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PR10P.K0n : ℕ) : ℝ) / (PR10P.K0d : ℕ) = 36618377198 / 100 := by norm_num [PR10P]
  have e2 : ((PR10P.lamN : ℕ) : ℝ) / (PR10P.lamD : ℕ) = 499 / 500 := by norm_num [PR10P]
  have e3 : ((465 : ℕ) : ℝ) / (10000 : ℕ) = 93 / 2000 := by norm_num
  have e4 : d - 2 - PR10P.K = d - 11 := by simp [PR10P]; omega
  rw [e1, e2, e3, e4] at hb
  exact hb

/-- **Theorem B for maximum-likelihood decoding, kernel-checked.** -/
theorem rotated_B_kernel_ML (d : ℕ) (hd : 11 ≤ d) (hodd : Odd d) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailRotML d p ≤
      2 * d * (36618377198 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (d - 11) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) :=
  le_trans (PfailRotML_le d p hp0.le (by linarith)) (rotated_B_kernel d hd hodd hp0 hp)

end QEC
