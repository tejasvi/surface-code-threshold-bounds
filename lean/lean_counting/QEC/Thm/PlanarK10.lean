import QEC.KChecks.A10K2.All
import QEC.Count.Inst

/-!
# Theorem A, kernel-checked: the planar code at `p ≤ 93/2000 = 0.0465` (certificate A10K2: windows of up to 10 edges)

The statement of `planar_A` (`QEC/Thm/Planar.lean`), proved from the same certificate (certificate
`cc2d/cert/m10g_p0465`) through the kernel route, version 2 (`QECCountComp/Kern2.lean`: every check walks one named
subtree; `QEC/KChecks/A10K2`, run on three machines): the axioms of `planar_A10_kernel` and
`planar_A10_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Theorem A, kernel-checked.** For the unrotated planar code at `p ≤ 0.0465`, some minimum-weight correction fails
with probability at most `ny · 398.91 · λ^(nx - 10) / (1 - λ)`, `λ = 0.998 √(p (1 - p) / (0.0465 · 0.9535))`. -/
theorem planar_A10_kernel (nx ny : ℕ) (hnx : 10 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailMW (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (39891 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (nx - 10) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) := by
  have hb := QECKChecks.A10K2.bound ![nx, ny] (0 : Fin 2) (by simp [PA10K2]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PA10K2.K0n : ℕ) : ℝ) / (PA10K2.K0d : ℕ) = 39891 / 100 := by norm_num [PA10K2]
  have e2 : ((PA10K2.lamN : ℕ) : ℝ) / (PA10K2.lamD : ℕ) = 499 / 500 := by norm_num [PA10K2]
  have e3 : ((93 : ℕ) : ℝ) / (2000 : ℕ) = 93 / 2000 := by norm_num
  have e4 : (![nx, ny] : Fin 2 → ℕ) (0 : Fin 2) - 1 - PA10K2.K = nx - 10 := by simp [PA10K2]; omega
  rw [e1, e2, e3, e4] at hb
  exact bound_of_face (card_face_planar nx ny) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb

/-- **Theorem A for maximum-likelihood decoding, kernel-checked.** -/
theorem planar_A10_kernel_ML (nx ny : ℕ) (hnx : 10 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailML (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (39891 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (nx - 10) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (planar_A10_kernel nx ny hnx hp0 hp)

end QEC
