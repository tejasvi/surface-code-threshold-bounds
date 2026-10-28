import QEC.KChecks.A6K.All

/-!
# The planar code at `p ≤ 0.044`, checked by the kernel (certificate A6K: windows of up to 6 edges)

The statement of `planar_A6` (`QEC/Thm/PlanarA6.lean`), proved from the same certificate (certificate
`cc2d/cert/m6g_p044`) with every check evaluated by the Lean kernel (`decide +kernel`, `QEC/KChecks/A6K`): the axioms
of `planar_A6_kernel` and `planar_A6_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **The planar code at `p ≤ 0.044`, kernel-checked**: every minimum-weight decoder (any tie rule) fails with
probability at most `ny · 2.2676 · λ^(nx - 6) / (1 - λ)`, `λ = 0.997 √(p (1 - p) / (0.044 · 0.956))`. -/
theorem planar_A6_kernel (nx ny : ℕ) (hnx : 6 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailMW (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (22676 / 10000) * (997 / 1000 * rhoOf (11 / 250) p) ^ (nx - 6) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) := by
  have hb := QECKChecks.A6K.bound ![nx, ny] (0 : Fin 2) (by simp [PA6K]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PA6K.K0n : ℕ) : ℝ) / (PA6K.K0d : ℕ) = 22676 / 10000 := by norm_num [PA6K]
  have e2 : ((PA6K.lamN : ℕ) : ℝ) / (PA6K.lamD : ℕ) = 997 / 1000 := by norm_num [PA6K]
  have e3 : ((11 : ℕ) : ℝ) / (250 : ℕ) = 11 / 250 := by norm_num
  have e4 : (![nx, ny] : Fin 2 → ℕ) (0 : Fin 2) - 1 - PA6K.K = nx - 6 := by simp [PA6K]; omega
  rw [e1, e2, e3, e4] at hb
  exact bound_of_face (card_face_planar nx ny) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb

/-- The same bound for maximum-likelihood decoding, kernel-checked. -/
theorem planar_A6_kernel_ML (nx ny : ℕ) (hnx : 6 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailML (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (22676 / 10000) * (997 / 1000 * rhoOf (11 / 250) p) ^ (nx - 6) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (planar_A6_kernel nx ny hnx hp0 hp)

end QEC
