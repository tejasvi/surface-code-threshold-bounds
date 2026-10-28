import QEC.KChecks.KA8.All

/-!
# The planar code at `p ≤ 9/200 = 0.045`, checked by the kernel (certificate KA8: windows of up to 8 edges)

The planar code of `QEC/Thm/Planar.lean`, from the certificate `cc2d/cert/m8g_p045` (M = 8, `p** = 9/200`,
`X = 31766/10000`, `λ = 199/200`), with every check evaluated by the Lean kernel (`decide +kernel`, `QEC/KChecks/KA8`,
run on one machine): the axioms of `planar_A8_kernel` and `planar_A8_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **The planar code at `p ≤ 0.045`, kernel-checked**: every minimum-weight decoder (any tie rule) fails with
probability at most `ny · 94.47 · λ^(nx - 8) / (1 - λ)`, `λ = 0.995 √(p (1 - p) / (0.045 · 0.955))`. -/
theorem planar_A8_kernel (nx ny : ℕ) (hnx : 8 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailMW (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (9447 / 100) * (199 / 200 * rhoOf (9 / 200) p) ^ (nx - 8) /
        (1 - 199 / 200 * rhoOf (9 / 200) p) := by
  have hb := QECKChecks.KA8.bound ![nx, ny] (0 : Fin 2) (by simp [PKA8]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PKA8.K0n : ℕ) : ℝ) / (PKA8.K0d : ℕ) = 9447 / 100 := by norm_num [PKA8]
  have e2 : ((PKA8.lamN : ℕ) : ℝ) / (PKA8.lamD : ℕ) = 199 / 200 := by norm_num [PKA8]
  have e3 : ((9 : ℕ) : ℝ) / (200 : ℕ) = 9 / 200 := by norm_num
  have e4 : (![nx, ny] : Fin 2 → ℕ) (0 : Fin 2) - 1 - PKA8.K = nx - 8 := by simp [PKA8]; omega
  rw [e1, e2, e3, e4] at hb
  exact bound_of_face (card_face_planar nx ny) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb

/-- The same bound for maximum-likelihood decoding, kernel-checked. -/
theorem planar_A8_kernel_ML (nx ny : ℕ) (hnx : 8 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 9 / 200) :
    PfailML (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (9447 / 100) * (199 / 200 * rhoOf (9 / 200) p) ^ (nx - 8) /
        (1 - 199 / 200 * rhoOf (9 / 200) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (planar_A8_kernel nx ny hnx hp0 hp)

end QEC
