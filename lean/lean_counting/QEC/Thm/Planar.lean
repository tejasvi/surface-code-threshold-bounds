import QEC.Checks.A10.All

/-!
# Theorem A: the planar code at `p ≤ 93/2000 = 0.0465` (certificate A10: windows of up to 10 edges)

Unrotated planar code, one error sector, code capacity: checks `[0, nx) × [0, ny)`, edges between checks at ℓ¹
distance `1`, half-edges at the columns `0` (to `b1`) and `nx - 1` (to `b2`); code distance `nx + 1`; every edge
(qubit) flips independently with probability `p`. The axioms of `planar_A` and `planar_A_ML`: the three standard
ones and the `native_decide` certificates of `QEC/Checks/A10`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem A.** For the unrotated planar code at `p ≤ 0.0465`, some minimum-weight correction fails with
probability at most `ny · 398.91 · λ^(nx - 10) / (1 - λ)`, `λ = 0.998 √(p (1 - p) / (0.0465 · 0.9535))`. -/
theorem planar_A (nx ny : ℕ) (hnx : 10 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailMW (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (39891 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (nx - 10) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) := by
  have hb := QECChecks.A10.bound ![nx, ny] (0 : Fin 2) (by simp [PA10]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PA10.K0n : ℕ) : ℝ) / (PA10.K0d : ℕ) = 39891 / 100 := by norm_num [PA10]
  have e2 : ((PA10.lamN : ℕ) : ℝ) / (PA10.lamD : ℕ) = 499 / 500 := by norm_num [PA10]
  have e3 : ((93 : ℕ) : ℝ) / (2000 : ℕ) = 93 / 2000 := by norm_num
  have e4 : (![nx, ny] : Fin 2 → ℕ) (0 : Fin 2) - 1 - PA10.K = nx - 10 := by simp [PA10]; omega
  rw [e1, e2, e3, e4] at hb
  exact bound_of_face (card_face_planar nx ny) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb

/-- **Theorem A for maximum-likelihood decoding.** -/
theorem planar_A_ML (nx ny : ℕ) (hnx : 10 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 93 / 2000) :
    PfailML (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (39891 / 100) * (499 / 500 * rhoOf (93 / 2000) p) ^ (nx - 10) /
        (1 - 499 / 500 * rhoOf (93 / 2000) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (planar_A nx ny hnx hp0 hp)

end QEC
