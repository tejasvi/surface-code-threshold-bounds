import QEC.Checks.A6.All

/-!
# The planar code at `p ≤ 0.044` (certificate A6: windows of up to 6 edges)

Unrotated planar code, one error sector, code capacity: checks `[0, nx) × [0, ny)`, half-edges at the columns `0`
(to `b1`) and `nx - 1` (to `b2`); code distance `nx + 1`. The axioms of `planar_A6` and `planar_A6_ML`: the three
standard ones and the `native_decide` certificates of `QEC/Checks/A6`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **The planar code at `p ≤ 0.044`**: every minimum-weight decoder (any tie rule) fails with probability at most
`ny · 2.2676 · λ^(nx - 6) / (1 - λ)`, `λ = 0.997 √(p (1 - p) / (0.044 · 0.956))`. -/
theorem planar_A6 (nx ny : ℕ) (hnx : 6 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailMW (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (22676 / 10000) * (997 / 1000 * rhoOf (11 / 250) p) ^ (nx - 6) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) := by
  have hb := QECChecks.A6.bound ![nx, ny] (0 : Fin 2) (by simp [PA6]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PA6.K0n : ℕ) : ℝ) / (PA6.K0d : ℕ) = 22676 / 10000 := by norm_num [PA6]
  have e2 : ((PA6.lamN : ℕ) : ℝ) / (PA6.lamD : ℕ) = 997 / 1000 := by norm_num [PA6]
  have e3 : ((11 : ℕ) : ℝ) / (250 : ℕ) = 11 / 250 := by norm_num
  have e4 : (![nx, ny] : Fin 2 → ℕ) (0 : Fin 2) - 1 - PA6.K = nx - 6 := by simp [PA6]; omega
  rw [e1, e2, e3, e4] at hb
  exact bound_of_face (card_face_planar nx ny) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb

/-- The same bound for maximum-likelihood decoding. -/
theorem planar_A6_ML (nx ny : ℕ) (hnx : 6 ≤ nx) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 11 / 250) :
    PfailML (boxEdges 2 ![nx, ny] 0) p ≤
      ny * (22676 / 10000) * (997 / 1000 * rhoOf (11 / 250) p) ^ (nx - 6) /
        (1 - 997 / 1000 * rhoOf (11 / 250) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (planar_A6 nx ny hnx hp0 hp)

end QEC
