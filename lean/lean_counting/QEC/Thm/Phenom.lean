import QEC.Checks.D2.All

/-!
# Theorem D2: phenomenological noise at `p ≤ 2/125 = 0.016` (certificate D2: windows of up to 8 edges)

The space-time decoding graph of the planar code with distance `d = H + 1`, width `W`, `T` noisy rounds and a final
perfect round: detectors `(t, X, Y) ∈ [0, T] × [0, W) × [0, H)`, edges between detectors at ℓ¹ distance `1`
(space-like: a data-qubit flip before round `t`; time-like: a flip of a syndrome bit of rounds `0..T-1`),
half-edges at `Y = 0` (to `b1`) and `Y = H - 1` (to `b2`); every edge flips independently with probability `p`
(one edge per error location). The axioms of `phenom_D2` and `phenom_D2_ML`: the three standard ones and the
`native_decide` certificates of `QEC/Checks/D2`.
-/

namespace QEC

open Finset QECComp QECComp.Data

/-- **Theorem D2.** Under phenomenological noise at `p ≤ 0.016`, some minimum-weight correction fails with
probability at most `(T + 1) W · 1.2827 · λ^(d - 9) / (1 - λ)` (`d = H + 1`),
`λ = 0.998 √(p (1 - p) / (0.016 · 0.984))`. -/
theorem phenom_D2 (T W H : ℕ) (hH : 8 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 2 / 125) :
    PfailMW (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (12827 / 10000) * (499 / 500 * rhoOf (2 / 125) p) ^ (H - 8) /
        (1 - 499 / 500 * rhoOf (2 / 125) p) := by
  have hb := QECChecks.D2.bound ![T + 1, W, H] (2 : Fin 3) (by simp [PD2]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PD2.K0n : ℕ) : ℝ) / (PD2.K0d : ℕ) = 12827 / 10000 := by norm_num [PD2]
  have e2 : ((PD2.lamN : ℕ) : ℝ) / (PD2.lamD : ℕ) = 499 / 500 := by norm_num [PD2]
  have e3 : ((2 : ℕ) : ℝ) / (125 : ℕ) = 2 / 125 := by norm_num
  have e4 : (![T + 1, W, H] : Fin 3 → ℕ) (2 : Fin 3) - 1 - PD2.K = H - 8 := by simp [PD2]; omega
  rw [e1, e2, e3, e4] at hb
  have h := bound_of_face (card_face_phenom T W H) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb
  push_cast at h
  exact h

/-- **Theorem D2 for maximum-likelihood decoding.** -/
theorem phenom_D2_ML (T W H : ℕ) (hH : 8 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 2 / 125) :
    PfailML (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (12827 / 10000) * (499 / 500 * rhoOf (2 / 125) p) ^ (H - 8) /
        (1 - 499 / 500 * rhoOf (2 / 125) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (phenom_D2 T W H hH hp0 hp)

end QEC
