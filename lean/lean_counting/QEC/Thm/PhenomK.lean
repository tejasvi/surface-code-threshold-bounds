import QEC.KChecks.D2K6.All

/-!
# Phenomenological noise at `p ≤ 31/2000 = 0.0155`, checked by the kernel (certificate D2K6: windows of up to 6 edges)

The decoding graph of `QEC/Thm/Phenom.lean` (planar code of distance `d = H + 1`, width `W`, `T` noisy rounds and a
final perfect round). The certificate is `d2/out/m6.states` with `d2/cert/m6_p0155.H` (M = 6,
`p** = 31/2000`, `X = 49/10`, `λ = 199/200`); every check is evaluated by the Lean kernel (`decide +kernel`,
`QEC/KChecks/D2K6`), so the axioms of `phenom_D2_kernel` and `phenom_D2_kernel_ML` are the three standard ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Phenomenological noise at `p ≤ 0.0155`, kernel-checked**: some minimum-weight correction fails with
probability at most `(T + 1) W · 0.5917 · λ^(d - 7) / (1 - λ)` (`d = H + 1`),
`λ = 0.995 √(p (1 - p) / (0.0155 · 0.9845))`. -/
theorem phenom_D2_kernel (T W H : ℕ) (hH : 6 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 31 / 2000) :
    PfailMW (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (5917 / 10000) * (199 / 200 * rhoOf (31 / 2000) p) ^ (H - 6) /
        (1 - 199 / 200 * rhoOf (31 / 2000) p) := by
  have hb := QECKChecks.D2K6.bound ![T + 1, W, H] (2 : Fin 3) (by simp [PD2K6]; omega) hp0 (by norm_num; linarith)
  have e1 : ((PD2K6.K0n : ℕ) : ℝ) / (PD2K6.K0d : ℕ) = 5917 / 10000 := by norm_num [PD2K6]
  have e2 : ((PD2K6.lamN : ℕ) : ℝ) / (PD2K6.lamD : ℕ) = 199 / 200 := by norm_num [PD2K6]
  have e3 : ((31 : ℕ) : ℝ) / (2000 : ℕ) = 31 / 2000 := by norm_num
  have e4 : (![T + 1, W, H] : Fin 3 → ℕ) (2 : Fin 3) - 1 - PD2K6.K = H - 6 := by simp [PD2K6]; omega
  rw [e1, e2, e3, e4] at hb
  have h := bound_of_face (card_face_phenom T W H) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb
  push_cast at h
  exact h

/-- The same bound for maximum-likelihood decoding, kernel-checked. -/
theorem phenom_D2_kernel_ML (T W H : ℕ) (hH : 6 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 31 / 2000) :
    PfailML (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (5917 / 10000) * (199 / 200 * rhoOf (31 / 2000) p) ^ (H - 6) /
        (1 - 199 / 200 * rhoOf (31 / 2000) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (phenom_D2_kernel T W H hH hp0 hp)

end QEC
