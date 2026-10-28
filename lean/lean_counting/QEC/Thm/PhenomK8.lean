import QEC.KChecks.D2M8K2.All
import QEC.Count.Inst

/-!
# Theorem D2, kernel-checked: phenomenological noise at `p ≤ 2/125 = 0.016` (certificate D2M8K2: windows of up to 8 edges)

The statement of `phenom_D2` (`QEC/Thm/Phenom.lean`), proved from the same certificate (`d2/out/m8.states`,
`d2/cert/m8_p016.H`) through the kernel route, version 2 (`QECCountComp/Kern2.lean`; `QEC/KChecks/D2M8K2`, run on
four machines): the axioms of `phenom_D2M8_kernel` and `phenom_D2M8_kernel_ML` are the three standard
ones only.
-/

namespace QEC

open Finset QECComp QECComp.KData

/-- **Theorem D2, kernel-checked.** Under phenomenological noise at `p ≤ 0.016`, some minimum-weight correction fails
with probability at most `(T + 1) W · 1.2827 · λ^(d - 9) / (1 - λ)` (`d = H + 1`),
`λ = 0.998 √(p (1 - p) / (0.016 · 0.984))`. -/
theorem phenom_D2M8_kernel (T W H : ℕ) (hH : 8 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 2 / 125) :
    PfailMW (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (12827 / 10000) * (499 / 500 * rhoOf (2 / 125) p) ^ (H - 8) /
        (1 - 499 / 500 * rhoOf (2 / 125) p) := by
  have hb := QECKChecks.D2M8K2.bound ![T + 1, W, H] (2 : Fin 3) (by simp [PD2M8K2]; omega) hp0
    (by norm_num; linarith)
  have e1 : ((PD2M8K2.K0n : ℕ) : ℝ) / (PD2M8K2.K0d : ℕ) = 12827 / 10000 := by norm_num [PD2M8K2]
  have e2 : ((PD2M8K2.lamN : ℕ) : ℝ) / (PD2M8K2.lamD : ℕ) = 499 / 500 := by norm_num [PD2M8K2]
  have e3 : ((2 : ℕ) : ℝ) / (125 : ℕ) = 2 / 125 := by norm_num
  have e4 : (![T + 1, W, H] : Fin 3 → ℕ) (2 : Fin 3) - 1 - PD2M8K2.K = H - 8 := by simp [PD2M8K2]; omega
  rw [e1, e2, e3, e4] at hb
  have h := bound_of_face (card_face_phenom T W H) (by norm_num) (by norm_num) (by norm_num) (rhoOf_nonneg _ _)
    (rhoOf_le_one hp0 hp (by norm_num)) _ hb
  push_cast at h
  exact h

/-- **Theorem D2 for maximum-likelihood decoding, kernel-checked.** -/
theorem phenom_D2M8_kernel_ML (T W H : ℕ) (hH : 8 ≤ H) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 2 / 125) :
    PfailML (boxEdges 3 ![T + 1, W, H] 2) p ≤
      (T + 1) * W * (12827 / 10000) * (499 / 500 * rhoOf (2 / 125) p) ^ (H - 8) /
        (1 - 499 / 500 * rhoOf (2 / 125) p) :=
  le_trans (PfailML_le_PfailMW _ hp0.le (by linarith)) (phenom_D2M8_kernel T W H hH hp0 hp)

end QEC
