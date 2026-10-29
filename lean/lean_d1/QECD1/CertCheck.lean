import QECD1.CertData

/-!
# Kernel checks of the Bellman certificates of the refined 3D T2 count

`ex_check`, `fam_check`: the Bellman vectors of `QECD1.CertData` satisfy the Bellman inequalities of the excursion
and family automata (one natural-number inequality per state, evaluated by the kernel). Hence (`check_sound`) the
values of the corresponding real automata are bounded by the certificate entries:

* excursion factor at `B`: `exc ≤ 57180026368 / 10^15 ≈ 5.718e-5`;
* family factor of axis x at `B` before the mark: `F0x ≤ 2174093984726 / 10^15 ≈ 2.174e-3`.

The three axes agree at `s = 0`, so `F0 ≤ 3 F0x ≈ 6.522e-3`.
-/

namespace QECD1.CertData

theorem ex_check : exAut.check Qden (fun q => exB.getD q.val 0) = true := by decide +kernel

theorem fam_check : famAut.check Qden (fun q => famB.getD q.val 0) = true := by decide +kernel

theorem Qden_pos : 0 < Qden := by decide

/-- **Excursion factor**: every word length, from `B` (state 0). -/
theorem ex_val_le (N : ℕ) : (exAut.toFAut Qden).val N 0 ≤ (57180026368 : ℝ) / 10 ^ 15 := by
  have h := NatAut.check_sound exAut Qden Qden_pos _ ex_check N 0
  have e1 : exB.getD (0 : Fin 52).val 0 = 57180026368 := by decide +kernel
  have e2 : ((Qden : ℕ) : ℝ) = 10 ^ 15 := by norm_num [Qden]
  rw [e1, e2] at h
  exact_mod_cast h

/-- **Family factor of one axis**: every word length, from `B` before the mark (state 0). -/
theorem fam_val_le (N : ℕ) : (famAut.toFAut Qden).val N 0 ≤ (2174093984726 : ℝ) / 10 ^ 15 := by
  have h := NatAut.check_sound famAut Qden Qden_pos _ fam_check N 0
  have e1 : famB.getD (0 : Fin 104).val 0 = 2174093984726 := by decide +kernel
  have e2 : ((Qden : ℕ) : ℝ) = 10 ^ 15 := by norm_num [Qden]
  rw [e1, e2] at h
  exact_mod_cast h

end QECD1.CertData
