import QEC.Count.Final
import QEC.Count.Chunks

/-!
# Helpers for the instances

The size of the face `x_a = 0` of the planar code (`n = 2`, `a = 0`) and of the phenomenological space-time graph
(`n = 3`, `a = 2`), bounds on `ρ`, and the bound of `box_bound_of_cert` with the face size replaced by an upper bound.
-/

namespace QEC

open Finset

theorem card_face_planar (nx ny : ℕ) :
    #(univ.filter (fun u : BoxV 2 ![nx, ny] => (u 0 : ℕ) = 0)) ≤ ny := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter (fun u : BoxV 2 ![nx, ny] => (u 0 : ℕ) = 0))
    (t := (univ : Finset (Fin ny))) (fun u => (u 1 : Fin ny)) (by intro u _; exact Finset.mem_coe.mpr (Finset.mem_univ _)) (by
      intro u hu v hv huv
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu hv
      funext i
      fin_cases i
      · exact Fin.ext (by simp only [Fin.zero_eta] at hu hv ⊢; rw [hu, hv])
      · exact huv)
  simpa using h

theorem card_face_phenom (T W H : ℕ) :
    #(univ.filter (fun u : BoxV 3 ![T + 1, W, H] => (u 2 : ℕ) = 0)) ≤ (T + 1) * W := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter (fun u : BoxV 3 ![T + 1, W, H] => (u 2 : ℕ) = 0))
    (t := (univ : Finset (Fin (T + 1) × Fin W))) (fun u => ((u 0 : Fin (T + 1)), (u 1 : Fin W)))
    (by intro u _; exact Finset.mem_coe.mpr (Finset.mem_univ _)) (by
      intro u hu v hv huv
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu hv
      have h1 := congrArg Prod.fst huv
      have h2 := congrArg Prod.snd huv
      funext i
      fin_cases i
      · exact h1
      · exact h2
      · exact Fin.ext (hu.trans hv.symm))
  simpa using h

theorem rhoOf_nonneg (ps p : ℝ) : 0 ≤ rhoOf ps p := Real.sqrt_nonneg _

theorem rhoOf_le_one {ps p : ℝ} (hp0 : 0 < p) (hp : p ≤ ps) (hps : ps ≤ 1 / 2) : rhoOf ps p ≤ 1 := by
  unfold rhoOf
  rw [Real.sqrt_le_one]
  have hps0 : 0 < ps := lt_of_lt_of_le hp0 hp
  have hden : 0 < ps * (1 - ps) := mul_pos hps0 (by linarith)
  rw [div_le_one hden]
  nlinarith

/-- The bound with the face size replaced by an upper bound. -/
theorem bound_of_face {face F : ℕ} (hface : face ≤ F) {K0 lam rho B : ℝ} (hK0 : 0 ≤ K0) (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (e : ℕ)
    (hB : B ≤ face * K0 * (lam * rho) ^ e / (1 - lam * rho)) :
    B ≤ F * K0 * (lam * rho) ^ e / (1 - lam * rho) := by
  have hlr : lam * rho < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hlam0 hrho1) hlam1
  have hpos : 0 < 1 - lam * rho := by linarith
  refine le_trans hB ?_
  apply div_le_div_of_nonneg_right _ hpos.le
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg hlam0 hrho0) e)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hface) hK0

end QEC
