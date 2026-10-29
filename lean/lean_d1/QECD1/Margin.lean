import QECD1.Transfer

/-!
# Margin in the additive constant `off`

The λ-trick constant of the 3D lemma is `off = (1 + κ) D ν = 30` (`Const.off_val`). Any extra constant in the 3D
proof enlarges it. At `λ = 0.014`, `s = 0.007` the transfer ratio is about 0.8927 at `off = 30` (at most
0.9, `r3_le`) and stays at most 0.95 for every `off ≤ 34`:

* `exp_off34_le`: `e^{0.476} ≤ 1.609634`;
* `ratio_off_num`: `Jbar2 · 1.609634 · ε* · F0s ≤ 0.95` (value 0.9441);
* `r_off_le`: `Jbar2 · e^{λ off} ε* · F0s ≤ 0.95` for `off ≤ 34`;
* `transfer3_off`: the 3D transfer with the per-family factor `e^{λ off} ε*`, `off ≤ 34`: at most `20 topB`.

(`off = 35` gives 0.9574.)
-/

namespace QECD1

def eoff34Up : ℚ := 1609634 / 1000000

theorem exp_off34_le : Real.exp (lam * 34) ≤ (eoff34Up : ℝ) := by
  have h := Real.exp_bound (x := 119 / 250) (by norm_num [abs_of_pos]) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [eoff34Up, lam]
  linarith [h.1, h.2]

theorem ratio_off_num : Jbar2 * (eoff34Up : ℝ) * (37 / 2000000) * F0s ≤ 19 / 20 := by
  unfold Jbar2 F0s
  norm_num [qUpT, qLoT, qmUp, qmLo, qpUp, qpLo, eoff34Up]

/-- **Margin in `off`**: the ratio stays at most 0.95 for every `off ≤ 34`. -/
theorem r_off_le (off : ℝ) (hoff : off ≤ 34) : Jbar2 * (Real.exp (lam * off) * eps) * F0s ≤ 19 / 20 := by
  have hlam : 0 ≤ lam := by norm_num [lam]
  have h1 : Real.exp (lam * off) ≤ (eoff34Up : ℝ) :=
    le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hoff hlam)) exp_off34_le
  have h2 : Jbar2 * (Real.exp (lam * off) * eps) * F0s ≤ Jbar2 * ((eoff34Up : ℝ) * eps) * F0s := by
    have := mul_le_mul_of_nonneg_right h1 eps_nonneg
    have := mul_le_mul_of_nonneg_left this Jbar2_nonneg
    exact mul_le_mul_of_nonneg_right this F0s_nonneg
  have h3 := ratio_off_num
  have e : (37 / 2000000 : ℝ) = eps := rfl
  rw [e] at h3
  have h4 : Jbar2 * ((eoff34Up : ℝ) * eps) * F0s = Jbar2 * (eoff34Up : ℝ) * eps * F0s := by ring
  linarith

/-- **The 3D transfer with `off ≤ 34`**. -/
theorem transfer3_off {FK Top : Type} [DecidableEq FK] [DecidableEq Top] (off : ℝ) (hoff : off ≤ 34)
    (E : Encoding3DRooted FK) (exitF : FK → V3) (tw : V3 → Top → ℝ) (tok : V3 → Top → Prop) (topB : ℝ)
    (htopB : 0 ≤ topB) (hw : ∀ k, 0 ≤ E.w k) (htw : ∀ c t, 0 ≤ tw c t)
    (hT : ∀ (c : V3) (T : Finset Top), (∀ t ∈ T, tok c t) → ∑ t ∈ T, tw c t ≤ topB)
    (c : V3) (S : Finset (List (V3 × FK) × Top))
    (hS : ∀ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).TailOK c x.1 x.2) :
    ∑ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).tailW (Real.exp (lam * off) * eps) c x.1 x.2 ≤
      20 * topB := by
  have hC : 0 ≤ Real.exp (lam * off) * eps := mul_nonneg (Real.exp_pos _).le eps_nonneg
  have hr := r_off_le off hoff
  have h := (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).transfer (Real.exp (lam * off) * eps) Jbar2 F0s
    topB hC Jbar2_nonneg F0s_nonneg htopB (fun _ _ => (Real.exp_pos _).le) hw htw
    (fun c E hE => landing3 c E hE) (fun e K hK => famB3_rooted E e K hK) hT (by linarith) c S hS
  have h1 : 0 < 1 - Jbar2 * (Real.exp (lam * off) * eps) * F0s := by linarith
  have h2 : topB / (1 - Jbar2 * (Real.exp (lam * off) * eps) * F0s) ≤ 20 * topB := by
    rw [div_le_iff₀ h1]
    nlinarith
  linarith

end QECD1
