import QECML.Simulation

/-!
# The ML failure probability is non-decreasing in `q` on `[0, 1/2]`

For `0 ≤ q ≤ q' ≤ 1/2`, let `N` be i.i.d. Bernoulli(`r`) with
`r = (q' - q) / (1 - 2q)`, independent of `E ∼ Bern(q)`; then `E + N ∼ Bern(q')`. The randomized decoder
`s ↦ ML_{q'}(s + syn N) - cls N` at rate `q` fails exactly when `ML_{q'}` fails on `E + N`. Stated for any code whose
syndrome and class maps are additive, then for the planar code.
-/

open Finset

namespace QECML

section MonoQ

variable {ι S C : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] [AddCommGroup S]
  [Fintype C] [DecidableEq C] [AddCommGroup C] [Nonempty C]

/-- Adding an independent Bernoulli(`r`) noise to Bernoulli(`q`) errors gives Bernoulli(`q + r - 2 q r`) errors,
as a pushforward identity of finite sums. -/
theorem sum_bernProd_add (q r : ℝ) (f : (ι → ZMod 2) → ℝ) :
    ∑ e, ∑ n, bernProd q e * bernProd r n * f (e + n) = ∑ e', bernProd (q + r - 2 * q * r) e' * f e' := by
  have hinv : ∀ e n : ι → ZMod 2, e + n + n = e := fun e n => by
    funext i
    simp [add_assoc, zmod2_add_self]
  rw [Finset.sum_comm]
  have h1 : ∀ n : ι → ZMod 2, ∑ e, bernProd q e * bernProd r n * f (e + n) =
      ∑ e', bernProd q (e' + n) * bernProd r n * f e' := by
    intro n
    exact Fintype.sum_equiv (Equiv.addRight n) _ _ (fun e => by simp [hinv])
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [← bernProd_conv q r e', Finset.sum_mul]

/-- Monotonicity in `q` for any code with additive syndrome and class maps. (The proof does not need any lower
bound on `q`.) -/
theorem pML_mono_q (syn : (ι → ZMod 2) →+ S) (cls : (ι → ZMod 2) →+ C) {q q' : ℝ}
    (hqq' : q ≤ q') (hq' : q' ≤ 1 / 2) :
    pML (bernProd q) syn cls ≤ pML (bernProd q') syn cls := by
  rcases eq_or_lt_of_le (hqq'.trans hq') with hq2 | hq2
  · -- q = 1/2 forces q' = q
    have : q' = q := le_antisymm (hq'.trans hq2.symm.le) hqq'
    rw [this]
  · set r := (q' - q) / (1 - 2 * q) with hr
    have hpos : 0 < 1 - 2 * q := by linarith
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one hpos]
      linarith
    have hq'eq : q + r - 2 * q * r = q' := by
      have hmul : r * (1 - 2 * q) = q' - q := by
        rw [hr]
        exact div_mul_cancel₀ _ hpos.ne'
      linear_combination hmul
    refine pML_le_of_sim (bernProd q) syn cls (bernProd q') syn cls (bernProd r)
      (bernProd_nonneg hr0 hr1) (sum_bernProd r) (fun e n => e + n) ?_ (fun s n => s + syn n) ?_
      (fun n => cls n) ?_
    · intro f
      rw [← hq'eq]
      exact sum_bernProd_add q r f
    · intro e n
      exact map_add syn e n
    · intro e n
      exact map_add cls e n

end MonoQ

/-- Monotonicity in `q` for the planar code with `w + 1` columns and `h + 1` rows. -/
theorem pMLPlanar_mono_q (w h : ℕ) {q q' : ℝ} (hqq' : q ≤ q') (hq' : q' ≤ 1 / 2) :
    pMLPlanar w h q ≤ pMLPlanar w h q' :=
  pML_mono_q (psyn w h) (pcls w h) hqq' hq'

end QECML
