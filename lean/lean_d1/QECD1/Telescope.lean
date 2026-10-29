import QECD1.Weights

/-!
# Tilt telescoping: the family weight is dominated by the product of the move weights

The 2D family weight (TwoD/T2Sum, `wFamK`) carries the tilt `e^{μ |r0 - exit|₁ + s (exit_y - r0_y)}` of a family
from its landing root `r0` to its exit. The family automata weigh every step and link `v` by `ε e^{μ |v|₁ + s v_y}`,
and leaves by `ε` (untilted, since a leaf does not move the route). The exit is the root plus the sum of the step
and link offsets. So the tilt is at most the product of the per-move tilts: `ℓ1` is subadditive and the y-displacement
is additive. This is the tilt part of `Encoding3D.le` (`w k ≤ keyWt`).

* `l1_add_le`, `l1_sum_le`: `|Σ v|₁ ≤ Σ |v|₁`.
* `y_sum`: `(Σ v)_y = Σ v_y`.
* `tilt_telescope`: for `μ ≥ 0`, `e^{μ |Σ v|₁ + s (Σ v)_y} ≤ Π e^{μ |v|₁ + s v_y}`.
* `tw_telescope`: with the T2 weights, `ε^m e^{λ |Σ v|₁ + s (Σ v)_y} ≤ Π tw v` for `m` moves.
-/

namespace QECD1

theorem l1_add_le (a b : V3) : l1 (a + b) ≤ l1 a + l1 b := by
  simp only [l1, Prod.fst_add, Prod.snd_add]
  have h1 := Int.natAbs_add_le a.1 b.1
  have h2 := Int.natAbs_add_le a.2.1 b.2.1
  have h3 := Int.natAbs_add_le a.2.2 b.2.2
  omega

theorem l1_zero : l1 (0 : V3) = 0 := rfl

theorem l1_sum_le : ∀ vs : List V3, l1 vs.sum ≤ (vs.map l1).sum
  | [] => by simp [l1_zero]
  | v :: vs => by
    simp only [List.sum_cons, List.map_cons]
    exact le_trans (l1_add_le v vs.sum) (Nat.add_le_add_left (l1_sum_le vs) _)

theorem y_sum : ∀ vs : List V3, vs.sum.2.2 = (vs.map fun v => v.2.2).sum
  | [] => rfl
  | v :: vs => by
    simp only [List.sum_cons, List.map_cons, Prod.snd_add]
    rw [y_sum vs]

theorem exp_list_sum (f : V3 → ℝ) : ∀ vs : List V3, Real.exp (vs.map f).sum = (vs.map fun v => Real.exp (f v)).prod
  | [] => by simp
  | v :: vs => by
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    rw [Real.exp_add, exp_list_sum f vs]

theorem map_sum_lin (μ s : ℝ) : ∀ vs : List V3, ((vs.map fun v => μ * l1 v + s * v.2.2).sum) =
    μ * (((vs.map l1).sum : ℕ) : ℝ) + s * (((vs.map fun v => v.2.2).sum : ℤ) : ℝ)
  | [] => by simp
  | v :: vs => by
    simp only [List.map_cons, List.sum_cons]
    rw [map_sum_lin μ s vs]
    push_cast
    ring

/-- **Tilt telescoping.** -/
theorem tilt_telescope (μ s : ℝ) (hμ : 0 ≤ μ) (vs : List V3) :
    Real.exp (μ * l1 vs.sum + s * vs.sum.2.2) ≤ (vs.map fun v => Real.exp (μ * l1 v + s * v.2.2)).prod := by
  rw [← exp_list_sum (fun v => μ * l1 v + s * v.2.2) vs]
  apply Real.exp_le_exp.2
  have h1 : (l1 vs.sum : ℝ) ≤ ((vs.map l1).sum : ℕ) := by exact_mod_cast l1_sum_le vs
  have h2 : (vs.sum.2.2 : ℝ) = (((vs.map fun v => v.2.2).sum : ℤ) : ℝ) := by rw [y_sum]
  rw [map_sum_lin μ s vs, h2]
  have := mul_le_mul_of_nonneg_left h1 hμ
  linarith

theorem prod_tw : ∀ vs : List V3,
    (vs.map tw).prod = eps ^ vs.length * (vs.map fun v => Real.exp (lam * l1 v + sT * v.2.2)).prod
  | [] => by simp
  | v :: vs => by
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [prod_tw vs]
    unfold tw
    ring

/-- **With the T2 weights**: `ε^m e^{λ |Σ v|₁ + s (Σ v)_y} ≤ Π tw v` over the `m` moves `vs`. -/
theorem tw_telescope (vs : List V3) :
    eps ^ vs.length * Real.exp (lam * l1 vs.sum + sT * vs.sum.2.2) ≤ (vs.map tw).prod := by
  have hlam : 0 ≤ lam := by norm_num [lam]
  have h := tilt_telescope lam sT hlam vs
  rw [prod_tw]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg eps_nonneg _)

end QECD1
