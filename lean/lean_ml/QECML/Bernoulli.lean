import QECML.ML

/-!
# Bernoulli product weights

Nonnegativity, total mass one, the XOR convolution `Bern(q) xor Bern(r) = Bern(q + r - 2 q r)`, and the splitting
of a product weight along an equivalence of the index set with a sum type.
-/

open Finset

namespace QECML

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ x : ZMod 2, f x = f 0 + f 1 :=
  Fin.sum_univ_two f

theorem bern_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (x : ZMod 2) : 0 ≤ bern q x := by
  unfold bern
  split_ifs <;> linarith

theorem sum_bern (q : ℝ) : ∑ x : ZMod 2, bern q x = 1 := by
  rw [sum_zmod2]
  simp [bern]

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- One-bit XOR convolution. -/
theorem bern_conv (q r : ℝ) (x : ZMod 2) :
    ∑ n : ZMod 2, bern q (x + n) * bern r n = bern (q + r - 2 * q * r) x := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [sum_zmod2]
  rcases zmod2_cases x with rfl | rfl <;> simp [bern, h11, h10] <;> ring

section Prod

variable {ι : Type*} [Fintype ι]

theorem bernProd_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (e : ι → ZMod 2) : 0 ≤ bernProd q e :=
  Finset.prod_nonneg fun i _ => bern_nonneg h0 h1 (e i)

variable [DecidableEq ι]

theorem sum_bernProd (q : ℝ) : ∑ e : ι → ZMod 2, bernProd q e = 1 := by
  unfold bernProd
  rw [← Fintype.prod_sum (fun (_ : ι) (x : ZMod 2) => bern q x)]
  simp [sum_bern]

/-- XOR convolution of product weights: if `E ∼ Bern(q)` and `N ∼ Bern(r)` are independent, then `E + N` has the
product law `Bern(q + r - 2 q r)`. -/
theorem bernProd_conv (q r : ℝ) (e : ι → ZMod 2) :
    ∑ n : ι → ZMod 2, bernProd q (e + n) * bernProd r n = bernProd (q + r - 2 * q * r) e := by
  unfold bernProd
  simp_rw [← Finset.prod_mul_distrib, Pi.add_apply]
  rw [← Fintype.prod_sum (fun (i : ι) (x : ZMod 2) => bern q (e i + x) * bern r x)]
  simp [bern_conv]

end Prod

/-- Splitting a product weight along an equivalence `ι ≃ ι₁ ⊕ ι₂`. -/
theorem bernProd_split {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂] (σ : ι ≃ ι₁ ⊕ ι₂) (q : ℝ)
    (e : ι → ZMod 2) :
    bernProd q e = bernProd q (fun i => e (σ.symm (.inl i))) * bernProd q (fun j => e (σ.symm (.inr j))) := by
  unfold bernProd
  rw [← Fintype.prod_sum_type (fun k => bern q (e (σ.symm k)))]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

end QECML
