import QECML.MonoSize

/-!
# Independence of events that depend on disjoint sets of edges

Under the product weight `bernProd q` (any real `q`), an event that depends only on the coordinates in `J` and one
that depends only on the coordinates outside `J` have probability of intersection equal to the product
(`prob_and_of_split`). By induction, events with pairwise disjoint supports multiply (`prob_forall_eq_prod`). This
is the independence used by the per-block hypothesis (H) of the auxiliary decoder.
-/

open Finset

namespace QECML

open Classical in
/-- The probability of an event under a weight function (finite sum, classical decidability). -/
noncomputable def prob {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  ∑ ω, if A ω then P ω else 0

theorem prob_congr {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) {A B : Ω → Prop} (h : ∀ ω, A ω ↔ B ω) :
    prob P A = prob P B := by
  have : A = B := funext fun ω => propext (h ω)
  rw [this]

theorem prob_nonneg {Ω : Type*} [Fintype Ω] {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (A : Ω → Prop) :
    0 ≤ prob P A := by
  classical
  unfold prob
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [hP ω]

theorem prob_true {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) :
    prob (bernProd q) (fun _ : ι → ZMod 2 => True) = 1 := by
  simp [prob, sum_bernProd]

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two events supported on complementary coordinate sets are independent under `bernProd q`. -/
theorem prob_and_of_split (q : ℝ) (J : ι → Prop) (A B : (ι → ZMod 2) → Prop)
    (hA : ∀ e e', (∀ i, J i → e i = e' i) → (A e ↔ A e'))
    (hB : ∀ e e', (∀ i, ¬ J i → e i = e' i) → (B e ↔ B e')) :
    prob (bernProd q) (fun e => A e ∧ B e) = prob (bernProd q) A * prob (bernProd q) B := by
  classical
  let σ : ι ≃ {i // J i} ⊕ {i // ¬ J i} := (Equiv.sumCompl J).symm
  let glue : ({i // J i} → ZMod 2) → ({i // ¬ J i} → ZMod 2) → (ι → ZMod 2) :=
    fun a b i => Sum.elim a b (σ i)
  have hAe : ∀ e : ι → ZMod 2, A e ↔ A (glue (fun j => e (σ.symm (.inl j))) 0) := fun e =>
    hA _ _ fun i hi => by
      simp only [glue, σ, Equiv.sumCompl_symm_apply_of_pos hi, Sum.elim_inl, Equiv.symm_symm,
        Equiv.sumCompl_apply_inl]
  have hBe : ∀ e : ι → ZMod 2, B e ↔ B (glue 0 (fun j => e (σ.symm (.inr j)))) := fun e =>
    hB _ _ fun i hi => by
      simp only [glue, σ, Equiv.sumCompl_symm_apply_of_neg hi, Sum.elim_inr, Equiv.symm_symm,
        Equiv.sumCompl_apply_inr]
  let fA : ({i // J i} → ZMod 2) → ℝ := fun a => if A (glue a 0) then 1 else 0
  let fB : ({i // ¬ J i} → ZMod 2) → ℝ := fun b => if B (glue 0 b) then 1 else 0
  have hsplit := sum_bernProd_split σ q
  have eAB : prob (bernProd q) (fun e => A e ∧ B e) =
      ∑ a, ∑ b, bernProd q a * bernProd q b * (fA a * fB b) := by
    rw [← hsplit (fun a b => fA a * fB b)]
    unfold prob
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [fA, fB, ← hAe e, ← hBe e]
    by_cases h1 : A e <;> by_cases h2 : B e <;> simp [h1, h2]
  have eA : prob (bernProd q) A = ∑ a, bernProd q a * fA a := by
    have h := hsplit (fun a _ => fA a)
    unfold prob
    rw [show (∑ e, if A e then bernProd q e else 0) =
        ∑ e : ι → ZMod 2, bernProd q e * fA (fun j => e (σ.symm (.inl j))) from
      Finset.sum_congr rfl fun e _ => by simp only [fA, ← hAe e]; split_ifs <;> simp, h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (∑ b, bernProd q a * bernProd q b * fA a) = bernProd q a * fA a * ∑ b, bernProd q b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring, sum_bernProd, mul_one]
  have eB : prob (bernProd q) B = ∑ b, bernProd q b * fB b := by
    have h := hsplit (fun _ b => fB b)
    unfold prob
    rw [show (∑ e, if B e then bernProd q e else 0) =
        ∑ e : ι → ZMod 2, bernProd q e * fB (fun j => e (σ.symm (.inr j))) from
      Finset.sum_congr rfl fun e _ => by simp only [fB, ← hBe e]; split_ifs <;> simp, h,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (∑ a, bernProd q a * bernProd q b * fB b) = bernProd q b * fB b * ∑ a, bernProd q a by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring, sum_bernProd, mul_one]
  rw [eAB, eA, eB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Events with pairwise disjoint supports are independent under `bernProd q`. -/
theorem prob_forall_eq_prod {β : Type*} [DecidableEq β] (q : ℝ) (S : Finset β) (J : β → ι → Prop)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → ∀ i, J b i → ¬ J b' i) (A : β → (ι → ZMod 2) → Prop)
    (hA : ∀ b ∈ S, ∀ e e', (∀ i, J b i → e i = e' i) → (A b e ↔ A b e')) :
    prob (bernProd q) (fun e => ∀ b ∈ S, A b e) = ∏ b ∈ S, prob (bernProd q) (A b) := by
  induction S using Finset.induction_on with
  | empty => simp [prob, sum_bernProd]
  | insert b0 S hb0 ih =>
    rw [Finset.prod_insert hb0,
      ← ih (fun b hb b' hb' hne => hdisj b (mem_insert_of_mem hb) b' (mem_insert_of_mem hb') hne)
        (fun b hb => hA b (mem_insert_of_mem hb))]
    rw [prob_congr _ (B := fun e => A b0 e ∧ ∀ b ∈ S, A b e) (fun e => Finset.forall_mem_insert _ _ _)]
    refine prob_and_of_split q (J b0) _ _ (hA b0 (mem_insert_self _ _)) fun e e' h => ?_
    refine forall₂_congr fun b hb => hA b (mem_insert_of_mem hb) e e' fun i hi => h i ?_
    exact hdisj b (mem_insert_of_mem hb) b0 (mem_insert_self _ _) (fun hbb => hb0 (hbb ▸ hb)) i hi

end Split

end QECML
