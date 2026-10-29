import Mathlib

/-!
# Maximum-likelihood decoding: definitions, optimality, simulation, monotonicity in `q` (generic)

The generic part of the 2D modules `Defs`, `Bernoulli`, `ML`, `Simulation` and `MonoQ`, unchanged up to names, so that
the 3D code can use it (this development imports only Mathlib).

* `bern q`, `bernProd q`: i.i.d. Bernoulli(`q`) weights on configurations `ι → ZMod 2`.
* A decoding problem is a weight `P : Ω → ℝ` on a finite error space `Ω`, a syndrome map `syn : Ω → S` and a
  logical class map `cls : Ω → C`. Decoders: deterministic (`S → C`), with a finite random seed, randomized (a
  stochastic kernel), and decoders that output a correction (`pFailCorr`).
* `IsML`, `mlDec`, `pML`: maximum-likelihood decoding and the optimal failure probability.
* ML optimality: `pML_le_pFail`, `pML_le_pFailR`, `pML_le_pFailSeed`, `pML_le_pFailCorr`; every ML decoder has the
  failure probability `pML` (`pFail_eq_pML`).
* `pML_le_of_sim` (the simulation lemma): if problem 1 can simulate problem 2 with a random seed, then
  `pML₁ ≤ pML₂`.
* `pML_mono_q`: for additive syndrome and class maps, `pML` is non-decreasing in `q` on `[0, 1/2]`.
* `sum_bernProd_split`: a product weight splits along an equivalence `ι ≃ ι₁ ⊕ ι₂` of the index set.
-/

open Finset

namespace QECD1

/-! ## Bernoulli weights -/

/-- Weight of one bit under Bernoulli(`q`). -/
def bern (q : ℝ) (x : ZMod 2) : ℝ := if x = 0 then 1 - q else q

/-- The i.i.d. Bernoulli(`q`) weight of a configuration. -/
def bernProd {ι : Type*} [Fintype ι] (q : ℝ) (e : ι → ZMod 2) : ℝ := ∏ i, bern q (e i)

/-! ## Decoders and failure probabilities -/

section Decoding

variable {Ω S C : Type*} [Fintype Ω] [DecidableEq S] [DecidableEq C]

/-- Failure probability of a deterministic decoder `dec : S → C`. -/
def pFail (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (dec : S → C) : ℝ :=
  ∑ ω, if dec (syn ω) = cls ω then 0 else P ω

/-- Joint weight of the syndrome `s` and the class `c`. -/
def joint (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (s : S) (c : C) : ℝ :=
  ∑ ω, if syn ω = s ∧ cls ω = c then P ω else 0

/-- Maximum-likelihood decoders: every syndrome is decoded to a class of maximal joint weight (any tie rule). -/
def IsML (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (dec : S → C) : Prop :=
  ∀ s c, joint P syn cls s c ≤ joint P syn cls s (dec s)

/-- Failure probability of a decoder `dec r` whose seed `r` has law `ρ`, independently of the error. -/
def pFailSeed {R : Type*} [Fintype R] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (ρ : R → ℝ)
    (dec : R → S → C) : ℝ :=
  ∑ ω, ∑ r, if dec r (syn ω) = cls ω then 0 else P ω * ρ r

/-- A randomized decoder: for each syndrome `s`, a probability distribution `δ s` on the classes. -/
structure RDecoder (S C : Type*) [Fintype C] where
  /-- probability of answering `c` on syndrome `s` -/
  δ : S → C → ℝ
  nonneg : ∀ s c, 0 ≤ δ s c
  sum_one : ∀ s, ∑ c, δ s c = 1

/-- Failure probability of a randomized decoder. -/
def pFailR [Fintype C] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (D : RDecoder S C) : ℝ :=
  ∑ ω, P ω * (1 - D.δ (syn ω) (cls ω))

/-- Failure probability of a decoder that outputs a correction `corr s : Ω`: it fails when the correction has the
wrong syndrome, or when the residual `ω + corr (syn ω)` has a nonzero logical class. -/
def pFailCorr [AddCommGroup Ω] [Zero C] (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (corr : S → Ω) : ℝ :=
  ∑ ω, if syn (corr (syn ω)) = syn ω ∧ cls (ω + corr (syn ω)) = 0 then 0 else P ω

variable [Fintype C] [Nonempty C]

/-- A canonical ML decoder: for each syndrome, a maximiser of the joint weight chosen by classical choice. Every ML
decoder has the same failure probability (`pFail_eq_pML`). -/
noncomputable def mlDec (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) (s : S) : C :=
  Classical.choose (Finset.exists_max_image Finset.univ (joint P syn cls s) Finset.univ_nonempty)

/-- The optimal (maximum-likelihood) failure probability. -/
noncomputable def pML (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C) : ℝ :=
  pFail P syn cls (mlDec P syn cls)

end Decoding

/-! ## Optimality of maximum-likelihood decoding -/

section ML

variable {Ω S C : Type*} [Fintype Ω] [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
variable (P : Ω → ℝ) (syn : Ω → S) (cls : Ω → C)

/-- Regrouping a sum over configurations by syndrome and class. -/
theorem sum_mul_eq_sum_joint (f : S → C → ℝ) :
    ∑ ω, f (syn ω) (cls ω) * P ω = ∑ s, ∑ c, f s c * joint P syn cls s c := by
  rw [← Finset.sum_fiberwise Finset.univ (fun ω => (syn ω, cls ω)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
  rw [joint, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun ω hω => ?_
  · ext ω
    simp [Prod.ext_iff]
  · have h' : syn ω = s ∧ cls ω = c := by simpa [Prod.ext_iff] using hω
    rw [h'.1, h'.2]

/-- The weight decoded correctly by `dec` is `∑ s, joint s (dec s)`. -/
theorem sum_success_eq (dec : S → C) :
    (∑ ω, if dec (syn ω) = cls ω then P ω else 0) = ∑ s, joint P syn cls s (dec s) := by
  have h := sum_mul_eq_sum_joint P syn cls (fun s c => if dec s = c then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Finset.sum_ite_eq]

theorem pFail_eq (dec : S → C) :
    pFail P syn cls dec = ∑ ω, P ω - ∑ s, joint P syn cls s (dec s) := by
  rw [← sum_success_eq, pFail, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

theorem pFailR_eq (D : RDecoder S C) :
    pFailR P syn cls D = ∑ ω, P ω - ∑ s, ∑ c, D.δ s c * joint P syn cls s c := by
  rw [← sum_mul_eq_sum_joint, pFailR, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

variable [Nonempty C]

omit [Fintype S] in
theorem mlDec_isML : IsML P syn cls (mlDec P syn cls) := fun s c =>
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (joint P syn cls s)
    Finset.univ_nonempty)).2 c (Finset.mem_univ c)

/-- Every ML decoder has the failure probability `pML`. -/
theorem pFail_eq_pML {dec : S → C} (h : IsML P syn cls dec) : pFail P syn cls dec = pML P syn cls := by
  rw [pML, pFail_eq, pFail_eq]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  exact le_antisymm (mlDec_isML P syn cls s (dec s)) (h s (mlDec P syn cls s))

/-- ML optimality among deterministic decoders. -/
theorem pML_le_pFail (dec : S → C) : pML P syn cls ≤ pFail P syn cls dec := by
  rw [pML, pFail_eq, pFail_eq]
  gcongr with s
  exact mlDec_isML P syn cls s (dec s)

/-- ML optimality among randomized decoders (stochastic kernels). -/
theorem pML_le_pFailR (D : RDecoder S C) : pML P syn cls ≤ pFailR P syn cls D := by
  rw [pML, pFail_eq, pFailR_eq]
  gcongr with s
  calc ∑ c, D.δ s c * joint P syn cls s c
      ≤ ∑ c, D.δ s c * joint P syn cls s (mlDec P syn cls s) := by
        gcongr with c
        · exact D.nonneg s c
        · exact mlDec_isML P syn cls s c
    _ = joint P syn cls s (mlDec P syn cls s) := by rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- ML optimality among decoders with a finite random seed `r ∼ ρ`. -/
theorem pML_le_pFailSeed {R : Type*} [Fintype R] (ρ : R → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hρ1 : ∑ r, ρ r = 1)
    (dec : R → S → C) : pML P syn cls ≤ pFailSeed P syn cls ρ dec := by
  have h : pFailSeed P syn cls ρ dec = ∑ r, ρ r * pFail P syn cls (dec r) := by
    rw [pFailSeed, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pFail, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> ring
  rw [h]
  calc pML P syn cls = ∑ r, ρ r * pML P syn cls := by rw [← Finset.sum_mul, hρ1, one_mul]
    _ ≤ ∑ r, ρ r * pFail P syn cls (dec r) := by
        gcongr with r
        · exact hρ r
        · exact pML_le_pFail P syn cls (dec r)

/-- ML optimality among decoders that output a correction (for an additive class map and `P ≥ 0`). -/
theorem pML_le_pFailCorr [AddCommGroup Ω] [AddCommGroup C] (cls : Ω →+ C) (hP : ∀ ω, 0 ≤ P ω)
    (corr : S → Ω) : pML P syn cls ≤ pFailCorr P syn cls corr := by
  refine (pML_le_pFail P syn cls (fun s => -cls (corr s))).trans ?_
  rw [pFail, pFailCorr]
  gcongr with ω
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact hP ω
  · exfalso
    apply h1
    have h3 := h2.2
    rw [map_add] at h3
    exact neg_eq_of_add_eq_zero_left h3
  · exact le_rfl

end ML

/-! ## Bernoulli product weights -/

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

/-- A bit is `0` or `1` (as `Interior3.zmod2_cases`; restated here because this module imports only Mathlib). -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- One-bit XOR convolution. -/
theorem bern_conv (q r : ℝ) (x : ZMod 2) :
    ∑ n : ZMod 2, bern q (x + n) * bern r n = bern (q + r - 2 * q * r) x := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [sum_zmod2]
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> simp [bern, h11, h10] <;> ring

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

/-- Splitting a sum over configurations along an equivalence `ι ≃ ι₁ ⊕ ι₂` of the index set. -/
theorem sum_bernProd_split {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι]
    [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι ≃ ι₁ ⊕ ι₂) (q : ℝ)
    (G : (ι₁ → ZMod 2) → (ι₂ → ZMod 2) → ℝ) :
    ∑ e : ι → ZMod 2, bernProd q e * G (fun i => e (σ.symm (.inl i))) (fun j => e (σ.symm (.inr j))) =
      ∑ a : ι₁ → ZMod 2, ∑ b : ι₂ → ZMod 2, bernProd q a * bernProd q b * G a b := by
  let Φ : (ι → ZMod 2) ≃ (ι₁ → ZMod 2) × (ι₂ → ZMod 2) :=
    (Equiv.arrowCongr σ (Equiv.refl (ZMod 2))).trans (Equiv.sumArrowEquivProdArrow ι₁ ι₂ (ZMod 2))
  have hΦ : ∀ e, Φ e = ((fun i => e (σ.symm (.inl i))), (fun j => e (σ.symm (.inr j)))) := fun e => rfl
  rw [← Fintype.sum_prod_type' (fun a b => bernProd q a * bernProd q b * G a b)]
  refine Fintype.sum_equiv Φ _ _ (fun e => ?_)
  rw [hΦ, bernProd_split σ q e]

/-! ## The simulation lemma -/

/-- **Simulation.** Problem 1 can simulate problem 2 if there are a seed space `R` with law `ρ` and a map
`T : Ω₁ → R → Ω₂` that pushes `P₁ ⊗ ρ` to `P₂`, such that the syndrome of `T ω r` is a function `g` of the syndrome
of `ω` and of `r`, and the class of `T ω r` is the class of `ω` shifted by `k r`. Then the randomized decoder
`r, s ↦ ML₂ (g s r) - k r` for problem 1 fails exactly when ML fails on problem 2, so `pML₁ ≤ pML₂`. -/
theorem pML_le_of_sim {Ω₁ Ω₂ R S₁ S₂ C : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype R]
    [Fintype S₁] [DecidableEq S₁] [Fintype S₂] [DecidableEq S₂]
    [Fintype C] [DecidableEq C] [AddCommGroup C] [Nonempty C]
    (P₁ : Ω₁ → ℝ) (syn₁ : Ω₁ → S₁) (cls₁ : Ω₁ → C)
    (P₂ : Ω₂ → ℝ) (syn₂ : Ω₂ → S₂) (cls₂ : Ω₂ → C)
    (ρ : R → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hρ1 : ∑ r, ρ r = 1)
    (T : Ω₁ → R → Ω₂)
    (hT : ∀ f : Ω₂ → ℝ, ∑ ω, ∑ r, P₁ ω * ρ r * f (T ω r) = ∑ ω', P₂ ω' * f ω')
    (g : S₁ → R → S₂) (hg : ∀ ω r, syn₂ (T ω r) = g (syn₁ ω) r)
    (k : R → C) (hk : ∀ ω r, cls₂ (T ω r) = cls₁ ω + k r) :
    pML P₁ syn₁ cls₁ ≤ pML P₂ syn₂ cls₂ := by
  set D₂ := mlDec P₂ syn₂ cls₂
  refine (pML_le_pFailSeed P₁ syn₁ cls₁ ρ hρ hρ1 (fun r s => D₂ (g s r) - k r)).trans (le_of_eq ?_)
  have key : ∀ ω r, (D₂ (g (syn₁ ω) r) - k r = cls₁ ω) ↔ (D₂ (syn₂ (T ω r)) = cls₂ (T ω r)) := by
    intro ω r
    rw [hg, hk, sub_eq_iff_eq_add]
  have h := hT (fun ω' => if D₂ (syn₂ ω') = cls₂ ω' then 0 else 1)
  rw [pML, pFail, pFailSeed]
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [key ω r]

/-! ## Monotonicity in `q` -/

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

/-- **Monotonicity in `q`** for any code with additive syndrome and class maps: for `q ≤ q' ≤ 1/2`, `pML` at `q`
is at most `pML` at `q'` (degradation by an independent Bernoulli(`(q' - q)/(1 - 2q)`) noise). -/
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

end QECD1
