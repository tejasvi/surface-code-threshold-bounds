import QECML.CPInstance

/-!
# Validity of the Clopper–Pearson acceptance rule

* `hasDerivAt_binomCDF`: `d/dp F(k; n, p) = -(n - k) C(n,k) p^k (1-p)^(n-k-1)` for `k < n`.
* `binomCDF_antitoneOn`: `F(k; n, ·)` is antitone on `[0, 1]`. So `F(k; n, ε*) ≤ α` gives `F(k; n, ε) ≤ α` for every
  true rate `ε ≥ ε*`.
* `cp_confidence` (Bonferroni): on any finite probability space, if the count of type `t` is Binomial(`n`, `ε t`)
  (hypothesis `hlaw`, the binomial model of the Monte Carlo), then the probability that some type has a true rate
  above `ε̂` and yet at most `k` bad samples is at most `|T| α`, where `F(k; n, ε̂) ≤ α`.
* `cert_confidence_A`, `cert_confidence_B`: the registered designs. Whatever the true rates, the probability of
  accepting (every type has at most `k` bad samples) while some true rate exceeds `ε* = 5e-4` is at most `1e-9`.
-/

open Finset

namespace QECML

theorem binomCDF_succ (n k : ℕ) (p : ℝ) :
    binomCDF n (k + 1) p = binomCDF n k p + (n.choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (n - (k + 1)) := by
  rw [binomCDF, binomCDF, Finset.sum_range_succ]

theorem binomCDF_nonneg {n k : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ binomCDF n k p :=
  Finset.sum_nonneg fun j _ => by
    have : 0 ≤ 1 - p := by linarith
    positivity

/-- The derivative of the binomial lower tail in `p`. -/
theorem hasDerivAt_binomCDF {n k : ℕ} (hk : k < n) (p : ℝ) :
    HasDerivAt (binomCDF n k) (-(((n - k : ℕ) : ℝ) * n.choose k * p ^ k * (1 - p) ^ (n - k - 1))) p := by
  induction k with
  | zero =>
    have h2 := ((hasDerivAt_id' p).const_sub (1 : ℝ)).pow n
    have hf : binomCDF n 0 = (fun x : ℝ => 1 - x) ^ n := by
      funext x
      simp [binomCDF]
    rw [hf]
    refine h2.congr_deriv ?_
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero]
    ring
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = k + 2 + m := ⟨n - (k + 2), by omega⟩
    have ihk := ih (by omega)
    have hT : HasDerivAt (fun x : ℝ => ((k + 2 + m).choose (k + 1) : ℝ) * (x ^ (k + 1) * (1 - x) ^ (m + 1)))
        (((k + 2 + m).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * p ^ (k + 1 - 1) * (1 - p) ^ (m + 1) +
          p ^ (k + 1) * (((m + 1 : ℕ) : ℝ) * (1 - p) ^ (m + 1 - 1) * -1))) p :=
      ((hasDerivAt_pow (k + 1) p).mul (((hasDerivAt_id' p).const_sub (1 : ℝ)).pow (m + 1))).const_mul _
    have hf : binomCDF (k + 2 + m) (k + 1) = fun x => binomCDF (k + 2 + m) k x +
        ((k + 2 + m).choose (k + 1) : ℝ) * (x ^ (k + 1) * (1 - x) ^ (m + 1)) := by
      funext x
      rw [binomCDF_succ, show k + 2 + m - (k + 1) = m + 1 by omega]
      ring
    rw [hf]
    refine (ihk.add hT).congr_deriv ?_
    have e1 : k + 2 + m - k = m + 2 := by omega
    have e2 : k + 2 + m - k - 1 = m + 1 := by omega
    have e3 : k + 2 + m - (k + 1) = m + 1 := by omega
    have e4 : k + 2 + m - (k + 1) - 1 = m := by omega
    have hc : ((k + 2 + m).choose (k + 1) : ℝ) * ((k : ℝ) + 1) = ((k + 2 + m).choose k : ℝ) * ((m : ℝ) + 2) := by
      have h := Nat.choose_succ_right_eq (k + 2 + m) k
      rw [e1] at h
      exact_mod_cast h
    rw [e2, e1, e4, e3, Nat.add_sub_cancel, Nat.add_sub_cancel]
    push_cast
    linear_combination (p ^ k * (1 - p) ^ (m + 1)) * hc

/-- The binomial lower tail is antitone in `p` on `[0, 1]` (for `k < n`). -/
theorem binomCDF_antitoneOn {n k : ℕ} (hk : k < n) : AntitoneOn (binomCDF n k) (Set.Icc 0 1) := by
  have hd := hasDerivAt_binomCDF hk
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun p _ => (hd p).continuousAt.continuousWithinAt)
    (fun p _ => (hd p).differentiableAt.differentiableWithinAt) fun p hp => ?_
  rw [interior_Icc] at hp
  rw [(hd p).deriv]
  have h1 : 0 ≤ 1 - p := by linarith [hp.2]
  have h0 : 0 ≤ p := hp.1.le
  have : 0 ≤ ((n - k : ℕ) : ℝ) * n.choose k * p ^ k * (1 - p) ^ (n - k - 1) := by positivity
  linarith

/-- Bonferroni form of the certificate's confidence. -/
theorem cp_confidence {Ω T : Type*} [Fintype Ω] [Fintype T] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    {n k : ℕ} (hk : k < n) (K : T → Ω → ℕ) (ε : T → ℝ) (hε : ∀ t, ε t ≤ 1)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) = (n.choose j : ℝ) * ε t ^ j * (1 - ε t) ^ (n - j))
    {εhat α : ℝ} (hεhat0 : 0 ≤ εhat) (hεhat1 : εhat ≤ 1) (hcp : binomCDF n k εhat ≤ α) :
    (∑ ω, if ∃ t, εhat < ε t ∧ K t ω ≤ k then P ω else 0) ≤ Fintype.card T * α := by
  have hα : 0 ≤ α := (binomCDF_nonneg hεhat0 hεhat1).trans hcp
  have hper : ∀ t, (∑ ω, if εhat < ε t ∧ K t ω ≤ k then P ω else 0) ≤ α := by
    intro t
    by_cases ht : εhat < ε t
    · have hsum : (∑ ω, if εhat < ε t ∧ K t ω ≤ k then P ω else 0) = binomCDF n k (ε t) := by
        simp only [ht, true_and]
        rw [binomCDF, ← Finset.sum_congr rfl fun j _ => hlaw t j, Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_ite_eq]
        simp [Finset.mem_range]
      rw [hsum]
      exact (binomCDF_antitoneOn hk ⟨hεhat0, hεhat1⟩ ⟨by linarith, hε t⟩ ht.le).trans hcp
    · simp only [ht, false_and, ↓reduceIte, Finset.sum_const_zero]
      exact hα
  calc (∑ ω, if ∃ t, εhat < ε t ∧ K t ω ≤ k then P ω else 0)
      ≤ ∑ ω, ∑ t, if εhat < ε t ∧ K t ω ≤ k then P ω else 0 := by
        refine Finset.sum_le_sum fun ω _ => ?_
        have hnn : ∀ t ∈ (Finset.univ : Finset T),
            0 ≤ (if εhat < ε t ∧ K t ω ≤ k then P ω else 0) := fun t _ => by
          split_ifs
          · exact hP ω
          · exact le_rfl
        split_ifs with h
        · obtain ⟨t, ht⟩ := h
          have := Finset.single_le_sum hnn (Finset.mem_univ t)
          simpa [ht] using this
        · exact Finset.sum_nonneg hnn
    _ = ∑ t, ∑ ω, if εhat < ε t ∧ K t ω ≤ k then P ω else 0 := Finset.sum_comm
    _ ≤ ∑ _t : T, α := Finset.sum_le_sum fun t _ => hper t
    _ = Fintype.card T * α := by simp

/-- Acceptance with true rates above `ε*` is contained in the Bonferroni event. -/
theorem accept_bad_le {Ω T : Type*} [Fintype Ω] [Fintype T] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (K : T → Ω → ℕ)
    (ε : T → ℝ) (k : ℕ) (εs : ℝ) :
    (∑ ω, if (∀ t, K t ω ≤ k) ∧ (∃ t, εs < ε t) then P ω else 0) ≤
      ∑ ω, if ∃ t, εs < ε t ∧ K t ω ≤ k then P ω else 0 := by
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    obtain ⟨hall, t, ht⟩ := h1
    exact h2 ⟨t, ht, hall t⟩
  · exact hP ω
  · exact le_rfl

/-- **Confidence of design A** (`n = 1.2e5` per type, accept iff every one of the five types has at most 18 bad
blocks, `ε* = 5e-4`, `α = 2e-10` per type): under the binomial model `hlaw`, whatever the true rates `ε t`, the
probability of accepting while some true rate exceeds `ε*` is at most `1e-9`. -/
theorem cert_confidence_A {Ω T : Type*} [Fintype Ω] [Fintype T] (hT : Fintype.card T = 5) (P : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (K : T → Ω → ℕ) (ε : T → ℝ) (hε : ∀ t, ε t ≤ 1)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 120000 j : ℕ) : ℝ) * ε t ^ j * (1 - ε t) ^ (120000 - j)) :
    (∑ ω, if (∀ t, K t ω ≤ 18) ∧ (∃ t, 5e-4 < ε t) then P ω else 0) ≤ 1e-9 := by
  have h := cp_confidence P hP (n := 120000) (k := 18) (by norm_num) K ε hε hlaw (εhat := 5e-4) (α := 2e-10)
    (by norm_num) (by norm_num) cp_accept_A
  rw [hT] at h
  refine (accept_bad_le P hP K ε 18 5e-4).trans (h.trans ?_)
  norm_num

/-- **Confidence of design B** (`n = 8e4` per type, accept iff every type has at most 7 bad blocks). -/
theorem cert_confidence_B {Ω T : Type*} [Fintype Ω] [Fintype T] (hT : Fintype.card T = 5) (P : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (K : T → Ω → ℕ) (ε : T → ℝ) (hε : ∀ t, ε t ≤ 1)
    (hlaw : ∀ t j, (∑ ω, if K t ω = j then P ω else 0) =
      ((Nat.choose 80000 j : ℕ) : ℝ) * ε t ^ j * (1 - ε t) ^ (80000 - j)) :
    (∑ ω, if (∀ t, K t ω ≤ 7) ∧ (∃ t, 5e-4 < ε t) then P ω else 0) ≤ 1e-9 := by
  have h := cp_confidence P hP (n := 80000) (k := 7) (by norm_num) K ε hε hlaw (εhat := 5e-4) (α := 2e-10)
    (by norm_num) (by norm_num) cp_accept_B
  rw [hT] at h
  refine (accept_bad_le P hP K ε 7 5e-4).trans (h.trans ?_)
  norm_num

end QECML
