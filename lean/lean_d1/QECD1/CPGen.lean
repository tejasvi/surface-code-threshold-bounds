import Mathlib

/-!
# Clopper–Pearson arithmetic and the validity of an acceptance rule (generic)

The 2D modules `ClopperPearson`, `CPConfidence` (generic part) and `binomCDF_mono_k`, unchanged up to names, so that the
3D development can state its certified wrapper (this development imports only Mathlib).

* `binomCDF n k p = ∑_{j ≤ k} C(n,j) p^j (1-p)^(n-j)`, the binomial lower tail. For `p = a/b` and `α = c/d`,
  `cpCheck n k a b c d` compares the integers `d ∑_{j ≤ k} C(n,j) a^j (b-a)^(n-j)` and `c b^n`; `cpCheck_sound`
  turns a successful check into `binomCDF n k (a/b) ≤ c/d`. The check is a closed Boolean term, evaluated by
  `decide +kernel` (GMP arithmetic on literals). `cpCheckGt_sound` is the reverse check.
* `binomCDF_antitoneOn`: `F(k; n, ·)` is antitone on `[0, 1]`; `binomCDF_mono_k`: monotone in `k`.
* `cp_confidence` (Bonferroni): on a finite probability space, if the count of type `t` is Binomial(`n`, `ε t`), the
  probability that some type has a true rate above `ε̂` and yet at most `k` bad samples is at most `|T| α`, where
  `F(k; n, ε̂) ≤ α`. `accept_bad_le`: acceptance with a true rate above `ε̂` lies in that event.
-/

open Finset

namespace QECD1

/-- The binomial lower tail `F(k; n, p) = ∑_{j ≤ k} C(n,j) p^j (1-p)^(n-j)`. -/
noncomputable def binomCDF (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- Binomial coefficient through the falling factorial (`j` kernel steps). -/
def chooseF (n j : ℕ) : ℕ := n.descFactorial j / j.factorial

theorem chooseF_eq (n j : ℕ) : chooseF n j = n.choose j :=
  (Nat.choose_eq_descFactorial_div_factorial n j).symm

/-- `cpNum n a b k = ∑_{j ≤ k} C(n,j) a^j (b-a)^(n-j)`, by recursion on `k`. -/
def cpNum (n a b : ℕ) : ℕ → ℕ
  | 0 => chooseF n 0 * a ^ 0 * (b - a) ^ (n - 0)
  | k + 1 => cpNum n a b k + chooseF n (k + 1) * a ^ (k + 1) * (b - a) ^ (n - (k + 1))

theorem cpNum_eq (n a b k : ℕ) :
    cpNum n a b k = ∑ j ∈ range (k + 1), n.choose j * a ^ j * (b - a) ^ (n - j) := by
  induction k with
  | zero => simp [cpNum, chooseF_eq]
  | succ k ih => rw [cpNum, ih, Finset.sum_range_succ _ (k + 1), chooseF_eq]

/-- The integer check for `F(k; n, a/b) ≤ c/d`. -/
def cpCheck (n k a b c d : ℕ) : Bool := Nat.ble (d * cpNum n a b k) (c * b ^ n)

theorem cpCheck_sound {n k a b c d : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : cpCheck n k a b c d = true) : binomCDF n k ((a : ℝ) / b) ≤ (c : ℝ) / d := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hterm : ∀ j ∈ range (k + 1), (n.choose j : ℝ) * ((a : ℝ) / b) ^ j * (1 - (a : ℝ) / b) ^ (n - j) =
      ((n.choose j * a ^ j * (b - a) ^ (n - j) : ℕ) : ℝ) / (b : ℝ) ^ n := by
    intro j hj
    have hjn : j ≤ n := by
      simp only [Finset.mem_range] at hj
      omega
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hab, one_sub_div hbR.ne',
      div_pow, div_pow, show (b : ℝ) ^ n = (b : ℝ) ^ j * (b : ℝ) ^ (n - j) by
        rw [← pow_add, Nat.add_sub_cancel' hjn]]
    field_simp
  rw [binomCDF, Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, ← cpNum_eq,
    div_le_div_iff₀ (by positivity) hdR]
  have h' : ((d * cpNum n a b k : ℕ) : ℝ) ≤ ((c * b ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_ble_eq_true h
  push_cast at h'
  linarith

/-- `binomCDF n k (a/b)` as an integer over `b^n` (for `k ≤ n`, `a ≤ b`, `b > 0`). -/
theorem binomCDF_eq_cpNum {n k a b : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) :
    binomCDF n k ((a : ℝ) / b) = (cpNum n a b k : ℝ) / (b : ℝ) ^ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [binomCDF, cpNum_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by
    simp only [Finset.mem_range] at hj
    omega
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hab, one_sub_div hbR.ne',
    div_pow, div_pow, show (b : ℝ) ^ n = (b : ℝ) ^ j * (b : ℝ) ^ (n - j) by
      rw [← pow_add, Nat.add_sub_cancel' hjn]]
  field_simp

/-- The reverse integer check, for `c/d < F(k; n, a/b)`. -/
def cpCheckGt (n k a b c d : ℕ) : Bool := Nat.ble (c * b ^ n + 1) (d * cpNum n a b k)

theorem cpCheckGt_sound {n k a b c d : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : cpCheckGt n k a b c d = true) : (c : ℝ) / d < binomCDF n k ((a : ℝ) / b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [binomCDF_eq_cpNum hk hab hb, div_lt_div_iff₀ hdR (by positivity)]
  have h' : ((c * b ^ n : ℕ) : ℝ) < ((d * cpNum n a b k : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h)
  push_cast at h'
  linarith

theorem binomCDF_succ (n k : ℕ) (p : ℝ) :
    binomCDF n (k + 1) p = binomCDF n k p + (n.choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (n - (k + 1)) := by
  rw [binomCDF, binomCDF, Finset.sum_range_succ]

theorem binomCDF_nonneg {n k : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ binomCDF n k p :=
  Finset.sum_nonneg fun j _ => by
    have : 0 ≤ 1 - p := by linarith
    positivity

/-- The binomial lower tail is monotone in `k`. -/
theorem binomCDF_mono_k {n k k' : ℕ} {p : ℝ} (hk : k ≤ k') (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binomCDF n k p ≤ binomCDF n k' p := by
  unfold binomCDF
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (by omega)
  · intro j _ _
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

/-- Bonferroni form of a certificate's confidence. -/
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

end QECD1
