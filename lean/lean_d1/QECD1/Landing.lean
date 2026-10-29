import Mathlib

/-!
# The 3D landing sum

For `0 ≤ q < 1` and every finite set `S` of offsets `v ∈ ℤ³` with `|v|∞ ≥ 17`,

  `Σ_{v ∈ S} q^{|v|₁} ≤ ((1 + q)/(1 - q))³ - (Σ_{|k| ≤ 16} q^{|k|})³`   (`landing_le`),

because `S` lies in a box minus the box `|v|∞ ≤ 16`, the box sums factorize into cubes of 1D sums (`sum_box`), and
the 1D sum is `(1 + q - 2 q^{K+1})/(1 - q)` (`S1_eq`). With `q = e^{-λ}` this is the landing sum `Jbd` of the T2
transfer (jumps of block distance at least `a1 + 2 - D = 17`).
-/

namespace QECD1

/-- Integer offsets of the 3D block lattice. -/
abbrev V3 := ℤ × ℤ × ℤ

/-- `ℓ1` norm. -/
def l1 (v : V3) : ℕ := v.1.natAbs + v.2.1.natAbs + v.2.2.natAbs

/-- `ℓ∞` norm. -/
def linf (v : V3) : ℕ := max v.1.natAbs (max v.2.1.natAbs v.2.2.natAbs)

/-- The box `|v|∞ ≤ K`. -/
def box (K : ℕ) : Finset V3 :=
  Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K

theorem mem_Icc_iff_natAbs (a : ℤ) (K : ℕ) : a ∈ Finset.Icc (-(K : ℤ)) K ↔ a.natAbs ≤ K := by
  rw [Finset.mem_Icc]
  omega

theorem mem_box (v : V3) (K : ℕ) : v ∈ box K ↔ linf v ≤ K := by
  simp only [box, Finset.mem_product, mem_Icc_iff_natAbs, linf, max_le_iff]

/-- The 1D sum `Σ_{|k| ≤ K} q^{|k|}`. -/
noncomputable def S1 (q : ℝ) (K : ℕ) : ℝ := ∑ k ∈ Finset.Icc (-(K : ℤ)) K, q ^ k.natAbs

theorem Icc_succ (K : ℕ) :
    Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
      insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (Finset.Icc (-(K : ℤ)) K)) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem S1_succ (q : ℝ) (K : ℕ) : S1 q (K + 1) = S1 q K + 2 * q ^ (K + 1) := by
  unfold S1
  rw [Icc_succ, Finset.sum_insert, Finset.sum_insert]
  · have h1 : (-((K + 1 : ℕ) : ℤ)).natAbs = K + 1 := by omega
    have h2 : ((K + 1 : ℕ) : ℤ).natAbs = K + 1 := by omega
    rw [h1, h2]
    ring
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

theorem S1_zero (q : ℝ) : S1 q 0 = 1 := by
  simp [S1]

/-- Closed form of the 1D sum. -/
theorem S1_eq (q : ℝ) (hq : q ≠ 1) (K : ℕ) : S1 q K = (1 + q - 2 * q ^ (K + 1)) / (1 - q) := by
  have h1q : (1 : ℝ) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  induction K with
  | zero =>
    rw [S1_zero]
    field_simp
    ring
  | succ K ih =>
    rw [S1_succ, ih]
    field_simp
    ring

theorem S1_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) : S1 q K ≤ (1 + q) / (1 - q) := by
  rw [S1_eq q (ne_of_lt hq1) K]
  have h1q : (0 : ℝ) < 1 - q := by linarith
  apply div_le_div_of_nonneg_right _ h1q.le
  have : 0 ≤ q ^ (K + 1) := pow_nonneg hq0 _
  linarith

theorem S1_nonneg (q : ℝ) (hq0 : 0 ≤ q) (K : ℕ) : 0 ≤ S1 q K :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hq0 _

theorem S1_mono (q q' : ℝ) (hq0 : 0 ≤ q) (hqq : q ≤ q') (K : ℕ) : S1 q K ≤ S1 q' K :=
  Finset.sum_le_sum fun _ _ => pow_le_pow_left₀ hq0 hqq _

/-- Box sums factorize. -/
theorem sum_box (q : ℝ) (K : ℕ) : ∑ v ∈ box K, q ^ l1 v = S1 q K ^ 3 := by
  set A := Finset.Icc (-(K : ℤ)) K
  have h : ∑ v ∈ box K, q ^ l1 v = ∑ a ∈ A, ∑ y ∈ A ×ˢ A, q ^ a.natAbs * (q ^ y.1.natAbs * q ^ y.2.natAbs) := by
    unfold box
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [l1, pow_add, mul_assoc]
  rw [h]
  have h2 : ∀ a ∈ A, ∑ y ∈ A ×ˢ A, q ^ a.natAbs * (q ^ y.1.natAbs * q ^ y.2.natAbs) =
      q ^ a.natAbs * (S1 q K * S1 q K) := by
    intro a _
    rw [← Finset.mul_sum, Finset.sum_product, S1, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  show S1 q K * (S1 q K * S1 q K) = S1 q K ^ 3
  ring

/-- **Landing sum**: every finite set of offsets at `ℓ∞` distance at least 17. -/
theorem landing_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (S : Finset V3) (hS : ∀ v ∈ S, 17 ≤ linf v) :
    ∑ v ∈ S, q ^ l1 v ≤ ((1 + q) / (1 - q)) ^ 3 - S1 q 16 ^ 3 := by
  set K := max 16 (S.sup linf)
  have hsub : S ⊆ box K \ box 16 := by
    intro v hv
    rw [Finset.mem_sdiff, mem_box, mem_box]
    refine ⟨le_trans (Finset.le_sup hv) (le_max_right _ _), ?_⟩
    have := hS v hv
    omega
  have h16 : box 16 ⊆ box K := by
    intro v hv
    rw [mem_box] at hv ⊢
    exact le_trans hv (le_max_left _ _)
  have hnn : ∀ v ∈ box K \ box 16, 0 ≤ q ^ l1 v := fun _ _ => pow_nonneg hq0 _
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ => hnn v hv)
  rw [Finset.sum_sdiff_eq_sub h16, sum_box, sum_box] at h1
  have h2 : S1 q K ^ 3 ≤ ((1 + q) / (1 - q)) ^ 3 :=
    pow_le_pow_left₀ (S1_nonneg q hq0 K) (S1_le q hq0 hq1 K) 3
  linarith

end QECD1
