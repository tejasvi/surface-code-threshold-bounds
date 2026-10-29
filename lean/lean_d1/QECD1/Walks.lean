import QECD1.Landing

/-!
# Step offsets, marginals, the per-axis union bound and 1D witness walk counts

* `S0 = {v ∈ ℤ³ : 5 ≤ |v|∞ ≤ 8}` (the in-cluster step offsets for `D = 5`, `A0 = 8`); `card_S0 : |S0| = 4184`.
* `sum_marginal`: a sum over `S0` of a function of one coordinate is a sum over that coordinate weighted by the
  fibre sizes; `fiber_card`: the fibres along the first coordinate have `289` (for `5 ≤ |k| ≤ 8`) or `208`
  (for `|k| ≤ 4`) elements (`stepCount`).
* `span_indicator_le`: `[17 ≤ |z|∞] ≤ Σ_i [17 ≤ |z_i|]` (the union over the axes).
* `walkSum c z`: the number of `c`-step walks with steps in `S0`, started at first coordinate `z`, whose final first
  coordinate has absolute value at least `17` (defined by recursion over the steps); `walkSum_eq`: it equals the 1D
  count `Ncnt c z`, computed with the fibre sizes only. These are the counts `N_c(z)` of the witness mark.
-/

namespace QECD1

/-- The in-cluster step offsets for `D = 5`, `A0 = 8`. -/
def S0 : Finset V3 := (box 8).filter fun v => 5 ≤ linf v

theorem card_S0 : S0.card = 4184 := by decide +kernel

/-- The fibre sizes of `S0` along one coordinate. -/
def stepCount (k : ℤ) : ℕ := if k.natAbs ≤ 4 then 208 else if k.natAbs ≤ 8 then 289 else 0

theorem fiber_card : ∀ k ∈ Finset.Icc (-8 : ℤ) 8, (S0.filter fun v => v.1 = k).card = stepCount k := by
  decide +kernel

theorem S0_fst_mem : ∀ v ∈ S0, v.1 ∈ Finset.Icc (-8 : ℤ) 8 := by
  intro v hv
  rw [S0, Finset.mem_filter, mem_box] at hv
  have h := hv.1
  simp only [linf, max_le_iff] at h
  rw [Finset.mem_Icc]
  omega

/-- **Marginalization** along the first coordinate. -/
theorem sum_marginal (f : ℤ → ℝ) :
    ∑ v ∈ S0, f v.1 = ∑ k ∈ Finset.Icc (-8 : ℤ) 8, (stepCount k : ℝ) * f k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v : V3 => v.1) (t := Finset.Icc (-8 : ℤ) 8) S0_fst_mem]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.sum_const, nsmul_eq_mul,
    fiber_card k hk]

/-- **Union over the axes** of the span condition. -/
theorem span_indicator_le (z : V3) :
    (if 17 ≤ linf z then (1 : ℝ) else 0) ≤
      (if 17 ≤ z.1.natAbs then 1 else 0) + (if 17 ≤ z.2.1.natAbs then 1 else 0) +
        (if 17 ≤ z.2.2.natAbs then 1 else 0) := by
  unfold linf
  simp only [le_max_iff]
  split_ifs with h0 h1 h2 h3 <;> norm_num
  rcases h0 with h | h | h <;> contradiction

/-- Witness walks counted step by step in `ℤ³` (first coordinate tracked). -/
noncomputable def walkSum : ℕ → ℤ → ℝ
  | 0, z => if 17 ≤ z.natAbs then 1 else 0
  | c + 1, z => ∑ v ∈ S0, walkSum c (z + v.1)

/-- The same count in 1D with the fibre sizes. -/
def Ncnt : ℕ → ℤ → ℕ
  | 0, z => if 17 ≤ z.natAbs then 1 else 0
  | c + 1, z => ∑ k ∈ Finset.Icc (-8 : ℤ) 8, stepCount k * Ncnt c (z + k)

/-- **The 1D count is exact.** -/
theorem walkSum_eq : ∀ c z, walkSum c z = (Ncnt c z : ℝ)
  | 0, z => by
    simp only [walkSum, Ncnt]
    split_ifs <;> simp
  | c + 1, z => by
    simp only [walkSum, Ncnt]
    rw [sum_marginal (fun k => walkSum c (z + k))]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [walkSum_eq c (z + k)]

end QECD1
