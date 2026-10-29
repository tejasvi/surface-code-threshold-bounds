import QECD1.T2Metric3

/-!
# The metric input (M) on the 3D code in block units

For checks `u`, `v` in blocks at displacement `Δ` (block side `L = 35`), per coordinate `35 |Δ_i| ≤ |u_i - v_i| + 34`
and `|u_i - v_i| ≤ 35 |Δ_i| + 34`. Combined with `wsum3_ge_l1` and `pairCost3_le_l1`:

* `wsum3_ge_block`: an edge set without half-edges with odd checks `{u, v}` weighs at least `wmin (35 |Δ|_1 - 102)`;
* `pairCost3_le_block`: the pair cost of `{u, v}` is at most `wmax (35 |Δ|_1 + 102)`.
-/

namespace QECD1

variable {T w h : ℕ}

/-- The block displacement of two checks, in the block `ℓ1` norm. -/
def blockL1_3 (u v : PVert3 T w h) : ℕ := l1 (blockOf3 u - blockOf3 v)

/-- A coordinate difference against the block difference (lower bound). -/
theorem coord_ge_block (x y : ℕ) : 35 * ((x : ℤ) / 35 - (y : ℤ) / 35).natAbs ≤ ((x : ℤ) - y).natAbs + 34 := by
  omega

/-- A coordinate difference against the block difference (upper bound). -/
theorem coord_le_block (x y : ℕ) : ((x : ℤ) - y).natAbs ≤ 35 * ((x : ℤ) / 35 - (y : ℤ) / 35).natAbs + 34 := by
  omega

theorem blockL1_3_eq (u v : PVert3 T w h) : blockL1_3 u v =
    ((u.1.val : ℤ) / 35 - (v.1.val : ℤ) / 35).natAbs + ((u.2.1.val : ℤ) / 35 - (v.2.1.val : ℤ) / 35).natAbs +
      ((u.2.2.val : ℤ) / 35 - (v.2.2.val : ℤ) / 35).natAbs := rfl

theorem l1_ge_block3 (u v : PVert3 T w h) : 35 * blockL1_3 u v ≤ cl1_3 u v + 3 * 34 := by
  have h1 := coord_ge_block u.1.val v.1.val
  have h2 := coord_ge_block u.2.1.val v.2.1.val
  have h3 := coord_ge_block u.2.2.val v.2.2.val
  rw [blockL1_3_eq]
  unfold cl1_3
  omega

theorem l1_le_block3 (u v : PVert3 T w h) : cl1_3 u v ≤ 35 * blockL1_3 u v + 3 * 34 := by
  have h1 := coord_le_block u.1.val v.1.val
  have h2 := coord_le_block u.2.1.val v.2.1.val
  have h3 := coord_le_block u.2.2.val v.2.2.val
  rw [blockL1_3_eq]
  unfold cl1_3
  omega

/-- **(M) in block units, lower bound.** -/
theorem wsum3_ge_block {wt : PEdge3 T w h → ℝ} {wmin : ℝ} (hmin0 : 0 ≤ wmin) (hwt0 : ∀ e, 0 ≤ wt e)
    (hwt : ∀ e, ¬ e.isHalf → wmin ≤ wt e) (X : PEdge3 T w h → ZMod 2)
    (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0) {u v : PVert3 T w h}
    (hpsyn : psyn3 X = Pi.single u 1 + Pi.single v 1) :
    wmin * ((35 * blockL1_3 u v : ℕ) : ℝ) - wmin * ((3 * 34 : ℕ) : ℝ) ≤ wsum3 wt X := by
  have h := wsum3_ge_l1 hmin0 hwt0 hwt X hX hpsyn
  have hb : ((35 * blockL1_3 u v : ℕ) : ℝ) ≤ (cl1_3 u v : ℝ) + ((3 * 34 : ℕ) : ℝ) := by
    exact_mod_cast l1_ge_block3 u v
  nlinarith

/-- **(M) in block units, upper bound.** -/
theorem pairCost3_le_block {wt : PEdge3 T w h → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax) (u v : PVert3 T w h) :
    pairCost3 wt (Pi.single u 1 + Pi.single v 1) ≤
      wmax * ((35 * blockL1_3 u v : ℕ) : ℝ) + wmax * ((3 * 34 : ℕ) : ℝ) := by
  have h := pairCost3_le_l1 hwt hwt0 u v
  have hb : (cl1_3 u v : ℝ) ≤ ((35 * blockL1_3 u v : ℕ) : ℝ) + ((3 * 34 : ℕ) : ℝ) := by
    exact_mod_cast l1_le_block3 u v
  nlinarith

end QECD1
