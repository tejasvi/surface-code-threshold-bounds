import QECML.TwoD.T2Metric

/-!
# The metric input (M) in block units

For checks `u`, `v` in blocks at displacement `Δ` (block side `L`): `L |Δ_x| ≤ |u_x - v_x| + (L - 1)` and
`|u_x - v_x| ≤ L |Δ_x| + (L - 1)`, and likewise for rows. Combined with `wsum_ge_l1` and `pairCost_le_l1`:

* `wsum_ge_block`: a bulk edge set with odd checks `{u, v}` weighs at least `wmin (L |Δ|_1 - 2 (L - 1))`;
* `pairCost_le_block`: the pair cost of `{u, v}` is at most `wmax (L |Δ|_1 + 2 (L - 1))`.
-/

namespace QECML

theorem ndist_mul (L a b : ℕ) : ndist (L * a) (L * b) = L * ndist a b := by
  simp only [ndist, Nat.mul_sub, Nat.mul_add]

/-- A coordinate difference against the block difference (lower bound). -/
theorem block_le_ndist {L : ℕ} (hL : 0 < L) (x y : ℕ) : L * ndist (x / L) (y / L) ≤ ndist x y + (L - 1) := by
  have hx := Nat.div_add_mod x L
  have hy := Nat.div_add_mod y L
  have rx := Nat.mod_lt x hL
  have ry := Nat.mod_lt y hL
  rw [← ndist_mul]
  simp only [ndist] at *
  omega

/-- A coordinate difference against the block difference (upper bound). -/
theorem ndist_le_block {L : ℕ} (hL : 0 < L) (x y : ℕ) : ndist x y ≤ L * ndist (x / L) (y / L) + (L - 1) := by
  have hx := Nat.div_add_mod x L
  have hy := Nat.div_add_mod y L
  have rx := Nat.mod_lt x hL
  have ry := Nat.mod_lt y hL
  rw [← ndist_mul]
  simp only [ndist] at *
  omega

namespace S3Geom

variable {G : S3Geom}

/-- The block displacement of two checks, in the block `ℓ1` norm. -/
def blockL1 (u v : G.V) : ℕ :=
  ndist (G.blockOf u).1.val (G.blockOf v).1.val + ndist (G.blockOf u).2.val (G.blockOf v).2.val

theorem l1_ge_block (u v : G.V) :
    G.L * blockL1 u v ≤ ndist u.1.val v.1.val + ndist u.2.val v.2.val + 2 * (G.L - 1) := by
  have h1 := block_le_ndist G.hL u.1.val v.1.val
  have h2 := block_le_ndist G.hL u.2.val v.2.val
  have e1 : (G.blockOf u).1.val = u.1.val / G.L := rfl
  have e2 : (G.blockOf v).1.val = v.1.val / G.L := rfl
  have e3 : (G.blockOf u).2.val = u.2.val / G.L := rfl
  have e4 : (G.blockOf v).2.val = v.2.val / G.L := rfl
  simp only [blockL1, e1, e2, e3, e4, Nat.mul_add]
  omega

theorem l1_le_block (u v : G.V) :
    ndist u.1.val v.1.val + ndist u.2.val v.2.val ≤ G.L * blockL1 u v + 2 * (G.L - 1) := by
  have h1 := ndist_le_block G.hL u.1.val v.1.val
  have h2 := ndist_le_block G.hL u.2.val v.2.val
  have e1 : (G.blockOf u).1.val = u.1.val / G.L := rfl
  have e2 : (G.blockOf v).1.val = v.1.val / G.L := rfl
  have e3 : (G.blockOf u).2.val = u.2.val / G.L := rfl
  have e4 : (G.blockOf v).2.val = v.2.val / G.L := rfl
  simp only [blockL1, e1, e2, e3, e4, Nat.mul_add]
  omega

/-- **(M) in block units, lower bound.** -/
theorem wsum_ge_block {wt : G.Ed → ℝ} {wmin : ℝ} (hmin0 : 0 ≤ wmin) (hwt0 : ∀ e, 0 ≤ wt e)
    (hwt : ∀ e, isBulk e → wmin ≤ wt e) (X : G.Ed → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0)
    {u v : G.V} (hpsyn : psyn G.w G.h X = Pi.single u 1 + Pi.single v 1) :
    wmin * ((G.L * blockL1 u v : ℕ) : ℝ) - wmin * ((2 * (G.L - 1) : ℕ) : ℝ) ≤ wsum wt X := by
  have h := wsum_ge_l1 hmin0 hwt0 hwt X hX hpsyn
  have hb : ((G.L * blockL1 u v : ℕ) : ℝ) ≤ ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) +
      ((2 * (G.L - 1) : ℕ) : ℝ) := by
    exact_mod_cast l1_ge_block u v
  nlinarith

/-- **(M) in block units, upper bound.** -/
theorem pairCost_le_block {wt : G.Ed → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, isBulk e → wt e ≤ wmax) (u v : G.V) :
    pairCost wt (Pi.single u 1 + Pi.single v 1) ≤
      wmax * ((G.L * blockL1 u v : ℕ) : ℝ) + wmax * ((2 * (G.L - 1) : ℕ) : ℝ) := by
  have h := pairCost_le_l1 hwt0 hmax0 hwt u v
  have hb : ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) ≤ ((G.L * blockL1 u v : ℕ) : ℝ) +
      ((2 * (G.L - 1) : ℕ) : ℝ) := by
    exact_mod_cast l1_le_block u v
  nlinarith

end S3Geom

end QECML
