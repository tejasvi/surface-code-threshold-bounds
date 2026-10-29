import QECD1.LongA3Code3

/-!
# Lemma X (exchange) on the 3D code (2D `exchange`)

The weight of an edge set is the sum of `wt` over its support (`wsum3`). Let `C` be a minimum-weight edge set for its
syndrome: every edge set with the same syndrome weighs at least as much. Then any part `P` of `C` weighs at most any
edge set `P'` with the same syndrome as `P` (`exchange3`). Otherwise `C + P + P'` would be a lighter edge set with the
syndrome of `C`.

This is the general form of Lemma X. With unit weights it gives the `ℓ1` exchange behind the λ-trick constants
(`ν = 3`). The top-level correction `C_top` of the decoder is such a `C` (2D `Solver.minimal`).
-/

namespace QECD1

variable {T w h : ℕ}

/-- The weight of an edge set: `wt` summed over its support. -/
noncomputable def wsum3 (wt : PEdge3 T w h → ℝ) (X : PEdge3 T w h → ZMod 2) : ℝ :=
  ∑ e, if X e ≠ 0 then wt e else 0

/-- The syndrome is additive. -/
theorem psyn3_add (X Y : PEdge3 T w h → ZMod 2) : psyn3 (X + Y) = psyn3 X + psyn3 Y := by
  funext v
  simp only [psyn3, Pi.add_apply, Finset.sum_add_distrib]

theorem wsum3_add_le {wt : PEdge3 T w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) (X Y : PEdge3 T w h → ZMod 2) :
    wsum3 wt (X + Y) ≤ wsum3 wt X + wsum3 wt Y := by
  unfold wsum3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hw := hwt e
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (X e) with hx | hx <;> rcases zmod2_cases (Y e) with hy | hy
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy, h11]
    linarith

/-- Removing a part of an edge set lowers its weight by the weight of the part. -/
theorem wsum3_add_of_subset {wt : PEdge3 T w h → ℝ} {X Y : PEdge3 T w h → ZMod 2} (h : ∀ e, X e ≠ 0 → Y e ≠ 0) :
    wsum3 wt (Y + X) = wsum3 wt Y - wsum3 wt X := by
  unfold wsum3
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases zmod2_cases (X e) with hx | hx <;> rcases zmod2_cases (Y e) with hy | hy
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · exact absurd hy (h e (by rw [hx]; exact one_ne_zero))
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp [Pi.add_apply, hx, hy, h11]

/-- **Lemma X (exchange) on the 3D code.** -/
theorem exchange3 (wt : PEdge3 T w h → ℝ) (hwt : ∀ e, 0 ≤ wt e) {C P P' : PEdge3 T w h → ZMod 2}
    (hmin : ∀ Y, psyn3 Y = psyn3 C → wsum3 wt C ≤ wsum3 wt Y)
    (hP : ∀ e, P e ≠ 0 → C e ≠ 0) (hpsyn : psyn3 P' = psyn3 P) : wsum3 wt P ≤ wsum3 wt P' := by
  have hY : psyn3 (C + P + P') = psyn3 C := by
    rw [psyn3_add, psyn3_add, hpsyn]
    funext v
    simp only [Pi.add_apply]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h0 := hmin _ hY
  have h1 := wsum3_add_le hwt (C + P) P'
  have h2 := wsum3_add_of_subset (wt := wt) hP
  linarith

end QECD1
