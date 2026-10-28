import QECML.TwoD.T2Num
import QECML.TwoD.T2GenE
import QECML.TwoD.RouteNum

/-!
# Factors of the T2 summation at `λ = 0.041`, `κ = 1.05`, `s = 0.02`, `ε = 5e-4`, `(D, a0, a1) = (5, 4, 12)`

* One-move sums of the T2 move weights `t2g ε μ s` (`μ = 0.04305`) from any block: steps `≤ ε · 324.6`, links
  `≤ ε · 2260.3`, leaves `≤ ε · 208` (`t2_u0`, `t2_u1`, `t2_l0`).
* Route factors (`route_bot_le`, `route_top_le`): the weighted sums over grammar words from state `A` are at most
  `1.81` when words may not end right after a link, and `3.85` when they may end anywhere.
* Jumps (`jump_le`, `jump_full_le`): over any finite set of target blocks at block distance `≥ 9` from `c`,
  `Σ e^{-λ |e - c|_1 + s (e_y - c_y)} ≤ Jbd`; over any finite set of targets, `≤ JFbd`.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

theorem bdl1_eq_natAbs (cur b : G.Block) :
    bdl1 cur b = (((b.1.val : ℤ) - cur.1.val).natAbs + ((b.2.val : ℤ) - cur.2.val).natAbs) := by
  simp only [bdl1, ndist_eq_natAbs]

/-- The tilted one-move weight is at most the rational bound of its offset. -/
theorem t2g_step_le (cur b : G.Block) :
    Real.exp (0.04305 * (bdl1 cur b : ℝ) + 0.02 * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤
      ((Wbd ((((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val) : ℤ × ℤ).1.natAbs +
        (((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val) : ℤ × ℤ).2.natAbs)
        (((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val) : ℤ × ℤ).2 : ℚ) : ℝ) := by
  have h := exp_tilt_le (((b.1.val : ℤ) - cur.1.val).natAbs + ((b.2.val : ℤ) - cur.2.val).natAbs)
    ((b.2.val : ℤ) - cur.2.val)
  rw [bdl1_eq_natAbs]
  push_cast at h ⊢
  exact h

theorem t2_u0 (cur : G.Block) (hD : G.D = 5) :
    ∑ b ∈ univ.filter (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4),
      t2g 5e-4 0.04305 0.02 cur (.step b) ≤ 5e-4 * 324.6 := by
  simp only [t2g]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [hD]
  refine (Finset.sum_le_sum fun b _ => t2g_step_le cur b).trans ?_
  refine (sum_offsets_le_gen 5 8 (fun v => ((Wbd (v.1.natAbs + v.2.natAbs) v.2 : ℚ) : ℝ))
    (fun v => Rat.cast_nonneg.2 (mul_nonneg (pow_nonneg (by norm_num [muUp]) _) (by
      unfold Hbd; split_ifs
      · exact pow_nonneg (by norm_num [sUp]) _
      · exact pow_nonneg (by norm_num [sInv]) _))) cur).trans ?_
  have h := sum_Wbd_5_8
  have h' : ((∑ v ∈ offBox 5 8, Wbd (v.1.natAbs + v.2.natAbs) v.2 : ℚ) : ℝ) ≤ ((3246 / 10 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  norm_num at h' ⊢
  exact h'

theorem t2_u1 (cur : G.Block) (hD : G.D = 5) :
    ∑ b ∈ univ.filter (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 12),
      t2g 5e-4 0.04305 0.02 cur (.link b) ≤ 5e-4 * 2260.3 := by
  simp only [t2g]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [hD]
  refine (Finset.sum_le_sum fun b _ => t2g_step_le cur b).trans ?_
  refine (sum_offsets_le_gen 5 16 (fun v => ((Wbd (v.1.natAbs + v.2.natAbs) v.2 : ℚ) : ℝ))
    (fun v => Rat.cast_nonneg.2 (mul_nonneg (pow_nonneg (by norm_num [muUp]) _) (by
      unfold Hbd; split_ifs
      · exact pow_nonneg (by norm_num [sUp]) _
      · exact pow_nonneg (by norm_num [sInv]) _))) cur).trans ?_
  have h := sum_Wbd_5_16
  have h' : ((∑ v ∈ offBox 5 16, Wbd (v.1.natAbs + v.2.natAbs) v.2 : ℚ) : ℝ) ≤ ((22603 / 10 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  norm_num at h' ⊢
  exact h'

theorem t2_l0 (cur : G.Block) (hD : G.D = 5) :
    ∑ b ∈ univ.filter (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4),
      t2g 5e-4 0.04305 0.02 cur (.leaf b) ≤ 5e-4 * 208 := by
  simp only [t2g]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 := card_offsets_le (G := G) G.D (G.D - 1 + 4) cur
  have hcard : Tbox 5 8 0 = 208 := by
    simp only [Tbox, zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one, card_offBox_5_8]
    norm_num
  rw [hD] at h1 ⊢
  exact h1.trans (le_of_eq hcard)

/-- **Route factor, no end after a link** (bottom routes, family routes): `≤ 1.81` from state `A`, `≤ 0.452` from
state `B`, `≤ 1.512` from state `C`. -/
theorem route_noB_le (hD : G.D = 5) (N : ℕ) (X : GState) (cur : G.Block) :
    GWsumE G.D (G.D - 1 + 4) (G.D - 1 + 12) (t2g 5e-4 0.04305 0.02)
      (fun X => match X with | .A => 1 | .B => 0 | .C => 1) N X cur ≤ X.val 1.81 0.452 1.512 :=
  GWsumE_le (u0 := 5e-4 * 324.6) (u1 := 5e-4 * 2260.3) (l0 := 5e-4 * 208)
    (t2g_nonneg (by norm_num) _ _) (fun cur => t2_u0 cur hD) (fun cur => t2_u1 cur hD) (fun cur => t2_l0 cur hD)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) N X cur

/-- **Route factor, any end** (top routes): `≤ 3.85` from state `A`. -/
theorem route_any_le (hD : G.D = 5) (N : ℕ) (X : GState) (cur : G.Block) :
    GWsumE G.D (G.D - 1 + 4) (G.D - 1 + 12) (t2g 5e-4 0.04305 0.02) (fun _ => 1) N X cur ≤
      X.val 3.85 1.966 3.222 :=
  GWsumE_le (u0 := 5e-4 * 324.6) (u1 := 5e-4 * 2260.3) (l0 := 5e-4 * 208)
    (t2g_nonneg (by norm_num) _ _) (fun cur => t2_u0 cur hD) (fun cur => t2_u1 cur hD) (fun cur => t2_l0 cur hD)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) N X cur

/-! ### Jumps -/

/-- The jump weight from `c` to `e`: `e^{-λ |e - c|_1 + s (e_y - c_y)}`. -/
noncomputable def jw (c e : G.Block) : ℝ :=
  Real.exp (-0.041 * (bdl1 c e : ℝ) + 0.02 * ((e.2.val : ℝ) - (c.2.val : ℝ)))

theorem jw_eq (c e : G.Block) : jw c e =
    (fun v : ℤ × ℤ => Real.exp (-0.041 * ((v.1.natAbs + v.2.natAbs : ℕ) : ℝ) + 0.02 * (v.2 : ℝ)))
      ((e.1.val : ℤ) - c.1.val, (e.2.val : ℤ) - c.2.val) := by
  simp only [jw, bdl1_eq_natAbs]
  push_cast
  ring_nf

theorem offset_inj (c : G.Block) (S : Finset G.Block) :
    Set.InjOn (fun b : G.Block => ((b.1.val : ℤ) - c.1.val, (b.2.val : ℤ) - c.2.val)) (S : Set G.Block) :=
  fun b _ b' _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- **Jumps with (R)**: over any finite set of target blocks at block distance at least `9`, the jump weights sum to
at most `Jbd`. -/
theorem jump_le (c : G.Block) (S : Finset G.Block) (hS : ∀ e ∈ S, 9 ≤ G.blockDist c e) :
    ∑ e ∈ S, jw c e ≤ Jbd := by
  simp only [jw_eq]
  rw [← Finset.sum_image (f := fun v : ℤ × ℤ =>
    Real.exp (-0.041 * ((v.1.natAbs + v.2.natAbs : ℕ) : ℝ) + 0.02 * (v.2 : ℝ))) (offset_inj c S)]
  refine landing_le _ fun v hv => ?_
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hv
  have h := hS e he
  have e1 := ndist_eq_natAbs c.1.val e.1.val
  have e2 := ndist_eq_natAbs c.2.val e.2.val
  have hd : G.blockDist c e = max (ndist c.1.val e.1.val) (ndist c.2.val e.2.val) := rfl
  simp only
  omega

/-- **Jumps without (R)**: over any finite set of target blocks, the jump weights sum to at most `JFbd`. -/
theorem jump_full_le (c : G.Block) (S : Finset G.Block) : ∑ e ∈ S, jw c e ≤ JFbd := by
  simp only [jw_eq]
  rw [← Finset.sum_image (f := fun v : ℤ × ℤ =>
    Real.exp (-0.041 * ((v.1.natAbs + v.2.natAbs : ℕ) : ℝ) + 0.02 * (v.2 : ℝ))) (offset_inj c S)]
  exact landing_full_le _

end S3Geom

end QECML
