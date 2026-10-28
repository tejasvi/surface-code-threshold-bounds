import QECML.TwoD.RouteCount

/-!
# The T1 count at `(D, a0, a1) = (5, 4, 12)`, `ε = 5e-4`, tilt `s = 0.2155`

* `exp_s_bounds`: `1.2404 ≤ e^{0.2155} ≤ 1.2405` (Taylor bound `Real.exp_bound`, five terms).
* `exp_mul_int_le`: `e^{0.2155 k} ≤ Ebd k` for every integer `k`, with `Ebd k = 1.2405^k` (`k ≥ 0`) and
  `(1/1.2404)^{-k}` (`k < 0`), rational.
* `Tbox_5_8_le`, `Tbox_5_16_le`: the tilted offset sums are at most `385` and `5254` (the rational sums of `Ebd`
  over the offset boxes are evaluated by the kernel); `card_offBox_5_8`: `|offBox 5 8| = 208`.
* `S3Fam.h2dT1count_a12`: `H2D_T1count 4 12 constsA12 5e-4` for every family with `D = 5`. With the fixed point
  `(α, β, γ) = (45.57, 13.62, 36.80)` of the transfer inequalities (`u0 = 5e-4·385`, `u1 = 5e-4·5254`,
  `l0 = 5e-4·208`), the count is at most `8 · 45.57 = 364.56 ≤ 422` times `n_x e^{-0.2155 (n_y - 31)}`.
-/

open Finset

namespace QECML

namespace S3Geom

/-- Upper bound for `e^{0.2155}`. -/
def rUp : ℚ := 12405 / 10000

/-- Upper bound for `e^{-0.2155}`. -/
def rInv : ℚ := 10000 / 12404

/-- Rational upper bound for `e^{0.2155 k}`. -/
def Ebd (k : ℤ) : ℚ := if 0 ≤ k then rUp ^ k.toNat else rInv ^ (-k).toNat

theorem exp_s_bounds : (1.2404 : ℝ) ≤ Real.exp 0.2155 ∧ Real.exp 0.2155 ≤ 1.2405 := by
  have h := Real.exp_bound (x := 0.2155) (by norm_num [abs_of_pos]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem exp_mul_int_le (k : ℤ) : Real.exp (0.2155 * (k : ℝ)) ≤ ((Ebd k : ℚ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := exp_s_bounds
  unfold Ebd
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp only [Int.toNat_natCast, Rat.cast_pow, rUp]
    rw [show (0.2155 : ℝ) * ((n : ℤ) : ℝ) = (n : ℝ) * 0.2155 by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by push_cast; linarith) n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    simp only [neg_neg, Int.toNat_natCast, Rat.cast_pow, rInv]
    rw [show (0.2155 : ℝ) * ((-(n : ℤ) : ℤ) : ℝ) = (n : ℝ) * (-0.2155) by push_cast; ring, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ n
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    push_cast
    norm_num
    linarith

theorem Tbox_le_of (D A : ℕ) (t : ℚ) (h : ∑ v ∈ offBox D A, Ebd v.2 ≤ t) : Tbox D A 0.2155 ≤ (t : ℝ) := by
  unfold Tbox
  calc ∑ v ∈ offBox D A, Real.exp (0.2155 * (v.2 : ℝ)) ≤ ∑ v ∈ offBox D A, ((Ebd v.2 : ℚ) : ℝ) :=
        Finset.sum_le_sum fun v _ => exp_mul_int_le v.2
    _ = ((∑ v ∈ offBox D A, Ebd v.2 : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ (t : ℝ) := by exact_mod_cast h

theorem sum_Ebd_5_8 : ∑ v ∈ offBox 5 8, Ebd v.2 ≤ 385 := by decide +kernel

theorem sum_Ebd_5_16 : ∑ v ∈ offBox 5 16, Ebd v.2 ≤ 5254 := by decide +kernel

theorem card_offBox_5_8 : (offBox 5 8).card = 208 := by decide +kernel

end S3Geom

namespace S3Fam

variable (fam : S3Fam)

/-- **The T1 counting bound for a1 = 12 is a theorem** (for `D = 5`, e.g. `R = L - 1`, `L ≥ 2`): the
`ε`-weighted number of counted-block sets of valid routes is at most `4.22e2 n_x e^{-0.2155 (n_y - 31)}`. -/
theorem h2dT1count_a12 (hD : 4 + 2 * fam.R / fam.L = 5) : fam.H2D_T1count 4 12 constsA12 5e-4 := by
  intro nx ny hnx hny hny1
  set G := fam.geom nx ny (by omega) hny1 with hG
  have hGD : G.D = 5 := hD
  have hT0 : S3Geom.Tbox 5 8 0.2155 ≤ 385 := by
    have := S3Geom.Tbox_le_of 5 8 385 S3Geom.sum_Ebd_5_8
    exact_mod_cast this
  have hT1 : S3Geom.Tbox 5 16 0.2155 ≤ 5254 := by
    have := S3Geom.Tbox_le_of 5 16 5254 S3Geom.sum_Ebd_5_16
    exact_mod_cast this
  have hcard : S3Geom.Tbox 5 8 0 = 208 := by
    simp only [S3Geom.Tbox, zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
      S3Geom.card_offBox_5_8]
    norm_num
  have hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4),
      (5e-4 : ℝ) * Real.exp (0.2155 * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ 5e-4 * 385 := by
    intro cur
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h1 := S3Geom.sum_offsets_le (G := G) G.D (G.D - 1 + 4) 0.2155 cur
    rw [hGD] at h1 ⊢
    exact h1.trans hT0
  have hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 12),
      (5e-4 : ℝ) * Real.exp (0.2155 * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ 5e-4 * 5254 := by
    intro cur
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h1 := S3Geom.sum_offsets_le (G := G) G.D (G.D - 1 + 12) 0.2155 cur
    rw [hGD] at h1 ⊢
    exact h1.trans hT1
  have hl0 : ∀ cur : G.Block, ∑ _b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4), (5e-4 : ℝ) ≤ 5e-4 * 208 := by
    intro cur
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h1 := S3Geom.card_offsets_le (G := G) G.D (G.D - 1 + 4) cur
    rw [hGD] at h1 ⊢
    exact h1.trans (le_of_eq hcard)
  have h := G.routeCount_le 4 12 (ε := 5e-4) (s := 0.2155) (u0 := 5e-4 * 385) (u1 := 5e-4 * 5254)
    (l0 := 5e-4 * 208) (α := 45.57) (β := 13.62) (γ := 36.80) (by norm_num) (by norm_num) hu0 hu1 hl0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have key : (G.nx : ℝ) * ((Stage1.hs 12 : ℝ) + 1) * 45.57 *
      Real.exp (-0.2155 * ((G.ny : ℝ) - ((2 * Stage1.hs 12 + (G.D - 1 + 12) + 1 : ℕ) : ℝ))) ≤
      constsA12.C1 * nx * Real.exp (-constsA12.s1 * ((ny : ℝ) - constsA12.H0)) := by
    have e1 : ((2 * Stage1.hs 12 + (G.D - 1 + 12) + 1 : ℕ) : ℝ) = 31 := by
      rw [hGD]
      norm_num [Stage1.hs]
    have e2 : (Stage1.hs 12 : ℝ) = 7 := by norm_num [Stage1.hs]
    rw [e1, e2]
    simp only [constsA12]
    have hx : 0 ≤ Real.exp (-0.2155 * ((ny : ℝ) - 31)) := (Real.exp_pos _).le
    have hn : (0 : ℝ) ≤ nx := Nat.cast_nonneg _
    have hnx' := mul_nonneg hn hx
    show (nx : ℝ) * (7 + 1) * 45.57 * Real.exp (-0.2155 * ((ny : ℝ) - 31)) ≤
      4.22e2 * nx * Real.exp (-0.2155 * ((ny : ℝ) - 31))
    nlinarith
  exact h.trans key

end S3Fam

end QECML
