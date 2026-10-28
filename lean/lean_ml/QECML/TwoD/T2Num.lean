import QECML.TwoD.T2Gen

/-!
# T2 numerics: tilts `λ = 0.041`, `κ = 1.05` (`μ = λ κ = 0.04305`), height tilt `s = 0.02`, `(D, a0, a1) = (5, 4, 12)`

* Exponential bounds (`Real.exp_bound`, five terms): `e^{0.04305} ≤ 1.043991`, `e^{0.02} ≤ 1.020202`,
  `e^{-0.02} ≤ 0.980199`, `e^{-0.041} ≤ 0.959830`, `e^{-0.021} ≤ 0.979219`, `e^{-0.061} ≤ 0.940824`.
* `exp_tilt_le`: `e^{μ k + s j} ≤ Wbd k j` (rational); `sum_Wbd_5_8`, `sum_Wbd_5_16`: the tilted offset sums
  `Σ_{D ≤ |v|∞ ≤ A} e^{μ |v|_1 + s v_y}` are at most `324.6` (`A = 8`) and `2260.3` (`A = 16`) (kernel).
* Geometric sums over finite sets of integers (`sum_abs_pow_le`, `sum_abs_pow_le_tail`, `sum_abs_pow_le_box`,
  `sum_gy_le`, `sum_gy_le_tail`), and the landing sum: for every finite set of offsets with `|v|∞ ≥ 9`,
  `Σ e^{-λ |v|_1 + s v_y} ≤ Jbd` (`landing_le`), and without the restriction `≤ JFbd` (`landing_full_le`).
-/

open Finset

namespace QECML

namespace S3Geom

/-! ### Exponential bounds -/

def muUp : ℚ := 1043991 / 1000000
def sUp : ℚ := 1020202 / 1000000
def sInv : ℚ := 980199 / 1000000
def qUp : ℚ := 959830 / 1000000
def qpUp : ℚ := 979219 / 1000000
def qmUp : ℚ := 940824 / 1000000

theorem exp_mu_le : Real.exp 0.04305 ≤ (muUp : ℝ) := by
  have h := Real.exp_bound (x := 0.04305) (by norm_num [abs_of_pos]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [muUp]
  linarith [h.1, h.2]

theorem exp_s_le : Real.exp 0.02 ≤ (sUp : ℝ) := by
  have h := Real.exp_bound (x := 0.02) (by norm_num [abs_of_pos]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [sUp]
  linarith [h.1, h.2]

theorem exp_neg_s_le : Real.exp (-0.02) ≤ (sInv : ℝ) := by
  have h := Real.exp_bound (x := -0.02) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [sInv]
  linarith [h.1, h.2]

theorem exp_neg_lam_le : Real.exp (-0.041) ≤ (qUp : ℝ) := by
  have h := Real.exp_bound (x := -0.041) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qUp]
  linarith [h.1, h.2]

theorem exp_neg_lam_sub_le : Real.exp (-0.021) ≤ (qpUp : ℝ) := by
  have h := Real.exp_bound (x := -0.021) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qpUp]
  linarith [h.1, h.2]

theorem exp_neg_lam_add_le : Real.exp (-0.061) ≤ (qmUp : ℝ) := by
  have h := Real.exp_bound (x := -0.061) (by norm_num [abs_of_neg]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qmUp]
  linarith [h.1, h.2]

/-! ### Tilted offset sums -/

/-- The height factor `e^{s j}` bound. -/
def Hbd (j : ℤ) : ℚ := if 0 ≤ j then sUp ^ j.toNat else sInv ^ (-j).toNat

/-- Rational upper bound for `e^{μ k + s j}`. -/
def Wbd (k : ℕ) (j : ℤ) : ℚ := muUp ^ k * Hbd j

theorem exp_height_le (j : ℤ) : Real.exp (0.02 * (j : ℝ)) ≤ ((Hbd j : ℚ) : ℝ) := by
  unfold Hbd
  split_ifs with hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [Int.toNat_natCast, Rat.cast_pow]
    rw [show (0.02 : ℝ) * ((n : ℤ) : ℝ) = (n : ℝ) * 0.02 by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_s_le n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    subst hn
    simp only [neg_neg, Int.toNat_natCast, Rat.cast_pow]
    rw [show (0.02 : ℝ) * ((-(n : ℤ) : ℤ) : ℝ) = (n : ℝ) * (-0.02) by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_s_le n

theorem exp_tilt_le (k : ℕ) (j : ℤ) :
    Real.exp (0.04305 * (k : ℝ) + 0.02 * (j : ℝ)) ≤ ((Wbd k j : ℚ) : ℝ) := by
  rw [Real.exp_add, Wbd, Rat.cast_mul]
  refine mul_le_mul ?_ (exp_height_le j) (Real.exp_pos _).le
    (Rat.cast_nonneg.2 (pow_nonneg (by norm_num [muUp]) _))
  rw [show (0.04305 : ℝ) * (k : ℝ) = (k : ℝ) * 0.04305 by ring, Real.exp_nat_mul, Rat.cast_pow]
  exact pow_le_pow_left₀ (Real.exp_pos _).le exp_mu_le k

theorem sum_Wbd_5_8 : ∑ v ∈ offBox 5 8, Wbd (v.1.natAbs + v.2.natAbs) v.2 ≤ 3246 / 10 := by decide +kernel

theorem sum_Wbd_5_16 : ∑ v ∈ offBox 5 16, Wbd (v.1.natAbs + v.2.natAbs) v.2 ≤ 22603 / 10 := by decide +kernel

theorem card_offBox_5_16 : (offBox 5 16).card = 1008 := by decide +kernel

/-! ### Geometric sums over finite sets of integers -/

theorem sum_nat_pow_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) (K : Finset ℕ) (hK : ∀ k ∈ K, m ≤ k) :
    ∑ k ∈ K, q ^ k ≤ q ^ m / (1 - q) := by
  have hsub : K ⊆ Finset.Ico m (K.sup id + 1) := by
    intro k hk
    simp only [Finset.mem_Ico]
    exact ⟨hK k hk, Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)⟩
  calc ∑ k ∈ K, q ^ k ≤ ∑ k ∈ Finset.Ico m (K.sup id + 1), q ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => pow_nonneg hq0 k
    _ ≤ q ^ m / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 hq1

theorem sum_natAbs_pow_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) (X : Finset ℤ)
    (hinj : ∀ x ∈ X, ∀ y ∈ X, x.natAbs = y.natAbs → x = y) (hX : ∀ x ∈ X, m ≤ x.natAbs) :
    ∑ x ∈ X, q ^ x.natAbs ≤ q ^ m / (1 - q) := by
  rw [← Finset.sum_image (f := fun k : ℕ => q ^ k) hinj]
  exact sum_nat_pow_le hq0 hq1 m _ fun k hk => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    exact hX x hx

theorem natAbs_inj_nonneg (X : Finset ℤ) :
    ∀ x ∈ X.filter (fun x => 0 ≤ x), ∀ y ∈ X.filter (fun x => 0 ≤ x), x.natAbs = y.natAbs → x = y := by
  intro x hx y hy h
  simp only [Finset.mem_filter] at hx hy
  omega

theorem natAbs_inj_neg (X : Finset ℤ) :
    ∀ x ∈ X.filter (fun x => ¬ 0 ≤ x), ∀ y ∈ X.filter (fun x => ¬ 0 ≤ x), x.natAbs = y.natAbs → x = y := by
  intro x hx y hy h
  simp only [Finset.mem_filter] at hx hy
  omega

/-- `Σ_{x ∈ X} q^{|x|} ≤ (1 + q) / (1 - q)`. -/
theorem sum_abs_pow_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (X : Finset ℤ) :
    ∑ x ∈ X, q ^ x.natAbs ≤ (1 + q) / (1 - q) := by
  rw [← Finset.sum_filter_add_sum_filter_not X (fun x => 0 ≤ x)]
  have h1 := sum_natAbs_pow_le hq0 hq1 0 _ (natAbs_inj_nonneg X) (fun _ _ => Nat.zero_le _)
  have h2 := sum_natAbs_pow_le hq0 hq1 1 _ (natAbs_inj_neg X) (fun x hx => by
    simp only [Finset.mem_filter] at hx
    omega)
  have e : (1 + q) / (1 - q) = q ^ 0 / (1 - q) + q ^ 1 / (1 - q) := by
    rw [pow_zero, pow_one, add_div]
  rw [e]
  exact add_le_add h1 h2

/-- `Σ_{x ∈ X} q^{|x|} ≤ 2 q^m / (1 - q)` when every `|x| ≥ m ≥ 1`. -/
theorem sum_abs_pow_le_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {m : ℕ} (X : Finset ℤ)
    (hX : ∀ x ∈ X, m ≤ x.natAbs) : ∑ x ∈ X, q ^ x.natAbs ≤ 2 * (q ^ m / (1 - q)) := by
  rw [← Finset.sum_filter_add_sum_filter_not X (fun x => 0 ≤ x), two_mul]
  refine add_le_add (sum_natAbs_pow_le hq0 hq1 m _ (natAbs_inj_nonneg X) fun x hx => ?_)
    (sum_natAbs_pow_le hq0 hq1 m _ (natAbs_inj_neg X) fun x hx => ?_)
  · exact hX x (Finset.mem_filter.1 hx).1
  · exact hX x (Finset.mem_filter.1 hx).1

/-- `Σ_{x ∈ X} q^{|x|} ≤ Σ_{k ≤ 8} q^k + Σ_{1 ≤ k ≤ 8} q^k` when every `|x| ≤ 8`. -/
theorem sum_abs_pow_le_box {q : ℝ} (hq0 : 0 ≤ q) (X : Finset ℤ) (hX : ∀ x ∈ X, x.natAbs ≤ 8) :
    ∑ x ∈ X, q ^ x.natAbs ≤ ∑ k ∈ Finset.range 9, q ^ k + ∑ k ∈ Finset.Icc 1 8, q ^ k := by
  rw [← Finset.sum_filter_add_sum_filter_not X (fun x => 0 ≤ x)]
  refine add_le_add ?_ ?_
  · rw [← Finset.sum_image (f := fun k : ℕ => q ^ k) (natAbs_inj_nonneg X)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => pow_nonneg hq0 k
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    have := hX x (Finset.mem_filter.1 hx).1
    exact Finset.mem_range.2 (by omega)
  · rw [← Finset.sum_image (f := fun k : ℕ => q ^ k) (natAbs_inj_neg X)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => pow_nonneg hq0 k
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hk
    have h1 := hX x (Finset.mem_filter.1 hx).1
    have h2 := (Finset.mem_filter.1 hx).2
    exact Finset.mem_Icc.2 ⟨by omega, h1⟩

/-- The row weight of a landing: `qp^y` above, `qm^{|y|}` below. -/
noncomputable def gy (qp qm : ℝ) (y : ℤ) : ℝ := if 0 ≤ y then qp ^ y.natAbs else qm ^ y.natAbs

theorem gy_nonneg {qp qm : ℝ} (hp : 0 ≤ qp) (hm : 0 ≤ qm) (y : ℤ) : 0 ≤ gy qp qm y := by
  unfold gy
  split_ifs
  · exact pow_nonneg hp _
  · exact pow_nonneg hm _

theorem sum_gy_split {qp qm : ℝ} (Y : Finset ℤ) :
    ∑ y ∈ Y, gy qp qm y = ∑ y ∈ Y.filter (fun y => 0 ≤ y), qp ^ y.natAbs +
      ∑ y ∈ Y.filter (fun y => ¬ 0 ≤ y), qm ^ y.natAbs := by
  rw [← Finset.sum_filter_add_sum_filter_not Y (fun y => 0 ≤ y)]
  congr 1
  · exact Finset.sum_congr rfl fun y hy => ite_eq_left (Finset.mem_filter.1 hy).2
  · exact Finset.sum_congr rfl fun y hy => ite_eq_right (Finset.mem_filter.1 hy).2

theorem sum_gy_le {qp qm : ℝ} (hp0 : 0 ≤ qp) (hp1 : qp < 1) (hm0 : 0 ≤ qm) (hm1 : qm < 1) (Y : Finset ℤ) :
    ∑ y ∈ Y, gy qp qm y ≤ 1 / (1 - qp) + qm / (1 - qm) := by
  rw [sum_gy_split]
  have h1 := sum_natAbs_pow_le hp0 hp1 0 _ (natAbs_inj_nonneg Y) (fun _ _ => Nat.zero_le _)
  have h2 := sum_natAbs_pow_le hm0 hm1 1 _ (natAbs_inj_neg Y) (fun x hx => by
    simp only [Finset.mem_filter] at hx
    omega)
  rw [pow_zero] at h1
  rw [pow_one] at h2
  exact add_le_add h1 h2

theorem sum_gy_le_tail {qp qm : ℝ} (hp0 : 0 ≤ qp) (hp1 : qp < 1) (hm0 : 0 ≤ qm) (hm1 : qm < 1) {m : ℕ}
    (Y : Finset ℤ) (hY : ∀ y ∈ Y, m ≤ y.natAbs) :
    ∑ y ∈ Y, gy qp qm y ≤ qp ^ m / (1 - qp) + qm ^ m / (1 - qm) := by
  rw [sum_gy_split]
  refine add_le_add (sum_natAbs_pow_le hp0 hp1 m _ (natAbs_inj_nonneg Y) fun x hx => ?_)
    (sum_natAbs_pow_le hm0 hm1 m _ (natAbs_inj_neg Y) fun x hx => ?_)
  · exact hY x (Finset.mem_filter.1 hx).1
  · exact hY x (Finset.mem_filter.1 hx).1

/-- A sum of a product weight over a finite set of pairs is at most the product of the sums over its projections. -/
theorem sum_prod_le_proj {f g : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) (V : Finset (ℤ × ℤ)) :
    ∑ v ∈ V, f v.1 * g v.2 ≤ (∑ x ∈ V.image Prod.fst, f x) * (∑ y ∈ V.image Prod.snd, g y) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => mul_nonneg (hf _) (hg _)
  exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hv, Finset.mem_image_of_mem _ hv⟩

/-! ### The landing sum -/

theorem rq_bounds : (0 : ℝ) ≤ (qUp : ℝ) ∧ (qUp : ℝ) < 1 ∧ (0 : ℝ) ≤ (qpUp : ℝ) ∧ (qpUp : ℝ) < 1 ∧
    (0 : ℝ) ≤ (qmUp : ℝ) ∧ (qmUp : ℝ) < 1 := by
  norm_num [qUp, qpUp, qmUp]

/-- The landing weight factorizes: `e^{-λ (|x| + |y|) + s y} ≤ qUp^{|x|} · gy(y)`. -/
theorem landing_weight_le (x y : ℤ) :
    Real.exp (-0.041 * ((x.natAbs + y.natAbs : ℕ) : ℝ) + 0.02 * (y : ℝ)) ≤
      (qUp : ℝ) ^ x.natAbs * gy (qpUp : ℝ) (qmUp : ℝ) y := by
  have e1 : -0.041 * ((x.natAbs + y.natAbs : ℕ) : ℝ) + 0.02 * (y : ℝ) =
      (x.natAbs : ℝ) * (-0.041) + (-0.041 * (y.natAbs : ℝ) + 0.02 * (y : ℝ)) := by
    push_cast
    ring
  rw [e1, Real.exp_add, Real.exp_nat_mul]
  refine mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_lam_le _) ?_ (Real.exp_pos _).le
    (pow_nonneg rq_bounds.1 _)
  unfold gy
  split_ifs with hy
  · have e2 : -0.041 * (y.natAbs : ℝ) + 0.02 * (y : ℝ) = (y.natAbs : ℝ) * (-0.021) := by
      have : (y.natAbs : ℝ) = (y : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hy)]
      rw [this]
      ring
    rw [e2, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_lam_sub_le _
  · have e2 : -0.041 * (y.natAbs : ℝ) + 0.02 * (y : ℝ) = (y.natAbs : ℝ) * (-0.061) := by
      have : (y.natAbs : ℝ) = -(y : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast (not_le.1 hy))]
      rw [this]
      ring
    rw [e2, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_lam_add_le _

/-- The landing bound `J` (offsets with `|v|∞ ≥ 9`). -/
noncomputable def Jbd : ℝ :=
  2 * ((qUp : ℝ) ^ 9 / (1 - qUp)) * (1 / (1 - (qpUp : ℝ)) + qmUp / (1 - qmUp)) +
    (∑ k ∈ Finset.range 9, (qUp : ℝ) ^ k + ∑ k ∈ Finset.Icc 1 8, (qUp : ℝ) ^ k) *
      ((qpUp : ℝ) ^ 9 / (1 - qpUp) + (qmUp : ℝ) ^ 9 / (1 - qmUp))

/-- The full landing bound (all offsets). -/
noncomputable def JFbd : ℝ := (1 + (qUp : ℝ)) / (1 - qUp) * (1 / (1 - (qpUp : ℝ)) + qmUp / (1 - qmUp))

/-- **The landing sum**: over any finite set of offsets with `|v|∞ ≥ 9`, `Σ e^{-λ |v|_1 + s v_y} ≤ Jbd`. -/
theorem landing_le (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, 9 ≤ max v.1.natAbs v.2.natAbs) :
    ∑ v ∈ V, Real.exp (-0.041 * ((v.1.natAbs + v.2.natAbs : ℕ) : ℝ) + 0.02 * (v.2 : ℝ)) ≤ Jbd := by
  obtain ⟨hq0, hq1, hp0, hp1, hm0, hm1⟩ := rq_bounds
  have hf : ∀ x : ℤ, 0 ≤ (qUp : ℝ) ^ x.natAbs := fun x => pow_nonneg hq0 _
  have hg : ∀ y : ℤ, 0 ≤ gy (qpUp : ℝ) (qmUp : ℝ) y := gy_nonneg hp0 hm0
  refine (Finset.sum_le_sum fun v _ => landing_weight_le v.1 v.2).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not V (fun v => 9 ≤ v.1.natAbs)]
  refine add_le_add ((sum_prod_le_proj hf hg _).trans ?_) ((sum_prod_le_proj hf hg _).trans ?_)
  · refine mul_le_mul (sum_abs_pow_le_tail hq0 hq1 _ fun x hx => ?_) (sum_gy_le hp0 hp1 hm0 hm1 _)
      (Finset.sum_nonneg fun y _ => hg y) (by positivity)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_filter.1 hv).2
  · refine mul_le_mul (sum_abs_pow_le_box hq0 _ fun x hx => ?_) (sum_gy_le_tail hp0 hp1 hm0 hm1 _ fun y hy => ?_)
      (Finset.sum_nonneg fun y _ => hg y) (by positivity)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
      have := (Finset.mem_filter.1 hv).2
      omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      have h1 := (Finset.mem_filter.1 hv).2
      have h2 := hV v (Finset.mem_filter.1 hv).1
      omega

/-- **The full landing sum** (no restriction on the offsets): `Σ e^{-λ |v|_1 + s v_y} ≤ JFbd`. -/
theorem landing_full_le (V : Finset (ℤ × ℤ)) :
    ∑ v ∈ V, Real.exp (-0.041 * ((v.1.natAbs + v.2.natAbs : ℕ) : ℝ) + 0.02 * (v.2 : ℝ)) ≤ JFbd := by
  obtain ⟨hq0, hq1, hp0, hp1, hm0, hm1⟩ := rq_bounds
  have hf : ∀ x : ℤ, 0 ≤ (qUp : ℝ) ^ x.natAbs := fun x => pow_nonneg hq0 _
  have hg : ∀ y : ℤ, 0 ≤ gy (qpUp : ℝ) (qmUp : ℝ) y := gy_nonneg hp0 hm0
  refine (Finset.sum_le_sum fun v _ => landing_weight_le v.1 v.2).trans ((sum_prod_le_proj hf hg _).trans ?_)
  exact mul_le_mul (sum_abs_pow_le hq0 hq1 _) (sum_gy_le hp0 hp1 hm0 hm1 _) (Finset.sum_nonneg fun y _ => hg y)
    (by positivity)

end S3Geom

end QECML
