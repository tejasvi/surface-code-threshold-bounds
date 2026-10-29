import QECD1.Family3
import QECD1.Ratio

/-!
# The transfer ratio with the height tilt `s = 7/1000` (the T2 rate)

With `λ = 0.014`, `s = 0.007`, `κ = 1`, `off = (1 + κ) D ν = 30` and
`ε = ε*`:

* `landing_tilt_le`: for every finite set `S` of offsets with `|v|∞ ≥ J = 17`,
  `Σ_{v ∈ S} e^{-λ |v|₁ + s v_y} ≤ Jbar2`; the full lattice factorizes into two plain 1D sums and one tilted 1D sum
  (`sum_box_prod`, `landing_prod_le`), with ratios `e^{-λ}`, `e^{-(λ - s)}`, `e^{-(λ + s)}`;
* `ratio_s_num`: `Jbar2 · 1.5219616 · ε* · F0 ≤ 0.9` with `F0 = 2 F0t + F0y` from the certificate (value 0.8927);
* `ratio_s_le`: the same with the real landing sum, the real `e^{30 λ}` and the values of the three real family
  automata (`fam3 0`, `fam3 1`, `fam3 2`) at any word length.
-/

namespace QECD1

def qmUp : ℚ := 9930245 / 10000000
def qmLo : ℚ := 9930244 / 10000000
def qpUp : ℚ := 9792190 / 10000000
def qpLo : ℚ := 9792189 / 10000000

theorem exp_qm_le : Real.exp (-(lam - sT)) ≤ (qmUp : ℝ) := by
  have h := Real.exp_bound (x := -(7 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qmUp, lam, sT]
  linarith [h.1, h.2]

theorem exp_qm_ge : (qmLo : ℝ) ≤ Real.exp (-(lam - sT)) := by
  have h := Real.exp_bound (x := -(7 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qmLo, lam, sT]
  linarith [h.1, h.2]

theorem exp_qp_le : Real.exp (-(lam + sT)) ≤ (qpUp : ℝ) := by
  have h := Real.exp_bound (x := -(21 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qpUp, lam, sT]
  linarith [h.1, h.2]

theorem exp_qp_ge : (qpLo : ℝ) ≤ Real.exp (-(lam + sT)) := by
  have h := Real.exp_bound (x := -(21 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qpLo, lam, sT]
  linarith [h.1, h.2]

/-! ### Bounds of `e^{-λ}` and `e^{30 λ}` at `λ = 0.014`

The tilted chain uses these; `Ratio` keeps its `s = 0` results and bounds at `λ = 0.013`. -/

def qUpT : ℚ := 9860976 / 10000000
def qLoT : ℚ := 9860975 / 10000000
def eoffUpT : ℚ := 15219616 / 10000000

theorem exp_neg_lamT_le : Real.exp (-lam) ≤ (qUpT : ℝ) := by
  have h := Real.exp_bound (x := -(14 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qUpT, lam]
  linarith [h.1, h.2]

theorem exp_neg_lamT_ge : (qLoT : ℝ) ≤ Real.exp (-lam) := by
  have h := Real.exp_bound (x := -(14 / 1000)) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qLoT, lam]
  linarith [h.1, h.2]

theorem exp_offT_le : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := by
  have h := Real.exp_bound (x := 21 / 50) (by norm_num [abs_of_pos]) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [eoffUpT, lam]
  linarith [h.1, h.2]

/-! ### Box factorization with product weights -/

theorem sum_box_prod (f g : ℤ → ℝ) (K : ℕ) :
    ∑ v ∈ box K, f v.1 * f v.2.1 * g v.2.2 =
      (∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a) *
        ((∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a) * ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c) := by
  set A := Finset.Icc (-(K : ℤ)) K
  have h : ∑ v ∈ box K, f v.1 * f v.2.1 * g v.2.2 = ∑ a ∈ A, ∑ y ∈ A ×ˢ A, f a * (f y.1 * g y.2) := by
    unfold box
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [h]
  have h2 : ∀ a ∈ A, ∑ y ∈ A ×ˢ A, f a * (f y.1 * g y.2) = f a * ((∑ b ∈ A, f b) * ∑ c ∈ A, g c) := by
    intro a _
    rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]

/-- **Landing sum with product weights**. -/
theorem landing_prod_le (f g : ℤ → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ c, 0 ≤ g c) (Fu Gu : ℝ)
    (hFu : ∀ K : ℕ, ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a ≤ Fu)
    (hGu : ∀ K : ℕ, ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c ≤ Gu)
    (S : Finset V3) (hS : ∀ v ∈ S, 17 ≤ linf v) :
    ∑ v ∈ S, f v.1 * f v.2.1 * g v.2.2 ≤
      Fu * (Fu * Gu) - (∑ a ∈ Finset.Icc (-16 : ℤ) 16, f a) *
        ((∑ a ∈ Finset.Icc (-16 : ℤ) 16, f a) * ∑ c ∈ Finset.Icc (-16 : ℤ) 16, g c) := by
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
  have hnn : ∀ v : V3, 0 ≤ f v.1 * f v.2.1 * g v.2.2 := fun v => mul_nonneg (mul_nonneg (hf _) (hf _)) (hg _)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hnn v)
  rw [Finset.sum_sdiff_eq_sub h16, sum_box_prod, sum_box_prod] at h1
  have hP0 : 0 ≤ ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a := Finset.sum_nonneg fun a _ => hf a
  have hG0 : 0 ≤ ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c := Finset.sum_nonneg fun c _ => hg c
  have h2 : (∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a) * ((∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a) *
      ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c) ≤ Fu * (Fu * Gu) := by
    have hFu0 : 0 ≤ Fu := le_trans hP0 (hFu K)
    exact mul_le_mul (hFu K) (mul_le_mul (hFu K) (hGu K) hG0 hFu0) (mul_nonneg hP0 hG0) hFu0
  have e16 : ((16 : ℕ) : ℤ) = 16 := rfl
  rw [e16] at h1
  linarith

/-! ### The tilted 1D sum -/

/-- `Σ_{|c| ≤ K} (a^c for c ≥ 0, b^{|c|} for c < 0)`. -/
noncomputable def Ty (a b : ℝ) (K : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc (-(K : ℤ)) K, if 0 ≤ c then a ^ c.natAbs else b ^ c.natAbs

theorem Ty_succ (a b : ℝ) (K : ℕ) : Ty a b (K + 1) = Ty a b K + a ^ (K + 1) + b ^ (K + 1) := by
  unfold Ty
  rw [Icc_succ, Finset.sum_insert, Finset.sum_insert]
  · have h1 : (-((K + 1 : ℕ) : ℤ)).natAbs = K + 1 := by omega
    have h2 : ((K + 1 : ℕ) : ℤ).natAbs = K + 1 := by omega
    have h3 : ¬ (0 ≤ -((K + 1 : ℕ) : ℤ)) := by omega
    have h4 : (0 ≤ ((K + 1 : ℕ) : ℤ)) := by omega
    rw [if_neg h3, if_pos h4, h1, h2]
    ring
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

theorem Ty_zero (a b : ℝ) : Ty a b 0 = 1 := by
  simp [Ty]

theorem Ty_eq (a b : ℝ) (ha : a ≠ 1) (hb : b ≠ 1) (K : ℕ) :
    Ty a b K = 1 + a * (1 - a ^ K) / (1 - a) + b * (1 - b ^ K) / (1 - b) := by
  have ha1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hb1 : (1 : ℝ) - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  induction K with
  | zero =>
    rw [Ty_zero]
    simp
  | succ K ih =>
    rw [Ty_succ, ih]
    field_simp
    ring

theorem Ty_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) (K : ℕ) :
    Ty a b K ≤ 1 + a / (1 - a) + b / (1 - b) := by
  rw [Ty_eq a b (ne_of_lt ha1) (ne_of_lt hb1) K]
  have hA : a * (1 - a ^ K) / (1 - a) ≤ a / (1 - a) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 ≤ a ^ K := pow_nonneg ha0 _
    nlinarith
  have hB : b * (1 - b ^ K) / (1 - b) ≤ b / (1 - b) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 ≤ b ^ K := pow_nonneg hb0 _
    nlinarith
  linarith

theorem Ty_mono (a a' b b' : ℝ) (ha : 0 ≤ a) (haa : a ≤ a') (hb : 0 ≤ b) (hbb : b ≤ b') (K : ℕ) :
    Ty a b K ≤ Ty a' b' K := by
  unfold Ty
  refine Finset.sum_le_sum fun c _ => ?_
  split_ifs
  · exact pow_le_pow_left₀ ha haa _
  · exact pow_le_pow_left₀ hb hbb _

/-- `x / (1 - x)` is increasing on `[0, 1)`. -/
theorem frac_mono (x y : ℝ) (hy : y < 1) (hxy : x ≤ y) : x / (1 - x) ≤ y / (1 - y) := by
  have h1 : 0 < 1 - y := by linarith
  have h2 : 0 < 1 - x := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-! ### The tilted landing bound and the ratio -/

/-- The tilted landing bound with rational parameters. -/
noncomputable def Jbar2 : ℝ :=
  ((1 + (qUpT : ℝ)) / (1 - qUpT)) * (((1 + (qUpT : ℝ)) / (1 - qUpT)) *
      (1 + (qmUp : ℝ) / (1 - qmUp) + (qpUp : ℝ) / (1 - qpUp))) -
    ((1 + (qLoT : ℝ) - 2 * (qLoT : ℝ) ^ 17) / (1 - qLoT)) * (((1 + (qLoT : ℝ) - 2 * (qLoT : ℝ) ^ 17) / (1 - qLoT)) *
      (1 + (qmLo : ℝ) * (1 - (qmLo : ℝ) ^ 16) / (1 - qmLo) + (qpLo : ℝ) * (1 - (qpLo : ℝ) ^ 16) / (1 - qpLo)))

theorem exp_tilt_split (v : V3) :
    Real.exp (-lam * l1 v + sT * v.2.2) =
      Real.exp (-lam) ^ v.1.natAbs * Real.exp (-lam) ^ v.2.1.natAbs *
        (if 0 ≤ v.2.2 then Real.exp (-(lam - sT)) ^ v.2.2.natAbs else Real.exp (-(lam + sT)) ^ v.2.2.natAbs) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  split_ifs with hc
  · rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hcast : ((v.2.2.natAbs : ℕ) : ℝ) = (v.2.2 : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact abs_of_nonneg (by exact_mod_cast hc)
    simp only [l1]
    push_cast
    rw [hcast]
    ring
  · rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hcast : ((v.2.2.natAbs : ℕ) : ℝ) = -(v.2.2 : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact abs_of_neg (by exact_mod_cast (not_le.1 hc))
    simp only [l1]
    push_cast
    rw [hcast]
    ring

/-- **Tilted landing bound** at `λ = 0.014`, `s = 0.007`. -/
theorem landing_tilt_le (S : Finset V3) (hS : ∀ v ∈ S, 17 ≤ linf v) :
    ∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) ≤ Jbar2 := by
  have hqU : Real.exp (-lam) ≤ (qUpT : ℝ) := by
    exact exp_neg_lamT_le
  have hqL : (qLoT : ℝ) ≤ Real.exp (-lam) := by
    exact exp_neg_lamT_ge
  set q := Real.exp (-lam)
  set qm := Real.exp (-(lam - sT))
  set qp := Real.exp (-(lam + sT))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqm0 : 0 ≤ qm := (Real.exp_pos _).le
  have hqp0 : 0 ≤ qp := (Real.exp_pos _).le
  have hU1 : (qUpT : ℝ) < 1 := by norm_num [qUpT]
  have hmU1 : (qmUp : ℝ) < 1 := by norm_num [qmUp]
  have hpU1 : (qpUp : ℝ) < 1 := by norm_num [qpUp]
  have hq1 : q < 1 := lt_of_le_of_lt hqU hU1
  have hqm1 : qm < 1 := lt_of_le_of_lt exp_qm_le hmU1
  have hqp1 : qp < 1 := lt_of_le_of_lt exp_qp_le hpU1
  set f : ℤ → ℝ := fun a => q ^ a.natAbs
  set g : ℤ → ℝ := fun c => if 0 ≤ c then qm ^ c.natAbs else qp ^ c.natAbs
  have hsplit : ∀ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) = f v.1 * f v.2.1 * g v.2.2 :=
    fun v _ => exp_tilt_split v
  rw [Finset.sum_congr rfl hsplit]
  have hf : ∀ a, 0 ≤ f a := fun a => pow_nonneg hq0 _
  have hg : ∀ c, 0 ≤ g c := fun c => by
    show 0 ≤ (if 0 ≤ c then qm ^ c.natAbs else qp ^ c.natAbs)
    split_ifs
    · exact pow_nonneg hqm0 _
    · exact pow_nonneg hqp0 _
  have hFu : ∀ K : ℕ, ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a ≤ (1 + (qUpT : ℝ)) / (1 - qUpT) := by
    intro K
    have h1 : ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a = S1 q K := rfl
    rw [h1]
    refine le_trans (S1_le q hq0 hq1 K) ?_
    have hpos : 0 < 1 - q := by linarith
    have hposU : (0 : ℝ) < 1 - qUpT := by linarith
    rw [div_le_div_iff₀ hpos hposU]
    nlinarith
  have hGu : ∀ K : ℕ, ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c ≤
      1 + (qmUp : ℝ) / (1 - qmUp) + (qpUp : ℝ) / (1 - qpUp) := by
    intro K
    have h1 : ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c = Ty qm qp K := rfl
    rw [h1]
    refine le_trans (Ty_le qm qp hqm0 hqm1 hqp0 hqp1 K) ?_
    have := frac_mono qm qmUp hmU1 exp_qm_le
    have := frac_mono qp qpUp hpU1 exp_qp_le
    linarith
  have h := landing_prod_le f g hf hg _ _ hFu hGu S hS
  -- lower bounds for the inner box
  have hin1 : ∑ a ∈ Finset.Icc (-16 : ℤ) 16, f a = S1 q 16 := rfl
  have hin2 : ∑ c ∈ Finset.Icc (-16 : ℤ) 16, g c = Ty qm qp 16 := rfl
  rw [hin1, hin2] at h
  have hS1L : S1 (qLoT : ℝ) 16 = (1 + (qLoT : ℝ) - 2 * (qLoT : ℝ) ^ 17) / (1 - qLoT) :=
    S1_eq _ (by norm_num [qLoT]) 16
  have hTyL : Ty (qmLo : ℝ) (qpLo : ℝ) 16 =
      1 + (qmLo : ℝ) * (1 - (qmLo : ℝ) ^ 16) / (1 - qmLo) + (qpLo : ℝ) * (1 - (qpLo : ℝ) ^ 16) / (1 - qpLo) :=
    Ty_eq _ _ (by norm_num [qmLo]) (by norm_num [qpLo]) 16
  have hS1m : S1 (qLoT : ℝ) 16 ≤ S1 q 16 := S1_mono _ _ (by norm_num [qLoT]) hqL 16
  have hTym : Ty (qmLo : ℝ) (qpLo : ℝ) 16 ≤ Ty qm qp 16 :=
    Ty_mono _ _ _ _ (by norm_num [qmLo]) exp_qm_ge (by norm_num [qpLo]) exp_qp_ge 16
  have hS10 : 0 ≤ S1 (qLoT : ℝ) 16 := S1_nonneg _ (by norm_num [qLoT]) 16
  have hTy0 : 0 ≤ Ty (qmLo : ℝ) (qpLo : ℝ) 16 := by
    unfold Ty
    refine Finset.sum_nonneg fun c _ => ?_
    split_ifs
    · exact pow_nonneg (by norm_num [qmLo]) _
    · exact pow_nonneg (by norm_num [qpLo]) _
  have hprod : S1 (qLoT : ℝ) 16 * (S1 (qLoT : ℝ) 16 * Ty (qmLo : ℝ) (qpLo : ℝ) 16) ≤
      S1 q 16 * (S1 q 16 * Ty qm qp 16) :=
    mul_le_mul hS1m (mul_le_mul hS1m hTym hTy0 (le_trans hS10 hS1m)) (mul_nonneg hS10 hTy0)
      (le_trans hS10 hS1m)
  unfold Jbar2
  rw [← hS1L, ← hTyL]
  linarith

/-- The certified family factor `F0 = 2 F0t + F0y`. -/
noncomputable def F0s : ℝ := 2 * ((2734104547231 : ℝ) / 10 ^ 15) + (2741437430948 : ℝ) / 10 ^ 15

/-- **The transfer ratio with tilt is at most 0.9** (value about 0.8927). -/
theorem ratio_s_num : Jbar2 * (eoffUpT : ℝ) * (37 / 2000000) * F0s ≤ 9 / 10 := by
  unfold Jbar2 F0s
  norm_num [qUpT, qLoT, qmUp, qmLo, qpUp, qpLo, eoffUpT]

theorem V_nonneg {σ τ : Type} (M : WA σ τ) (hg : ∀ q t, 0 ≤ M.g q t) (he : ∀ q, 0 ≤ M.e q) :
    ∀ (N : ℕ) (q : σ), 0 ≤ M.V N q
  | 0, q => he q
  | N + 1, q => add_nonneg (he q) (Finset.sum_nonneg fun t _ => mul_nonneg (hg q t) (V_nonneg M hg he N _))

/-- **Ratio bound with tilt**, for the real landing sum, the real `e^{30 λ}` and the real family automata of the
three axes at any word length. -/
theorem ratio_s_le (S : Finset V3) (hS : ∀ v ∈ S, Const.J ≤ linf v) (N : ℕ) :
    (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) * eps *
      ((fam3 0).V N 0 + (fam3 1).V N 0 + (fam3 2).V N 0) ≤ 9 / 10 := by
  have hJ := landing_tilt_le S fun v hv => by
    have h := hS v hv
    rw [Const.J_val] at h
    exact h
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := by
    exact exp_offT_le
  have hV : (fam3 0).V N 0 + (fam3 1).V N 0 + (fam3 2).V N 0 ≤ F0s := by
    unfold F0s
    linarith [famT_V_le N, famX_V_le N, famY_V_le N]
  have hV0 : 0 ≤ (fam3 0).V N 0 + (fam3 1).V N 0 + (fam3 2).V N 0 := by
    have h0 := V_nonneg (fam3 0) (fun n t => tokW_nonneg n t) famEnd_nonneg N 0
    have h1 := V_nonneg (fam3 1) (fun n t => tokW_nonneg n t) famEnd_nonneg N 0
    have h2 := V_nonneg (fam3 2) (fun n t => tokW_nonneg n t) famEnd_nonneg N 0
    linarith
  have hs0 : 0 ≤ ∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have he0 : (0 : ℝ) ≤ eps := eps_nonneg
  have h1 : (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) ≤ Jbar2 * (eoffUpT : ℝ) :=
    mul_le_mul hJ hE (Real.exp_pos _).le (le_trans hs0 hJ)
  have hJ0 : 0 ≤ Jbar2 * (eoffUpT : ℝ) := le_trans (mul_nonneg hs0 (Real.exp_pos _).le) h1
  have h2 : (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) * eps ≤
      Jbar2 * (eoffUpT : ℝ) * eps := mul_le_mul_of_nonneg_right h1 he0
  have h3 : (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) * eps *
      ((fam3 0).V N 0 + (fam3 1).V N 0 + (fam3 2).V N 0) ≤ Jbar2 * (eoffUpT : ℝ) * eps * F0s :=
    mul_le_mul h2 hV hV0 (mul_nonneg hJ0 he0)
  have h4 : Jbar2 * (eoffUpT : ℝ) * eps * F0s ≤ 9 / 10 := by
    have e : eps = 37 / 2000000 := rfl
    rw [e]
    exact ratio_s_num
  linarith

end QECD1
