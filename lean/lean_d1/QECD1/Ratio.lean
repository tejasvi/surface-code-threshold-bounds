import QECD1.Landing
import QECD1.CertCheck

/-!
# The transfer ratio of the refined 3D T2 count at `ε* = 1.85e-5`, `s = 0`

With `λ = μ = 0.013`, `κ = 1`, `off = (1 + κ) D ν = 30`:

* `exp_neg_lam_le`, `exp_neg_lam_ge`: `0.9870841 ≤ e^{-0.013} ≤ 0.9870842`; `exp_off_le`: `e^{0.39} ≤ 1.4769808`.
* `landing_bound`: for every finite set `S` of offsets with `|v|∞ ≥ 17`, `Σ_{v ∈ S} e^{-0.013 |v|₁} ≤ Jbar`.
* `ratio_le`: `Jbar · 1.4769808 · ε* · 3 · F0x ≤ 0.9`, where `F0x = 2174093984726 / 10^15` is the certified family
  factor of one axis (`QECD1.CertData.fam_val_le`); the three axes agree at `s = 0`. The value is about `0.6445`.
-/

namespace QECD1

def qUp : ℚ := 9870842 / 10000000
def qLo : ℚ := 9870841 / 10000000
def eoffUp : ℚ := 14769808 / 10000000

theorem exp_neg_lam_le : Real.exp (-0.013) ≤ (qUp : ℝ) := by
  have h := Real.exp_bound (x := -0.013) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qUp]
  linarith [h.1, h.2]

theorem exp_neg_lam_ge : (qLo : ℝ) ≤ Real.exp (-0.013) := by
  have h := Real.exp_bound (x := -0.013) (by norm_num [abs_of_neg]) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [qLo]
  linarith [h.1, h.2]

theorem exp_off_le : Real.exp (0.013 * 30) ≤ (eoffUp : ℝ) := by
  have h := Real.exp_bound (x := 0.013 * 30) (by norm_num [abs_of_pos]) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [eoffUp]
  linarith [h.1, h.2]

/-- The landing bound with rational parameters. -/
noncomputable def Jbar : ℝ :=
  ((1 + (qUp : ℝ)) / (1 - qUp)) ^ 3 - ((1 + (qLo : ℝ) - 2 * (qLo : ℝ) ^ 17) / (1 - qLo)) ^ 3

/-- **Landing bound** at `λ = 0.013`. -/
theorem landing_bound (S : Finset V3) (hS : ∀ v ∈ S, 17 ≤ linf v) :
    ∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ)) ≤ Jbar := by
  set q := Real.exp (-0.013) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqU : q ≤ (qUp : ℝ) := exp_neg_lam_le
  have hqL : (qLo : ℝ) ≤ q := exp_neg_lam_ge
  have hq1 : q < 1 := lt_of_le_of_lt hqU (by norm_num [qUp])
  have hrw : ∀ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ)) = q ^ l1 v := by
    intro v _
    rw [hqdef, ← Real.exp_nat_mul]
    ring_nf
  rw [Finset.sum_congr rfl hrw]
  have h1 := landing_le q hq0 hq1 S hS
  -- the full-lattice term is increasing in q, the inner term too (subtracted): use qUp and qLo
  have hfull : ((1 + q) / (1 - q)) ^ 3 ≤ ((1 + (qUp : ℝ)) / (1 - qUp)) ^ 3 := by
    have hU1 : (qUp : ℝ) < 1 := by norm_num [qUp]
    have hpos : 0 < 1 - q := by linarith
    have hposU : (0 : ℝ) < 1 - qUp := by linarith
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hpos hposU]
    nlinarith
  have hinner : S1 (qLo : ℝ) 16 ≤ S1 q 16 := S1_mono _ _ (by norm_num [qLo]) hqL 16
  have hinner0 : 0 ≤ S1 (qLo : ℝ) 16 := S1_nonneg _ (by norm_num [qLo]) 16
  have hcube : S1 (qLo : ℝ) 16 ^ 3 ≤ S1 q 16 ^ 3 := pow_le_pow_left₀ hinner0 hinner 3
  have hS1L : S1 (qLo : ℝ) 16 = (1 + (qLo : ℝ) - 2 * (qLo : ℝ) ^ 17) / (1 - qLo) :=
    S1_eq _ (by norm_num [qLo]) 16
  unfold Jbar
  rw [← hS1L]
  linarith

/-- **The transfer ratio is at most 0.9.** -/
theorem ratio_num_le :
    Jbar * (eoffUp : ℝ) * (37 / 2000000) * (3 * ((2174093984726 : ℝ) / 10 ^ 15)) ≤ 9 / 10 := by
  unfold Jbar
  norm_num [qUp, qLo, eoffUp]

/-- **Ratio bound** with the real landing sum and `e^{λ off}`: for every finite landing set `S`, the transfer ratio
`(Σ_S e^{-λ |v|₁}) · e^{λ off} · ε* · F0` with `F0 = 3 F0x` is at most `0.9`. -/
theorem ratio_le (S : Finset V3) (hS : ∀ v ∈ S, 17 ≤ linf v) :
    (∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ))) * Real.exp (0.013 * 30) * (37 / 2000000) *
      (3 * ((2174093984726 : ℝ) / 10 ^ 15)) ≤ 9 / 10 := by
  have hJ := landing_bound S hS
  have hE := exp_off_le
  have hs0 : 0 ≤ ∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ)) := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hc : (0 : ℝ) ≤ (37 / 2000000) * (3 * ((2174093984726 : ℝ) / 10 ^ 15)) := by positivity
  have h1 : (∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ))) * Real.exp (0.013 * 30) ≤ Jbar * (eoffUp : ℝ) :=
    mul_le_mul hJ hE (Real.exp_pos _).le (le_trans hs0 hJ)
  calc (∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ))) * Real.exp (0.013 * 30) * (37 / 2000000) *
        (3 * ((2174093984726 : ℝ) / 10 ^ 15))
      = ((∑ v ∈ S, Real.exp (-0.013 * (l1 v : ℝ))) * Real.exp (0.013 * 30)) *
          ((37 / 2000000) * (3 * ((2174093984726 : ℝ) / 10 ^ 15))) := by ring
    _ ≤ (Jbar * (eoffUp : ℝ)) * ((37 / 2000000) * (3 * ((2174093984726 : ℝ) / 10 ^ 15))) :=
        mul_le_mul_of_nonneg_right h1 hc
    _ = Jbar * (eoffUp : ℝ) * (37 / 2000000) * (3 * ((2174093984726 : ℝ) / 10 ^ 15)) := by ring
    _ ≤ 9 / 10 := ratio_num_le

end QECD1
