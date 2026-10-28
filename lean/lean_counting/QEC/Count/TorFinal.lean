import QEC.Count.CertSoundT
import QEC.Count.CountingT
import QEC.Count.TorSound
import QEC.Count.TorAssembly
import QEC.Count.Final

/-!
# The toric code from a checked seam certificate, for every `p ≤ p**` (Theorem A′, final step)

The certificate's rows are checked at `p** = Pn / Pd`, `X = Xn / Xd`. For `0 < p ≤ p** < 1/2` take
`X_p = X √(p**(1 - p) / (p (1 - p**)))`, so that `p X_p = ρ ω_E` and `(1 - p)/X_p = ρ ω_C` with
`ρ = √(p(1 - p) / (p**(1 - p**))) ≤ 1` (as in `Final.lean`): the rows hold with `λ ρ` (`certT_rows`), the start
sums scale by `ρ^K` (`certT_startSum`), and `pfail_tor_le` with `sum_legal_leT` (counting) and
`tor_window_not_excl` (soundness of the seam check on the torus) gives
`P_fail ≤ L² · K0 · (λρ)^(L-1-K) / (1 - λρ)` for every `L ≥ max(L0, 4(HC + K) + 4)`.
-/

namespace QEC

open Finset QECComp
open scoped symmDiff

/-- **The bound of the toric code from a checked seam certificate.** -/
theorem tor_bound_of_cert (P : ParamsT) (nk nG bk bH : Array ℕ) (hc : CertOKT P nk nG bk bH)
    (Pn Pd Xn Xd : ℕ) (hwE : P.wE = Pn * Xn ^ 2) (hwC : P.wC = (Pd - Pn) * Xd ^ 2) (hQ : P.Q = Pd * Xd * Xn)
    (hPn : 0 < Pn) (hPd : 2 * Pn < Pd) (hXd : 0 < Xd) (hX : Xd ≤ Xn)
    (hlam : P.lamN < P.lamD) (hHmin : 0 < P.Hmin) (hK0d : 0 < P.K0d)
    {L : ℕ} (hL0 : P.L0 ≤ L) (hL : 4 * (P.HC + P.K) + 4 ≤ L) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ (Pn : ℝ) / Pd) :
    PfailTor L p ≤ (L : ℝ) ^ 2 * ((P.K0n : ℝ) / P.K0d) *
        ((P.lamN : ℝ) / P.lamD * rhoOf ((Pn : ℝ) / Pd) p) ^ (L - 1 - P.K) /
          (1 - (P.lamN : ℝ) / P.lamD * rhoOf ((Pn : ℝ) / Pd) p) := by
  classical
  -- the parameters as reals
  have hPdN : 0 < Pd := by omega
  have hPd0 : (0 : ℝ) < Pd := by exact_mod_cast hPdN
  have hPn0 : (0 : ℝ) < Pn := by exact_mod_cast hPn
  have hPd2 : (2 : ℝ) * Pn < Pd := by exact_mod_cast hPd
  have hXd0 : (0 : ℝ) < Xd := by exact_mod_cast hXd
  have hXdn : (Xd : ℝ) ≤ Xn := by exact_mod_cast hX
  have hXn0 : (0 : ℝ) < Xn := lt_of_lt_of_le hXd0 hXdn
  have hQ0 : 0 < P.Q := hc.hQ
  have hQR : (0 : ℝ) < P.Q := by exact_mod_cast hQ0
  set ps : ℝ := (Pn : ℝ) / Pd with hps
  have hps0 : 0 < ps := div_pos hPn0 hPd0
  have hps2 : ps < 1 / 2 := by
    rw [hps, div_lt_iff₀ hPd0]
    linarith
  have hp1 : p < 1 := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1ps : 0 < 1 - ps := by linarith
  set A : ℝ := ps * (1 - p) / (p * (1 - ps)) with hA
  set B : ℝ := p * (1 - p) / (ps * (1 - ps)) with hB
  have hA0 : 0 < A := div_pos (mul_pos hps0 h1p) (mul_pos hp0 h1ps)
  have hB0 : 0 < B := div_pos (mul_pos hp0 h1p) (mul_pos hps0 h1ps)
  have hB1 : B ≤ 1 := by
    rw [hB, div_le_one (mul_pos hps0 h1ps)]
    exact Final.pq_le hp hps2
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ (mul_pos hp0 h1ps), one_mul]
    nlinarith
  set ρ := rhoOf ps p with hρ
  have hρB : ρ = Real.sqrt B := rfl
  set r := Real.sqrt A with hr
  have hρ0 : 0 < ρ := by rw [hρB]; exact Real.sqrt_pos.mpr hB0
  have hρ1 : ρ ≤ 1 := by
    rw [hρB]
    calc Real.sqrt B ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hB1
      _ = 1 := Real.sqrt_one
  have hr1 : 1 ≤ r := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt A := Real.sqrt_le_sqrt hA1
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hI1 : p * r = ps * ρ := by
    have e1 : p * r = Real.sqrt (p ^ 2 * A) := by
      rw [Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp0.le]
    have e2 : ps * ρ = Real.sqrt (ps ^ 2 * B) := by
      rw [hρB, Real.sqrt_mul (sq_nonneg ps), Real.sqrt_sq hps0.le]
    rw [e1, e2]
    congr 1
    rw [hA, hB]
    field_simp
  have hI2 : r * ρ = (1 - p) / (1 - ps) := by
    have e1 : r * ρ = Real.sqrt (A * B) := by rw [hρB, hr, Real.sqrt_mul hA0.le]
    rw [e1]
    have e2 : A * B = ((1 - p) / (1 - ps)) ^ 2 := by
      rw [hA, hB]
      field_simp
    rw [e2, Real.sqrt_sq (div_nonneg h1p.le h1ps.le)]
  -- the weights at `p`
  set Xs : ℝ := (Xn : ℝ) / Xd with hXs
  have hXs1 : 1 ≤ Xs := by rw [hXs, le_div_iff₀ hXd0, one_mul]; exact hXdn
  have hXs0 : 0 < Xs := lt_of_lt_of_le one_pos hXs1
  set Xp : ℝ := Xs * r with hXp
  have hXp1 : 1 ≤ Xp := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ Xs * r := mul_le_mul hXs1 hr1 zero_le_one hXs0.le
  have hXp0 : 0 < Xp := lt_of_lt_of_le one_pos hXp1
  set ωE : ℝ := (P.wE : ℝ) / P.Q with hωEd
  set ωC : ℝ := (P.wC : ℝ) / P.Q with hωCd
  have hωE : ωE = ps * Xs := by
    rw [hωEd, hwE, hQ, hps, hXs]
    push_cast
    field_simp
  have hωC : ωC = (1 - ps) / Xs := by
    rw [hωCd, hwC, hQ, hps, hXs, Nat.cast_mul, Nat.cast_sub (by omega : Pn ≤ Pd)]
    push_cast
    field_simp
  have hωE0 : 0 ≤ ωE := by rw [hωE]; exact (mul_pos hps0 hXs0).le
  have hωC0 : 0 ≤ ωC := by rw [hωC]; exact (div_pos h1ps hXs0).le
  have hwEp : p * Xp = ρ * ωE := by
    rw [hωE, hXp]
    calc p * (Xs * r) = Xs * (p * r) := by ring
      _ = Xs * (ps * ρ) := by rw [hI1]
      _ = ρ * (ps * Xs) := by ring
  have hwCp : (1 - p) / Xp = ρ * ωC := by
    rw [hωC, hXp]
    have h1 : 1 - p = (1 - ps) * (r * ρ) := by rw [hI2]; field_simp
    rw [h1]
    field_simp
  -- the row factor at `p`
  have hlamD0 : (0 : ℝ) < P.lamD := by exact_mod_cast hc.hlamD
  have hlamq : (P.lamN : ℝ) / P.lamD < 1 := by
    rw [div_lt_one hlamD0]
    exact_mod_cast hlam
  have hlamq0 : 0 ≤ (P.lamN : ℝ) / P.lamD := div_nonneg (Nat.cast_nonneg _) hlamD0.le
  set lam := (P.lamN : ℝ) / P.lamD * ρ with hlam'
  have hlam0 : 0 ≤ lam := mul_nonneg hlamq0 hρ0.le
  have hlam1 : lam < 1 := by
    calc lam = (P.lamN : ℝ) / P.lamD * ρ := rfl
      _ ≤ (P.lamN : ℝ) / P.lamD * 1 := mul_le_mul_of_nonneg_left hρ1 hlamq0
      _ < 1 := by rw [mul_one]; exact hlamq
  have hHminR : (0 : ℝ) < P.Hmin := by exact_mod_cast hHmin
  have hK0R : (0 : ℝ) ≤ (P.K0n : ℝ) / P.K0d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  set IsSt := IsStT P nk nG bk bH L with hIsSt
  set H : List (ℕ × Bool) → ℤ → ℝ := fun s o => (HofT P nk nG bk bH L s o : ℝ) with hH
  -- the rows at `p`
  have hrow : ∀ s o, IsSt s o → ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
      wtW (p * Xp) ((1 - p) / Xp) [x] * H (s ++ [x]).tail (offAt (nxtT L) o s 1) ≤ lam * H s o := by
    intro s o hs
    have h := certT_rows hc hL hs
    rw [hwEp, hwCp]
    calc ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
          wtW (ρ * ωE) (ρ * ωC) [x] * H (s ++ [x]).tail (offAt (nxtT L) o s 1)
        = ρ * ∑ x ∈ (cands 2).filter (SuccG (nxtT L) (ExclT P.L0) s o),
            wtW ωE ωC [x] * (HofT P nk nG bk bH L (s ++ [x]).tail (offAt (nxtT L) o s 1) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Final.wtW_smul]
          simp only [List.length_singleton, pow_one, hH]
          ring
      _ ≤ ρ * ((P.lamN : ℝ) / P.lamD * HofT P nk nG bk bH L s o) := mul_le_mul_of_nonneg_left h hρ0.le
      _ = lam * H s o := by
          rw [hlam', hH]
          ring
  -- the start sums at `p`
  have hlenK : ∀ s o, IsSt s o → s.length = P.K := fun s o hs => hs.2.1
  set Bc : ℝ := ((P.K0n : ℝ) / P.K0d) / (p * Xp + (1 - p) / Xp) with hBc
  have hsumpos : 0 < p * Xp + (1 - p) / Xp := by
    have := mul_pos hp0 hXp0
    have := div_pos h1p hXp0
    linarith
  have hBc0 : 0 ≤ Bc := div_nonneg hK0R hsumpos.le
  have hstartB : ∀ o, qoffZ L o = o →
      (∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW (p * Xp) ((1 - p) / Xp) s * H s o) / P.Hmin ≤ Bc := by
    intro o ho
    have hcs := certT_startSum hc hL ho
    have hS0 : 0 ≤ ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o :=
      Finset.sum_nonneg (fun s _ => mul_nonneg (Counting.wtW_nonneg hωE0 hωC0 s) (Nat.cast_nonneg _))
    have hsum : ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW (p * Xp) ((1 - p) / Xp) s * H s o =
        ρ ^ P.K * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o := by
      rw [hwEp, hwCp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Final.wtW_smul, hlenK s o (Finset.mem_filter.mp hs).2]
      ring
    rw [hsum, hBc, le_div_iff₀ hsumpos, div_mul_eq_mul_div, div_le_iff₀ hHminR]
    have hρK : ρ ^ (P.K + 1) ≤ 1 := pow_le_one₀ hρ0.le hρ1
    have hT0 : 0 ≤ (ωE + ωC) * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o :=
      mul_nonneg (add_nonneg hωE0 hωC0) hS0
    rw [hwEp, hwCp]
    calc ρ ^ P.K * (∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o) * (ρ * ωE + ρ * ωC)
        = ρ ^ (P.K + 1) * ((ωE + ωC) *
            ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o) := by ring
      _ ≤ 1 * ((ωE + ωC) * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s o), wtW ωE ωC s * H s o) :=
          mul_le_mul_of_nonneg_right hρK hT0
      _ ≤ (P.K0n : ℝ) / P.K0d * P.Hmin := by rw [one_mul]; exact hcs
  -- the counting bound from every start vertex
  have hcount : ∀ (v : TorV L) (n : ℕ), P.K ≤ n →
      ∑ w ∈ (pats 2 n).filter (LegalG (nxtT L) (ExclT P.L0) (P.K + 1) (qoff v)),
        wtW (p * Xp) ((1 - p) / Xp) w ≤ lam ^ (n - P.K) * Bc := by
    intro v n hn
    have hqv : qoffZ L (qoff v) = qoff v := SeamShift.qoffZ_idem _
    have h := sum_legal_leT (nxtT L) (ExclT P.L0) P.K (mul_pos hp0 hXp0).le (div_pos h1p hXp0).le hlam0 hHminR
      IsSt H (fun s o hs => ⟨hs.2.1, hs.2.2.1⟩)
      (fun s o hs => by simp only [hH]; exact_mod_cast certT_pos hc hs)
      (fun s o hs x hx => certT_closed hc hL hs hx) hrow (qoff v)
      (fun s hs hleg => certT_start hc hL hqv hs hleg) n hn
    exact le_trans h (mul_le_mul_of_nonneg_left (hstartB (qoff v) hqv) (pow_nonneg hlam0 _))
  -- the window property
  have hwin : ∀ E C : Finset (Sym2 (Vx (TorV L))), E ⊆ torEdges L → IsPhiMinFailT (phiTor L) E C →
      ∀ vs : List (TorV L), vs.Nodup → (vs.map Vx.det).IsChain (decGraph (C ∆ E)).Adj →
      ∀ i m, 2 ≤ m → m ≤ P.K + 1 → ∀ h : i + m < vs.length,
        ¬ ExclT P.L0 (qoff (vs[i]'(by omega))) (((patOfT E vs).drop i).take m) :=
    fun E C hE hC vs hnd hch i m hm2 hmM h =>
      tor_window_not_excl (M := P.K + 1) hL0 (by have := hc.hHC; omega) hE hC hnd hch hm2 hmM h
  have hmain := pfail_tor_le L P.L0 P.K (by have := hc.hHC; omega) hp0 hp1 hXp1 hlam0 hlam1 hBc0 hwin hcount
  calc PfailTor L p ≤ (L : ℝ) ^ 2 * (p * Xp + (1 - p) / Xp) * Bc * (lam ^ (L - 1 - P.K) / (1 - lam)) := hmain
    _ = (L : ℝ) ^ 2 * ((P.K0n : ℝ) / P.K0d) * lam ^ (L - 1 - P.K) / (1 - lam) := by
        rw [hBc]
        field_simp

end QEC
