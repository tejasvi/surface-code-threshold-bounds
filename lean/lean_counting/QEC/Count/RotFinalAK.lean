import QEC.Count.CertSoundAK
import QEC.Count.RotSoundA
import QEC.Count.RotAssemblyA
import QEC.Count.CountingT
import QEC.Count.Final
import QEC.Count.RotLayout

/-!
# The rotated code from an augmented certificate checked in kernel form, for every `p ≤ p**`

The proof of `rot_bound_of_certA` (`RotFinalA.lean`) with the kernel-form certificate `CertOKAK` (`CertSoundAK.lean`)
in place of `CertOKA`. As in `Final.lean`: for `0 < p ≤ p** < 1/2` the weights at `p` are `ρ ω_E`, `ρ ω_C`
(`X_p = X √(p**(1-p)/(p(1-p**)))`), so the rows hold with `λ ρ` (`certAK_rows`) and the start sums scale by `ρ^K`
(`certAK_startSum`); the counting with
height-dependent exclusions (`sum_legal_leT` with `nxtA`, `ExA`), the soundness of the region-aware check in the
rotated region (`rot_not_exclA`, strict bottom side `hN = 0`) and the assembly `pfail_rot_leA` give
`P_fail ≤ 2d · K0 · (λρ)^(d-2-K) / (1 - λρ)` for every odd `d ≥ K + 2` (the layout lemma `PfailRot_eq` turns the
region code into the rotated code).
-/

namespace QEC

open Finset QECComp

/-- **The bound of the rotated code from an augmented certificate checked in kernel form.** -/
theorem rot_bound_of_certAK (P : ParamsA) (fN fB : ℕ → Option (ℕ × ℕ)) (eN eB : List (ℕ × ℕ × ℕ))
    (hc : CertOKAK P fN fB eN eB) (d : ℕ)
    (hd3 : 3 ≤ d) (hodd : Odd d)
    (Pn Pd Xn Xd : ℕ) (hwE : P.wE = Pn * Xn ^ 2) (hwC : P.wC = (Pd - Pn) * Xd ^ 2) (hQ : P.Q = Pd * Xd * Xn)
    (hPn : 0 < Pn) (hPd : 2 * Pn < Pd) (hXd : 0 < Xd) (hX : Xd ≤ Xn)
    (hlam : P.lamN < P.lamD) (hHmin : 0 < P.Hmin) (hK : P.K + 2 ≤ d) {p : ℝ} (hp0 : 0 < p)
    (hp : p ≤ (Pn : ℝ) / Pd) :
    PfailRot d p ≤
      2 * d * ((P.K0n : ℝ) / P.K0d) * ((P.lamN : ℝ) / P.lamD * rhoOf ((Pn : ℝ) / Pd) p) ^ (d - 2 - P.K) /
        (1 - (P.lamN : ℝ) / P.lamD * rhoOf ((Pn : ℝ) / Pd) p) := by
  classical
  rw [PfailRot_eq d hd3 hodd p]
  -- the parameters as reals
  have hPdN : 0 < Pd := by omega
  have hPd0 : (0 : ℝ) < Pd := by exact_mod_cast hPdN
  have hPn0 : (0 : ℝ) < Pn := by exact_mod_cast hPn
  have hPd2 : (2 : ℝ) * Pn < Pd := by exact_mod_cast hPd
  have hXd0 : (0 : ℝ) < Xd := by exact_mod_cast hXd
  have hXdn : (Xd : ℝ) ≤ Xn := by exact_mod_cast hX
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
  set IsSt := IsStAK P fN fB with hIsSt
  set H : List (ℕ × Bool) → ℤ → ℝ := fun s h0 => (HofAK P fN fB s h0 : ℝ) with hH
  -- the rows at `p`
  have hrow : ∀ s h0, IsSt s h0 → ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
      wtW (p * Xp) ((1 - p) / Xp) [x] * H (s ++ [x]).tail (offAt nxtA h0 s 1) ≤ lam * H s h0 := by
    intro s h0 hs
    have h := certAK_rows hc hs
    rw [hwEp, hwCp]
    calc ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
          wtW (ρ * ωE) (ρ * ωC) [x] * H (s ++ [x]).tail (offAt nxtA h0 s 1)
        = ρ * ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
            wtW ωE ωC [x] * (HofAK P fN fB (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Final.wtW_smul]
          simp only [List.length_singleton, pow_one, hH]
          ring
      _ ≤ ρ * ((P.lamN : ℝ) / P.lamD * HofAK P fN fB s h0) := mul_le_mul_of_nonneg_left h hρ0.le
      _ = lam * H s h0 := by
          rw [hlam', hH]
          ring
  -- the start sums at `p`
  have hlenK : ∀ s h0, IsSt s h0 → s.length = P.K := fun s h0 hs => hs.1
  have hsumpos : 0 < p * Xp + (1 - p) / Xp := by
    have := mul_pos hp0 hXp0
    have := div_pos h1p hXp0
    linarith
  set Bc : ℝ := ((P.K0n : ℝ) / P.K0d) / (p * Xp + (1 - p) / Xp) ^ 2 with hBc
  have hBc0 : 0 ≤ Bc := div_nonneg hK0R (sq_nonneg _)
  have hstartB : ∀ h0 : ℤ, 0 ≤ h0 →
      (∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW (p * Xp) ((1 - p) / Xp) s * H s h0) / P.Hmin ≤ Bc := by
    intro h0 hh
    have hcs := certAK_startSum hc hh
    have hS0 : 0 ≤ ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0 :=
      Finset.sum_nonneg (fun s _ => mul_nonneg (Counting.wtW_nonneg hωE0 hωC0 s) (Nat.cast_nonneg _))
    have hsum : ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW (p * Xp) ((1 - p) / Xp) s * H s h0 =
        ρ ^ P.K * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0 := by
      rw [hwEp, hwCp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Final.wtW_smul, hlenK s h0 (Finset.mem_filter.mp hs).2]
      ring
    have hsq : 0 < (p * Xp + (1 - p) / Xp) ^ 2 := by positivity
    rw [hsum, hBc, le_div_iff₀ hsq, div_mul_eq_mul_div, div_le_iff₀ hHminR]
    have hρK : ρ ^ (P.K + 2) ≤ 1 := pow_le_one₀ hρ0.le hρ1
    have hT0 : 0 ≤ (ωE + ωC) ^ 2 * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0 :=
      mul_nonneg (sq_nonneg _) hS0
    rw [hwEp, hwCp]
    calc ρ ^ P.K * (∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0) *
          (ρ * ωE + ρ * ωC) ^ 2
        = ρ ^ (P.K + 2) * ((ωE + ωC) ^ 2 *
            ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0) := by ring
      _ ≤ 1 * ((ωE + ωC) ^ 2 * ∑ s ∈ (pats 2 P.K).filter (fun s => IsSt s h0), wtW ωE ωC s * H s h0) :=
          mul_le_mul_of_nonneg_right hρK hT0
      _ ≤ (P.K0n : ℝ) / P.K0d * P.Hmin := by rw [one_mul]; exact hcs
  -- the counting bound from every start height
  have hcount : ∀ h0 : ℤ, 0 ≤ h0 → ∀ n, P.K ≤ n →
      ∑ w ∈ (pats 2 n).filter (LegalG nxtA (ExA P.hN) (P.K + 1) h0),
        wtW (p * Xp) ((1 - p) / Xp) w ≤ lam ^ (n - P.K) * Bc := by
    intro h0 hh n hn
    have h := sum_legal_leT nxtA (ExA P.hN) P.K (mul_pos hp0 hXp0).le (div_pos h1p hXp0).le hlam0 hHminR
      IsSt H (fun s h0 hs => ⟨hs.1, hs.2.1⟩)
      (fun s h0 hs => by simp only [hH]; exact_mod_cast certAK_pos hc hs)
      (fun s h0 hs x hx => certAK_closed hc hs hx) hrow h0
      (fun s hs hleg => certAK_start hc hh hs hleg) n hn
    exact le_trans h (mul_le_mul_of_nonneg_left (hstartB h0 hh) (pow_nonneg hlam0 _))
  -- the window property
  have hwin : ∀ E C : Finset (Sym2 (RVx (RChk d) (ROut d))), IsPhiMinFailR (rotEdges d) rotSide (phiRot cA) E C →
      ∀ (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) (v0 : RChk d) (rest : List (RChk d)),
        AdjChainR (v0 :: rest) → (v0 :: rest).Nodup →
        (∀ uv ∈ pairs (v0 :: rest), (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C)) →
        rest.length < d → ¬ ExclA P.hN (heightR v0) (patOfR S (v0 :: rest)) := by
    intro E C hC S v0 rest hadj hnd hS hlen
    rw [hc.hN0]
    exact rot_not_exclA hC S v0 rest hadj hnd hS hlen
  have hmain := pfail_rot_leA d P.K P.hN hp0 hp1 hXp1 hlam0 hlam1 hBc0 hwin hcount hK
  rw [card_side1 d hd3 hodd] at hmain
  calc PfailMWR (rotEdges d) rotSide p
      ≤ (d : ℝ) * 2 * (p * Xp + (1 - p) / Xp) ^ 2 * Bc * (lam ^ (d - 2 - P.K) / (1 - lam)) := hmain
    _ = 2 * d * ((P.K0n : ℝ) / P.K0d) * lam ^ (d - 2 - P.K) / (1 - lam) := by
        rw [hBc]
        field_simp

end QEC

#print axioms QEC.rot_bound_of_certAK
