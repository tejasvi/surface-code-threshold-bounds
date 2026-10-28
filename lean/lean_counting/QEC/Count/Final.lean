import QEC.Count.Assembly
import QEC.Count.CertSound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# From a checked certificate to the bound, for every `p ≤ p**`

The certificate's rows are checked at `p** = Pn / Pd`, `X = Xn / Xd` (weights `ω_E = p** X`, `ω_C = (1 - p**)/X`,
scaled by `Q = Pd Xd Xn`). For `0 < p ≤ p** < 1/2` take `X_p = X √(p**(1 - p) / (p (1 - p**))) ≥ X ≥ 1`. Then
`p X_p = ρ ω_E` and `(1 - p)/X_p = ρ ω_C` with `ρ = √(p(1 - p) / (p**(1 - p**))) ≤ 1`, so every row holds with
`λ_p = λ ρ`, and the start constant scales by `ρ^(K+2) ≤ 1`. `pfail_box_le` gives the bound.
-/

namespace QEC

open Finset QECComp

/-- `ρ = √(p (1 - p) / (p** (1 - p**)))`. -/
noncomputable def rhoOf (ps p : ℝ) : ℝ := Real.sqrt (p * (1 - p) / (ps * (1 - ps)))

namespace Final

/-- Scaling both weights by `ρ` scales the weight of a walk by `ρ^|w|`. -/
theorem wtW_smul (ρ a b : ℝ) : ∀ w : List (ℕ × Bool), wtW (ρ * a) (ρ * b) w = ρ ^ w.length * wtW a b w
  | [] => by simp [wtW]
  | x :: w => by
    have ih := wtW_smul ρ a b w
    unfold wtW at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    split_ifs <;> ring

/-- For `p ≤ ps < 1/2`: `p (1 - p) ≤ ps (1 - ps)`. -/
theorem pq_le {p ps : ℝ} (hp : p ≤ ps) (hps : ps < 1 / 2) : p * (1 - p) ≤ ps * (1 - ps) := by
  nlinarith

end Final

/-- **The bound of a box code from a checked certificate.** -/
theorem box_bound_of_cert (P : Params) (keys Hs : Array ℕ) (N : Fin P.n → ℕ) (a : Fin P.n)
    (Pn Pd Xn Xd : ℕ) (hwE : P.wE = Pn * Xn ^ 2) (hwC : P.wC = (Pd - Pn) * Xd ^ 2) (hQ : P.Q = Pd * Xd * Xn)
    (hPn : 0 < Pn) (hPd : 2 * Pn < Pd) (hXd : 0 < Xd) (hX : Xd ≤ Xn)
    (hn0 : 0 < P.n) (hlamD : 0 < P.lamD) (hlam : P.lamN < P.lamD) (hHmin : 0 < P.Hmin) (hK0d : 0 < P.K0d)
    (hrows : ∀ i < keys.size, rowCheck P keys Hs i = true) (hdfs : dfsOK P keys P.K [] = true)
    (hst : startOK P keys Hs = true) (hK : P.K + 1 ≤ N a) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ (Pn : ℝ) / Pd) :
    PfailMW (boxEdges P.n N a) p ≤
      #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) * ((P.K0n : ℝ) / P.K0d) *
        ((P.lamN : ℝ) / P.lamD * rhoOf ((Pn : ℝ) / Pd) p) ^ (N a - 1 - P.K) /
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
  have hQ0 : 0 < P.Q := by
    rw [hQ]
    exact Nat.mul_pos (Nat.mul_pos hPdN hXd) (lt_of_lt_of_le hXd hX)
  set ps : ℝ := (Pn : ℝ) / Pd with hps
  have hps0 : 0 < ps := div_pos hPn0 hPd0
  have hps2 : ps < 1 / 2 := by
    rw [hps, div_lt_iff₀ hPd0]
    linarith
  have hp1 : p < 1 := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1ps : 0 < 1 - ps := by linarith
  -- `ρ = √B` and `r = √A`
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
  -- `p r = ps ρ`
  have hI1 : p * r = ps * ρ := by
    have e1 : p * r = Real.sqrt (p ^ 2 * A) := by
      rw [Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp0.le]
    have e2 : ps * ρ = Real.sqrt (ps ^ 2 * B) := by
      rw [hρB, Real.sqrt_mul (sq_nonneg ps), Real.sqrt_sq hps0.le]
    rw [e1, e2]
    congr 1
    rw [hA, hB]
    field_simp
  -- `r ρ = (1 - p) / (1 - ps)`
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
  have hωE : ωEof P = ps * Xs := by
    unfold ωEof
    rw [hwE, hQ, hps, hXs]
    push_cast
    field_simp
  have hωC : ωCof P = (1 - ps) / Xs := by
    unfold ωCof
    rw [hwC, hQ, hps, hXs, Nat.cast_mul, Nat.cast_sub (by omega : Pn ≤ Pd)]
    push_cast
    field_simp
  have hωE0 : 0 ≤ ωEof P := by rw [hωE]; exact (mul_pos hps0 hXs0).le
  have hωC0 : 0 ≤ ωCof P := by rw [hωC]; exact (div_pos h1ps hXs0).le
  have hwEp : p * Xp = ρ * ωEof P := by
    rw [hωE, hXp]
    calc p * (Xs * r) = Xs * (p * r) := by ring
      _ = Xs * (ps * ρ) := by rw [hI1]
      _ = ρ * (ps * Xs) := by ring
  have hwCp : (1 - p) / Xp = ρ * ωCof P := by
    rw [hωC, hXp]
    have h1 : 1 - p = (1 - ps) * (r * ρ) := by rw [hI2]; field_simp
    rw [h1]
    field_simp
  -- the row factor at `p`
  have hlamD0 : (0 : ℝ) < P.lamD := by exact_mod_cast hlamD
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
  -- the rows at `p`
  have hrow : ∀ s, IsSt P keys s → ∑ x ∈ (cands P.n).filter (Succ P.n P.c s),
      wtW (p * Xp) ((1 - p) / Xp) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) ≤ lam * (Hof P keys Hs s : ℝ) := by
    intro s hs
    have h := cert_rows P keys Hs hn0 hQ0 hlamD hrows s hs
    rw [hwEp, hwCp]
    calc ∑ x ∈ (cands P.n).filter (Succ P.n P.c s),
          wtW (ρ * ωEof P) (ρ * ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ)
        = ρ * ∑ x ∈ (cands P.n).filter (Succ P.n P.c s),
            wtW (ωEof P) (ωCof P) [x] * (Hof P keys Hs (s ++ [x]).tail : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Final.wtW_smul]
          simp only [List.length_singleton, pow_one]
          ring
      _ ≤ ρ * (lamOf P * Hof P keys Hs s) := mul_le_mul_of_nonneg_left h hρ0.le
      _ = lam * (Hof P keys Hs s : ℝ) := by
          rw [hlam']
          unfold lamOf
          ring
  -- the start term at `p`
  have hstart : (p * Xp + (1 - p) / Xp) ^ 2 *
      ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (p * Xp) ((1 - p) / Xp) s * (Hof P keys Hs s : ℝ)) /
        P.Hmin) ≤ (P.K0n : ℝ) / P.K0d := by
    rw [hwEp, hwCp]
    have hsum : ∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ρ * ωEof P) (ρ * ωCof P) s *
        (Hof P keys Hs s : ℝ) = ρ ^ P.K * ∑ s ∈ (pats P.n P.K).filter (IsSt P keys),
          wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hlen : s.length = P.K := by
        have := (Finset.mem_filter.mp hs).2
        unfold IsSt at this
        exact this.1
      rw [Final.wtW_smul, hlen]
      ring
    rw [hsum]
    have hcs := cert_startSum P keys Hs hn0 hQ0 hK0d hHmin hrows hst
    have hS0 : 0 ≤ ∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ) :=
      Finset.sum_nonneg (fun s _ => mul_nonneg (Counting.wtW_nonneg hωE0 hωC0 s) (Nat.cast_nonneg _))
    have hT0 : 0 ≤ (ωEof P + ωCof P) ^ 2 *
        ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s * (Hof P keys Hs s : ℝ)) /
          P.Hmin) :=
      mul_nonneg (sq_nonneg _) (div_nonneg hS0 hHminR.le)
    have hρK : ρ ^ (P.K + 2) ≤ 1 := pow_le_one₀ hρ0.le hρ1
    calc (ρ * ωEof P + ρ * ωCof P) ^ 2 *
          (ρ ^ P.K * (∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s *
            (Hof P keys Hs s : ℝ)) / P.Hmin)
        = ρ ^ (P.K + 2) * ((ωEof P + ωCof P) ^ 2 *
            ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s *
              (Hof P keys Hs s : ℝ)) / P.Hmin)) := by ring
      _ ≤ 1 * ((ωEof P + ωCof P) ^ 2 *
            ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (ωEof P) (ωCof P) s *
              (Hof P keys Hs s : ℝ)) / P.Hmin)) := mul_le_mul_of_nonneg_right hρK hT0
      _ ≤ (P.K0n : ℝ) / P.K0d := by rw [one_mul]; exact hcs
  -- the assembly
  have hmain := pfail_box_le P.n N a P.c P.K hp0 hp1 hXp1 hlam0 hlam1 hHminR (IsSt P keys)
    (fun s => (Hof P keys Hs s : ℝ))
    (fun s hs => by unfold IsSt at hs; exact ⟨hs.1, hs.2.1⟩)
    (fun s hs => by exact_mod_cast cert_pos P keys Hs hrows s hs)
    (cert_start P keys hn0 hdfs) (cert_closed P keys Hs hn0 hrows) hrow hK
  have hface : (0 : ℝ) ≤ #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) := Nat.cast_nonneg _
  have hq : 0 ≤ lam ^ (N a - 1 - P.K) / (1 - lam) := div_nonneg (pow_nonneg hlam0 _) (by linarith)
  calc PfailMW (boxEdges P.n N a) p
      ≤ #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) * (p * Xp + (1 - p) / Xp) ^ 2 *
          ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (p * Xp) ((1 - p) / Xp) s *
            (Hof P keys Hs s : ℝ)) / P.Hmin) * (lam ^ (N a - 1 - P.K) / (1 - lam)) := hmain
    _ = #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) * ((p * Xp + (1 - p) / Xp) ^ 2 *
          ((∑ s ∈ (pats P.n P.K).filter (IsSt P keys), wtW (p * Xp) ((1 - p) / Xp) s *
            (Hof P keys Hs s : ℝ)) / P.Hmin)) * (lam ^ (N a - 1 - P.K) / (1 - lam)) := by ring
    _ ≤ #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) * ((P.K0n : ℝ) / P.K0d) *
          (lam ^ (N a - 1 - P.K) / (1 - lam)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstart hface) hq
    _ = #(univ.filter (fun u : BoxV P.n N => (u a : ℕ) = 0)) * ((P.K0n : ℝ) / P.K0d) *
          lam ^ (N a - 1 - P.K) / (1 - lam) := by ring

end QEC
