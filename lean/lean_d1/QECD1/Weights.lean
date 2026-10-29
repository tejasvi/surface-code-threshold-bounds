import QECD1.Rooting
import QECD1.WitCount
import QECD1.CertTabCheck

/-!
# The real weights of the refined 3D T2 count and their certificate bounds (`λ = 14/1000`, `s = 7/1000`)


Real weights (`κ = 1` so `μ = λ`):

* steps and links `tw v = ε e^{λ |v|₁ + s v_y}`, leaves `ε`, with `ε = ε* = 1.85e-5`;
* the mark in route state `m` (`markW m = onW m + offW`): on-route witness walks
  `Σ_{c ≤ 4} ε^c N_c(z_m) + y^5/(1 - y)` with `y = ε |S0|`, and ALL walks `1/(1 - y)` at `Asp` (`m = 34`);
  off-route `ε |S1| exc/(1 - y)` with the certified excursion factor `exc = exB 0 / Qden`.

Certificate bounds, each against the tables of `QECD1.Tab` (rational upper bounds `muQ ≥ e^λ`, `sUpQ ≥ e^s`,
`sInvQ ≥ e^{-s}` by `Real.exp_bound`):

* `step_dom`: the fibre sums `Σ_{v ∈ S0, v_i = j - 8} tw v ≤ st j / Qden` for the axes t, x (`stT`) and y (`stY`)
  (`stepQ_le_T`, `stepQ_le_X`, `stepQ_le_Y`, kernel sums over `S0`);
* `leaf_dom`: `ε · |fibre| ≤ lf j / Qden` (`leafQ_le`);
* `link_dom`: `Σ_{v ∈ S1} tw v ≤ linkT / Qden` (box factorization, `S1 = box 24 \ box 4`);
* `mark_dom`: `markW m ≤ mkT m / Qden` for `m < 52` (`markQ_le`, with `Ncnt_eq_NcT`).
-/

namespace QECD1

open QECD1.Tab

/-! ### Parameters and exponential bounds -/

/-- `ε* = 1.85e-5`. -/
noncomputable def eps : ℝ := 37 / 2000000
/-- `λ = 0.014` (and `μ = κ λ = λ`). -/
noncomputable def lam : ℝ := 14 / 1000
/-- The height tilt `s = 0.007`. -/
noncomputable def sT : ℝ := 7 / 1000

def epsQ : ℚ := 37 / 2000000
def muQ : ℚ := 10141 / 10000
def sUpQ : ℚ := 100703 / 100000
def sInvQ : ℚ := 99303 / 100000

theorem eps_eq : eps = (epsQ : ℝ) := by norm_num [eps, epsQ]

theorem eps_nonneg : 0 ≤ eps := by norm_num [eps]

theorem exp_lam_le : Real.exp lam ≤ (muQ : ℝ) := by
  have h := Real.exp_bound (x := 14 / 1000) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [muQ, lam]
  linarith [h.1, h.2]

theorem exp_s_le : Real.exp sT ≤ (sUpQ : ℝ) := by
  have h := Real.exp_bound (x := 7 / 1000) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num [sUpQ, sT]
  linarith [h.1, h.2]

theorem exp_neg_s_le : Real.exp (-sT) ≤ (sInvQ : ℝ) := by
  have h := Real.exp_bound (x := -(7 / 1000)) (by norm_num [abs_of_neg]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_neg] at h
  rw [abs_le] at h
  norm_num [sInvQ, sT]
  linarith [h.1, h.2]

/-- The rational tilt factor of the `y` coordinate. -/
def syQ (c : ℤ) : ℚ := if 0 ≤ c then sUpQ ^ c.natAbs else sInvQ ^ c.natAbs

/-- The rational bound of `e^{λ |v|₁ + s v_y}`. -/
def rQ (v : V3) : ℚ := muQ ^ l1 v * syQ v.2.2

theorem syQ_nonneg (c : ℤ) : 0 ≤ syQ c := by
  unfold syQ
  split_ifs
  · exact pow_nonneg (by norm_num [sUpQ]) _
  · exact pow_nonneg (by norm_num [sInvQ]) _

theorem rQ_nonneg (v : V3) : 0 ≤ rQ v := mul_nonneg (pow_nonneg (by norm_num [muQ]) _) (syQ_nonneg _)

theorem exp_le_rQ (v : V3) : Real.exp (lam * l1 v + sT * v.2.2) ≤ (rQ v : ℝ) := by
  rw [Real.exp_add]
  have h1 : Real.exp (lam * l1 v) ≤ (muQ : ℝ) ^ l1 v := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_lam_le _
  have h2 : Real.exp (sT * v.2.2) ≤ (syQ v.2.2 : ℝ) := by
    unfold syQ
    split_ifs with hc
    · have hcast : (v.2.2 : ℝ) = ((v.2.2.natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact (abs_of_nonneg (by exact_mod_cast hc)).symm
      rw [hcast, mul_comm, Real.exp_nat_mul]
      push_cast
      exact pow_le_pow_left₀ (Real.exp_pos _).le exp_s_le _
    · have hcast : sT * (v.2.2 : ℝ) = ((v.2.2.natAbs : ℕ) : ℝ) * (-sT) := by
        have h0' : ((v.2.2.natAbs : ℕ) : ℝ) = -(v.2.2 : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
          exact abs_of_neg (by exact_mod_cast (not_le.1 hc))
        rw [h0']
        ring
      rw [hcast, Real.exp_nat_mul]
      push_cast
      exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_s_le _
  unfold rQ
  push_cast
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (pow_nonneg (by norm_num [muQ]) _)

/-! ### Weights, offsets, coordinates -/

/-- The T2 weight of a step or link offset: `ε e^{λ |v|₁ + s v_y}`. -/
noncomputable def tw (v : V3) : ℝ := eps * Real.exp (lam * l1 v + sT * v.2.2)

theorem tw_nonneg (v : V3) : 0 ≤ tw v := mul_nonneg eps_nonneg (Real.exp_pos _).le

theorem tw_le (v : V3) : tw v ≤ ((epsQ * rQ v : ℚ) : ℝ) := by
  unfold tw
  rw [eps_eq]
  push_cast
  exact mul_le_mul_of_nonneg_left (exp_le_rQ v) (by norm_num [epsQ])

/-- The link offsets `S1 = {D ≤ |v|∞ ≤ A1}` (`D = 5`, `A1 = 24`). -/
def S1off : Finset V3 := (box 24).filter fun v => 5 ≤ linf v

theorem S1off_eq_const : S1off = (box Const.A1).filter fun v => Const.D ≤ linf v := by
  rw [Const.A1_val, Const.D_val]
  rfl

theorem S1off_eq : S1off = box 24 \ box 4 := by
  ext v
  simp only [S1off, Finset.mem_filter, Finset.mem_sdiff, mem_box]
  omega

theorem box_mono {K K' : ℕ} (h : K ≤ K') : box K ⊆ box K' := by
  intro v hv
  rw [mem_box] at hv ⊢
  omega

theorem card_box (K : ℕ) : (box K).card = (2 * K + 1) ^ 3 := by
  simp only [box, Finset.card_product, Int.card_Icc]
  have : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rw [this]
  ring

theorem card_S1off : S1off.card = 116920 := by
  rw [S1off_eq, Finset.card_sdiff_of_subset (box_mono (by norm_num)), card_box, card_box]
  norm_num

/-- The tracked coordinate of axis `i` (`0 = t`, `1 = x`, `2 = y`). -/
def coord : Fin 3 → V3 → ℤ
  | 0 => fun v => v.1
  | 1 => fun v => v.2.1
  | 2 => fun v => v.2.2

/-- The table index `j = k + 8` of an offset coordinate `|k| ≤ 8`. -/
def jIdx (k : ℤ) : ℕ := (k + 8).toNat

theorem coord_natAbs_le (i : Fin 3) (v : V3) (hv : v ∈ S0) : (coord i v).natAbs ≤ 8 := by
  rw [S0, Finset.mem_filter, mem_box] at hv
  have h := hv.1
  simp only [linf, max_le_iff] at h
  fin_cases i <;> simp only [coord] <;> omega

theorem jIdx_lt (i : Fin 3) (v : V3) (hv : v ∈ S0) : jIdx (coord i v) < 17 := by
  have := coord_natAbs_le i v hv
  unfold jIdx
  omega

/-! ### Step, leaf and link weights -/

/-- Rational fibre sums of the step weights along axis `i`. -/
def stepQ (i : Fin 3) (j : ℕ) : ℚ := epsQ * ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), rQ v

theorem stepQ_le_T : ∀ j < 17, stepQ 0 j ≤ (stT j : ℚ) / Qden := by decide +kernel

theorem stepQ_le_X : ∀ j < 17, stepQ 1 j ≤ (stT j : ℚ) / Qden := by decide +kernel

theorem stepQ_le_Y : ∀ j < 17, stepQ 2 j ≤ (stY j : ℚ) / Qden := by decide +kernel

/-- **Step weights**: the fibre sums of the real step weights are bounded by the table. -/
theorem step_dom (i : Fin 3) (st : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden) (j : ℕ)
    (hj : j < 17) : ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), tw v ≤ (st j : ℝ) / Qden := by
  have h1 : ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), tw v ≤
      ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), ((epsQ * rQ v : ℚ) : ℝ) :=
    Finset.sum_le_sum fun v _ => tw_le v
  have h2 : ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), ((epsQ * rQ v : ℚ) : ℝ) = ((stepQ i j : ℚ) : ℝ) := by
    unfold stepQ
    rw [Finset.mul_sum]
    push_cast
    rfl
  have h3 : ((stepQ i j : ℚ) : ℝ) ≤ (((st j : ℚ) / Qden : ℚ) : ℝ) := by exact_mod_cast hst j hj
  have h4 : (((st j : ℚ) / Qden : ℚ) : ℝ) = (st j : ℝ) / Qden := by push_cast; rfl
  linarith

/-- Rational leaf weights of a fibre. -/
def leafQ (i : Fin 3) (j : ℕ) : ℚ := epsQ * (S0.filter (fun v => jIdx (coord i v) = j)).card

theorem leafQ_le : ∀ i : Fin 3, ∀ j < 17, leafQ i j ≤ (lf j : ℚ) / Qden := by decide +kernel

/-- **Leaf weights**. -/
theorem leaf_dom (i : Fin 3) (j : ℕ) (hj : j < 17) :
    ∑ _v ∈ S0.filter (fun v => jIdx (coord i v) = j), eps ≤ (lf j : ℝ) / Qden := by
  rw [Finset.sum_const, nsmul_eq_mul, eps_eq]
  have h3 : ((leafQ i j : ℚ) : ℝ) ≤ (((lf j : ℚ) / Qden : ℚ) : ℝ) := by exact_mod_cast leafQ_le i j hj
  unfold leafQ at h3
  push_cast at h3
  linarith

/-- 1D sums of the rational link weights. -/
def Pq (K : ℕ) : ℚ := ∑ a ∈ Finset.Icc (-(K : ℤ)) K, muQ ^ a.natAbs
def Tq (K : ℕ) : ℚ := ∑ c ∈ Finset.Icc (-(K : ℤ)) K, muQ ^ c.natAbs * syQ c

theorem sum_box_rQ (K : ℕ) : ∑ v ∈ box K, rQ v = Pq K * (Pq K * Tq K) := by
  set A := Finset.Icc (-(K : ℤ)) K
  have h : ∑ v ∈ box K, rQ v =
      ∑ a ∈ A, ∑ y ∈ A ×ˢ A, muQ ^ a.natAbs * (muQ ^ y.1.natAbs * (muQ ^ y.2.natAbs * syQ y.2)) := by
    unfold box
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [rQ, l1, pow_add]
    ring
  rw [h]
  have h2 : ∀ a ∈ A, ∑ y ∈ A ×ˢ A, muQ ^ a.natAbs * (muQ ^ y.1.natAbs * (muQ ^ y.2.natAbs * syQ y.2)) =
      muQ ^ a.natAbs * (Pq K * Tq K) := by
    intro a _
    rw [← Finset.mul_sum, Finset.sum_product, Pq, Tq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  rfl

theorem linkQ_le : epsQ * (Pq 24 * (Pq 24 * Tq 24) - Pq 4 * (Pq 4 * Tq 4)) ≤ (linkT : ℚ) / Qden := by
  decide +kernel

/-- **Link weights**. -/
theorem link_dom : ∑ v ∈ S1off, tw v ≤ (linkT : ℝ) / Qden := by
  have h1 : ∑ v ∈ S1off, tw v ≤ ∑ v ∈ S1off, ((epsQ * rQ v : ℚ) : ℝ) := Finset.sum_le_sum fun v _ => tw_le v
  have h2 : ∑ v ∈ S1off, ((epsQ * rQ v : ℚ) : ℝ) =
      ((epsQ * (Pq 24 * (Pq 24 * Tq 24) - Pq 4 * (Pq 4 * Tq 4)) : ℚ) : ℝ) := by
    rw [← Rat.cast_sum, ← Finset.mul_sum, S1off_eq, Finset.sum_sdiff_eq_sub (box_mono (by norm_num)),
      sum_box_rQ, sum_box_rQ]
  have h3 := linkQ_le
  have h3' : ((epsQ * (Pq 24 * (Pq 24 * Tq 24) - Pq 4 * (Pq 4 * Tq 4)) : ℚ) : ℝ) ≤
      (((linkT : ℚ) / Qden : ℚ) : ℝ) := by exact_mod_cast h3
  have h4 : (((linkT : ℚ) / Qden : ℚ) : ℝ) = (linkT : ℝ) / Qden := by push_cast; rfl
  linarith

/-! ### Mark weights -/

/-- `y = ε |S0|`: the weight of one untilted witness step. -/
noncomputable def yW : ℝ := eps * 4184
/-- The certified excursion factor. -/
noncomputable def excUp : ℝ := (exB 0 : ℝ) / Qden
/-- The off-route witness: an untilted walk, a link, an excursion. -/
noncomputable def offW : ℝ := eps * 116920 * excUp / (1 - yW)

/-- The displacement of route state `m`: `B` 0, `A(z)` `z = m - 17`, `C(z)` `z = m - 43`. -/
def zOf (m : ℕ) : ℤ := if m = 0 then 0 else if m ≤ 33 then (m : ℤ) - 17 else (m : ℤ) - 43

/-- On-route witness walks from route state `m`; at `Asp` (`m = 34`) ALL walks. -/
noncomputable def onW (m : ℕ) : ℝ :=
  if m = 34 then 1 / (1 - yW) else ∑ c ∈ Finset.range 5, eps ^ c * (Ncnt c (zOf m) : ℝ) + yW ^ 5 / (1 - yW)

/-- The mark weight of route state `m`. -/
noncomputable def markW (m : ℕ) : ℝ := onW m + offW

theorem yW_lt : yW < 1 := by norm_num [yW, eps]

theorem markW_nonneg (m : ℕ) : 0 ≤ markW m := by
  have hy : 0 < 1 - yW := by linarith [yW_lt]
  have hy0 : 0 ≤ yW := by norm_num [yW, eps]
  have hoff : 0 ≤ offW := by
    unfold offW excUp
    have : (0 : ℝ) ≤ eps * 116920 * ((exB 0 : ℝ) / Qden) := by
      have := eps_nonneg
      positivity
    exact div_nonneg this hy.le
  unfold markW onW
  split_ifs
  · have : 0 ≤ 1 / (1 - yW) := by positivity
    linarith
  · have h1 : 0 ≤ ∑ c ∈ Finset.range 5, eps ^ c * (Ncnt c (zOf m) : ℝ) :=
      Finset.sum_nonneg fun c _ => mul_nonneg (pow_nonneg eps_nonneg _) (Nat.cast_nonneg _)
    have h2 : 0 ≤ yW ^ 5 / (1 - yW) := div_nonneg (pow_nonneg hy0 _) hy.le
    linarith

/-- The rational mark weight, with the tabled witness counts. -/
def markQ (m : ℕ) : ℚ :=
  (if m = 34 then 1 / (1 - epsQ * 4184) else
    ∑ c ∈ Finset.range 5, epsQ ^ c * (NcT c (zOf m) : ℚ) + (epsQ * 4184) ^ 5 / (1 - epsQ * 4184)) +
    epsQ * 116920 * ((exB 0 : ℚ) / Qden) / (1 - epsQ * 4184)

theorem markQ_le : ∀ m < 52, markQ m ≤ (mkT m : ℚ) / Qden := by decide +kernel

theorem markW_eq (m : ℕ) : markW m = (markQ m : ℝ) := by
  have hN : ∀ c ∈ Finset.range 5, eps ^ c * (Ncnt c (zOf m) : ℝ) = ((epsQ ^ c * (NcT c (zOf m) : ℚ) : ℚ) : ℝ) := by
    intro c hc
    rw [Ncnt_eq_NcT c (by rw [Finset.mem_range] at hc; omega), eps_eq]
    push_cast
    rfl
  unfold markW onW offW markQ excUp yW
  rw [Finset.sum_congr rfl hN, eps_eq]
  split_ifs <;> push_cast <;> ring

/-- **Mark weights**. -/
theorem mark_dom (m : ℕ) (hm : m < 52) : markW m ≤ (mkT m : ℝ) / Qden := by
  rw [markW_eq]
  have h := markQ_le m hm
  have h' : ((markQ m : ℚ) : ℝ) ≤ (((mkT m : ℚ) / Qden : ℚ) : ℝ) := by exact_mod_cast h
  have h4 : (((mkT m : ℚ) / Qden : ℚ) : ℝ) = (mkT m : ℝ) / Qden := by push_cast; rfl
  linarith

end QECD1
