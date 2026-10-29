import QECD1.Transfer

/-!
# The 3D top part of a tail: route factor and boundary-plane jumps

This is the top-part input (`hT`) of `transfer3`. It ports the 2D `TopOK`, `wTop`, `topB` and `top_sum_le`
(TwoD/T2Sum). A top part entered from an exit cover `c` is `(et, mst, tf)`:

* `tf = true`: a counted top root `et`, reached by a jump with `|et - c|∞ ≥ 17`, followed by a top route word
  `mst` from state `A` (the route grammar without the mark). Its weight is `ε · jw3 c et · wt(mst)`;
* `tf = false`: no counted root. `et` is the vertical projection `(c_t, c_x, Y)` of `c` on the boundary plane
  `y = Y` above it, and `mst = []`. Its weight is `jw3 c et ≤ 1`.

Results:

* `route3_V_le`: route words from `A` weigh at most `RF = 15.7494` (at `λ = 0.014`, `s = 0.007`). The one-move
  bounds come from the certificate tables: `Σ_{S0} tw ≤ 0.094034`, links `≤ 3.699359`, leaves `ε |S0| = 0.077404`;
* `plane_sum_le`: jumps into one plane above `c` weigh at most `P2 = ((1 + q)/(1 - q))²` (about 20,400); the top
  parts use only the vertical projection (`jw3_proj_le`: weight at most 1), so `P2` does not enter `topB3`;
* `top3_sum_le`: every finite set of valid top parts weighs at most `topB3 = Jbar2 · ε* · RF + 1`;
* `transfer3_top`: tails with these top parts weigh at most `10 topB3`.
-/

namespace QECD1

open QECD1.Tab

/-! ### The top-route factor -/

/-- Top-route tokens: state 0 = `B` (at a root), 1 = `A` (after a step), 2 = `C` (after a leaf). -/
def rToks (q : ℕ) : Finset Tok :=
  if q = 0 then S0.image Tok.step ∪ S0.image Tok.leaf
  else if q = 1 then S0.image Tok.step ∪ S1off.image Tok.link
  else S1off.image Tok.link

def rNext (q : ℕ) : Tok → ℕ
  | .step _ => 1
  | .leaf _ => 2
  | .link _ => 0
  | .mark => q

/-- The top-route automaton: T2 weights (`tokW`), end weight 1 in every state. -/
noncomputable def route3 : WA ℕ Tok where
  toks := rToks
  next := rNext
  g _ := tokW 0
  e _ := 1

def RFq : ℚ := 78747 / 5000
def RBq : ℚ := 4483 / 1250
def RCq : ℚ := 35671 / 2500

/-- The Bellman vector of `route3`. -/
noncomputable def rB (q : ℕ) : ℝ := if q = 0 then (RBq : ℝ) else if q = 1 then (RFq : ℝ) else (RCq : ℝ)

theorem stT_sum : ∑ j ∈ Finset.range 17, stT j = 94033541400177 := by decide +kernel

theorem sum_tw_S0 : ∑ v ∈ S0, tw v ≤ (94033541400177 : ℝ) / 10 ^ 15 := by
  have h := marg_le 0 tw (fun _ => 1) (fun _ => zero_le_one) (fun j => (stT j : ℝ) / Qden)
    (fun j hj => step_dom 0 stT stepQ_le_T j hj)
  simp only [mul_one] at h
  refine le_trans h (le_of_eq ?_)
  rw [← Finset.sum_div, Qden_cast]
  congr 1
  exact_mod_cast stT_sum

theorem sum_eps_S0 : ∑ _v ∈ S0, eps = eps * 4184 := by
  rw [Finset.sum_const, card_S0, nsmul_eq_mul]
  push_cast
  ring

theorem link_dom' : ∑ v ∈ S1off, tw v ≤ (3699359368368201 : ℝ) / 10 ^ 15 := by
  have h := link_dom
  rw [Qden_cast] at h
  have e : (linkT : ℝ) = 3699359368368201 := by norm_num [linkT]
  rw [e] at h
  exact h

theorem route3_bellman (q : ℕ) (hq : q ≤ 2) :
    route3.e q + ∑ t ∈ route3.toks q, route3.g q t * rB (route3.next q t) ≤ rB q := by
  show 1 + ∑ t ∈ rToks q, tokW 0 t * rB (rNext q t) ≤ rB q
  have hB0 : (0 : ℝ) ≤ RFq := by norm_num [RFq]
  have hB1 : (0 : ℝ) ≤ RBq := by norm_num [RBq]
  have hB2 : (0 : ℝ) ≤ RCq := by norm_num [RCq]
  have hs := sum_tw_S0
  have hl := link_dom'
  have hstep : ∑ t ∈ S0.image Tok.step, tokW 0 t * rB (rNext q t) = (∑ v ∈ S0, tw v) * RFq := by
    rw [Finset.sum_image step_inj, Finset.sum_mul]
    rfl
  have hlink : ∑ t ∈ S1off.image Tok.link, tokW 0 t * rB (rNext q t) = (∑ v ∈ S1off, tw v) * RBq := by
    rw [Finset.sum_image link_inj, Finset.sum_mul]
    rfl
  have hleaf : ∑ t ∈ S0.image Tok.leaf, tokW 0 t * rB (rNext q t) = (∑ _v ∈ S0, eps) * RCq := by
    rw [Finset.sum_image leaf_inj, Finset.sum_mul]
    rfl
  interval_cases q
  · rw [rToks, if_pos rfl, Finset.sum_union disj_step_leaf, hstep, hleaf, sum_eps_S0]
    have h1 := mul_le_mul_of_nonneg_right hs hB0
    show _ ≤ (RBq : ℝ)
    norm_num [RFq, RBq, RCq, eps] at h1 ⊢
    linarith
  · rw [rToks, if_neg (by norm_num), if_pos rfl, Finset.sum_union disj_step_link, hstep, hlink]
    have h1 := mul_le_mul_of_nonneg_right hs hB0
    have h2 := mul_le_mul_of_nonneg_right hl hB1
    show _ ≤ (RFq : ℝ)
    norm_num [RFq, RBq, RCq] at h1 h2 ⊢
    linarith
  · rw [rToks, if_neg (by norm_num), if_neg (by norm_num), hlink]
    have h2 := mul_le_mul_of_nonneg_right hl hB1
    show _ ≤ (RCq : ℝ)
    norm_num [RFq, RBq, RCq] at h2 ⊢
    linarith

/-- **The top-route factor**: route words from `A` weigh at most `RF = 15.7494`. -/
theorem route3_V_le (N : ℕ) : route3.V N 1 ≤ (RFq : ℝ) := by
  have h := route3.V_le (fun _ t => tokW_nonneg 0 t) (fun q => q ≤ 2)
    (fun q _ t _ => by
      show rNext q t ≤ 2
      cases t <;> simp [rNext] <;> omega)
    rB (fun q hq => route3_bellman q hq)
    (fun q _ => by unfold rB; split_ifs <;> norm_num [RFq, RBq, RCq]) N 1 (by norm_num)
  simpa [rB] using h

/-! ### Jumps into the boundary plane -/

theorem jw3_nonneg (c e : V3) : 0 ≤ jw3 c e := (Real.exp_pos _).le

/-- **Boundary-plane jumps**: into any finite set of blocks of one plane `y = Y` above `c`. -/
theorem plane_sum_le (c : V3) (Y : ℤ) (hY : c.2.2 ≤ Y) (E : Finset V3) (hE : ∀ e ∈ E, e.2.2 = Y) :
    ∑ e ∈ E, jw3 c e ≤ ((1 + (qUpT : ℝ)) / (1 - qUpT)) ^ 2 := by
  set q := Real.exp (-lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqU : q ≤ (qUpT : ℝ) := by
    show Real.exp (-lam) ≤ _
    exact exp_neg_lamT_le
  have hq1 : q < 1 := lt_of_le_of_lt hqU (by norm_num [qUpT])
  -- each jump weighs at most q^|Δt| q^|Δx|
  have hpt : ∀ e ∈ E, jw3 c e ≤ q ^ (e - c).1.natAbs * q ^ (e - c).2.1.natAbs := by
    intro e he
    unfold jw3
    rw [exp_tilt_split]
    have hd : 0 ≤ (e - c).2.2 := by
      have := hE e he
      simp only [Prod.snd_sub]
      omega
    rw [if_pos hd]
    have h1 : Real.exp (-(lam - sT)) ^ (e - c).2.2.natAbs ≤ 1 :=
      pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by norm_num [lam, sT]))
    have h0 : 0 ≤ q ^ (e - c).1.natAbs * q ^ (e - c).2.1.natAbs := mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq0 _)
    calc q ^ (e - c).1.natAbs * q ^ (e - c).2.1.natAbs * Real.exp (-(lam - sT)) ^ (e - c).2.2.natAbs
        ≤ q ^ (e - c).1.natAbs * q ^ (e - c).2.1.natAbs * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  refine le_trans (Finset.sum_le_sum hpt) ?_
  -- re-index by the in-plane offset
  set φ : V3 → ℤ × ℤ := fun e => ((e - c).1, (e - c).2.1)
  have hinj : Set.InjOn φ (E : Set V3) := by
    intro e he e' he' h
    simp only [φ, Prod.mk.injEq, Prod.fst_sub, Prod.snd_sub] at h
    have h3 : e.2.2 = e'.2.2 := (hE e he).trans (hE e' he').symm
    exact Prod.ext (by linarith [h.1]) (Prod.ext (by linarith [h.2]) h3)
  have hre : ∑ e ∈ E, q ^ (e - c).1.natAbs * q ^ (e - c).2.1.natAbs =
      ∑ p ∈ E.image φ, q ^ p.1.natAbs * q ^ p.2.natAbs := by
    rw [Finset.sum_image hinj]
  rw [hre]
  set K := (E.image φ).sup fun p => max p.1.natAbs p.2.natAbs
  have hsub : E.image φ ⊆ Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K := by
    intro p hp
    have hK := Finset.le_sup (f := fun p : ℤ × ℤ => max p.1.natAbs p.2.natAbs) hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    simp only [max_le_iff] at hK
    omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℤ × ℤ => q ^ p.1.natAbs * q ^ p.2.natAbs) hsub
    (fun p _ _ => mul_nonneg (pow_nonneg hq0 _) (pow_nonneg hq0 _))
  rw [Finset.sum_product] at h1
  dsimp only at h1
  rw [← Finset.sum_mul_sum] at h1
  have hS1 : ∑ a ∈ Finset.Icc (-(K : ℤ)) K, q ^ a.natAbs = S1 q K := rfl
  rw [hS1] at h1
  have h2 : S1 q K ≤ (1 + (qUpT : ℝ)) / (1 - qUpT) := by
    refine le_trans (S1_le q hq0 hq1 K) ?_
    have hpos : 0 < 1 - q := by linarith
    have hposU : (0 : ℝ) < 1 - qUpT := by linarith [show (qUpT : ℝ) < 1 by norm_num [qUpT]]
    rw [div_le_div_iff₀ hpos hposU]
    nlinarith
  have h0 := S1_nonneg q hq0 K
  have h3 : S1 q K * S1 q K ≤ ((1 + (qUpT : ℝ)) / (1 - qUpT)) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul h2 h2 h0 (le_trans h0 h2)
  linarith


/-- **The vertical projection**: the jump from `c` to the block `(c_t, c_x, Y)` of the boundary plane
above it weighs at most 1, since `λ ≥ s`. -/
theorem jw3_proj_le (c : V3) (Y : ℤ) (hY : c.2.2 ≤ Y) : jw3 c ((c.1, c.2.1, Y) : V3) ≤ 1 := by
  unfold jw3
  have hd : (((c.1, c.2.1, Y) : V3) - c) = ((0 : ℤ), (0 : ℤ), Y - c.2.2) := by
    ext <;> simp
  rw [hd]
  have hnn : 0 ≤ Y - c.2.2 := sub_nonneg.2 hY
  have hl : ((l1 ((0 : ℤ), (0 : ℤ), Y - c.2.2) : ℕ) : ℝ) = ((Y - c.2.2 : ℤ) : ℝ) := by
    simp only [l1, Int.natAbs_zero, zero_add]
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact abs_of_nonneg (by exact_mod_cast hnn)
  rw [hl, Real.exp_le_one_iff]
  have h1 : (0 : ℝ) ≤ ((Y - c.2.2 : ℤ) : ℝ) := by exact_mod_cast hnn
  have h2 : sT ≤ lam := by norm_num [sT, lam]
  show -lam * ((Y - c.2.2 : ℤ) : ℝ) + sT * ((Y - c.2.2 : ℤ) : ℝ) ≤ 0
  nlinarith

/-! ### Top parts -/

/-- Top parts: `(et, mst, tf)`. -/
abbrev Top3 := V3 × List Tok × Bool

/-- Valid top parts entered from `c`, with the boundary plane `y = Y` (the uncounted part is the vertical projection
of `c`). -/
def tok3 (Y : ℤ) (c : V3) (t : Top3) : Prop :=
  if t.2.2 then jok3 c t.1 ∧ route3.Gram 1 t.2.1 else t.2.1 = [] ∧ t.1 = ((c.1, c.2.1, Y) : V3) ∧ c.2.2 ≤ Y

/-- The weight of a top part. -/
noncomputable def tw3 (c : V3) (t : Top3) : ℝ :=
  if t.2.2 then eps * jw3 c t.1 * route3.wt 1 t.2.1 else jw3 c t.1

/-- The top factor `Jbar2 ε* RF + 1`. -/
noncomputable def topB3 : ℝ := Jbar2 * eps * (RFq : ℝ) + 1

theorem tw3_nonneg (c : V3) (t : Top3) : 0 ≤ tw3 c t := by
  unfold tw3
  split_ifs
  · exact mul_nonneg (mul_nonneg eps_nonneg (Real.exp_pos _).le)
      (route3.wt_nonneg (fun _ t => tokW_nonneg 0 t) (fun _ => zero_le_one) 1 _)
  · exact (Real.exp_pos _).le

theorem topB3_nonneg : 0 ≤ topB3 := by
  unfold topB3
  have := Jbar2_nonneg
  have := eps_nonneg
  have : (0 : ℝ) ≤ RFq := by norm_num [RFq]
  positivity

/-- **The top-part sum.** -/
theorem top3_sum_le (Y : ℤ) (c : V3) (T : Finset Top3) (hT : ∀ t ∈ T, tok3 Y c t) :
    ∑ t ∈ T, tw3 c t ≤ topB3 := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.2.2 = true)]
  unfold topB3
  refine add_le_add ?_ ?_
  · -- counted top roots
    set T1 := T.filter fun t => t.2.2 = true
    have hT1 : ∀ t ∈ T1, jok3 c t.1 ∧ route3.Gram 1 t.2.1 ∧ t.2.2 = true := by
      intro t ht
      obtain ⟨htT, htf⟩ := Finset.mem_filter.1 ht
      have h := hT t htT
      unfold tok3 at h
      rw [if_pos htf] at h
      exact ⟨h.1, h.2, htf⟩
    have hw : ∀ t ∈ T1, tw3 c t = eps * jw3 c t.1 * route3.wt 1 t.2.1 := by
      intro t ht
      unfold tw3
      rw [if_pos (hT1 t ht).2.2]
    rw [Finset.sum_congr rfl hw, ← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := T1.image Prod.fst)
      (fun t ht => Finset.mem_image_of_mem _ ht)]
    have hfib : ∀ et ∈ T1.image Prod.fst, ∑ t ∈ T1 with t.1 = et, eps * jw3 c t.1 * route3.wt 1 t.2.1 ≤
        jw3 c et * (eps * (RFq : ℝ)) := by
      intro et _
      have hinj : Set.InjOn (fun t : Top3 => t.2.1) ((T1.filter (fun t => t.1 = et) : Finset Top3) : Set Top3) := by
        intro t ht t' ht' h
        have h1 := (Finset.mem_filter.1 ht).2
        have h2 := (Finset.mem_filter.1 ht').2
        have h3 := (hT1 t (Finset.mem_filter.1 ht).1).2.2
        have h4 := (hT1 t' (Finset.mem_filter.1 ht').1).2.2
        exact Prod.ext (h1.trans h2.symm) (Prod.ext h (h3.trans h4.symm))
      have heq : ∑ t ∈ T1 with t.1 = et, eps * jw3 c t.1 * route3.wt 1 t.2.1 =
          eps * jw3 c et * ∑ r ∈ (T1.filter (fun t => t.1 = et)).image (fun t : Top3 => t.2.1), route3.wt 1 r := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
      rw [heq]
      set R := (T1.filter (fun t => t.1 = et)).image (fun t : Top3 => t.2.1)
      have hR : ∑ r ∈ R, route3.wt 1 r ≤ (RFq : ℝ) := by
        refine le_trans (route3.sum_wt_le (fun _ t => tokW_nonneg 0 t) (fun _ => zero_le_one) (R.sup List.length) 1 R
          fun r hr => ⟨?_, Finset.le_sup hr⟩) (route3_V_le _)
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hr
        exact (hT1 t (Finset.mem_filter.1 ht).1).2.1
      have := mul_le_mul_of_nonneg_left hR (mul_nonneg eps_nonneg (jw3_nonneg c et))
      linarith
    refine le_trans (Finset.sum_le_sum hfib) ?_
    rw [← Finset.sum_mul]
    have hJ : ∑ et ∈ T1.image Prod.fst, jw3 c et ≤ Jbar2 := by
      refine landing3 c _ fun et het => ?_
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 het
      exact (hT1 t ht).1
    have h0 : (0 : ℝ) ≤ eps * RFq := mul_nonneg eps_nonneg (by norm_num [RFq])
    have := mul_le_mul_of_nonneg_right hJ h0
    linarith
  · -- the boundary plane: the vertical projection of `c`
    set T0 := T.filter fun t => ¬ t.2.2 = true
    set p : Top3 := (((c.1, c.2.1, Y) : V3), ([] : List Tok), false)
    have hT0 : ∀ t ∈ T0, t = p ∧ c.2.2 ≤ Y := by
      intro t ht
      obtain ⟨htT, htf⟩ := Finset.mem_filter.1 ht
      have h := hT t htT
      unfold tok3 at h
      rw [if_neg htf] at h
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨Prod.ext h2 (Prod.ext h1 (by simpa using htf)), h3⟩
    have hsub : T0 ⊆ {p} := fun t ht => Finset.mem_singleton.2 (hT0 t ht).1
    by_cases hne : T0 = ∅
    · rw [hne, Finset.sum_empty]
      norm_num
    · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hcY := (hT0 t0 ht0).2
      calc ∑ t ∈ T0, tw3 c t ≤ ∑ t ∈ ({p} : Finset Top3), tw3 c t :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => tw3_nonneg c t
        _ = jw3 c ((c.1, c.2.1, Y) : V3) := by
            rw [Finset.sum_singleton]
            simp [p, tw3]
        _ ≤ 1 := jw3_proj_le c Y hcY

/-- **Tails with 3D top parts** weigh at most `10 topB3`. -/
theorem transfer3_top {FK : Type} [DecidableEq FK] (E : Encoding3DRooted FK) (exitF : FK → V3) (Y : ℤ)
    (hw : ∀ k, 0 ≤ E.w k) (c : V3) (S : Finset (List (V3 × FK) × Top3))
    (hS : ∀ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw3 (tok3 Y)).TailOK c x.1 x.2) :
    ∑ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw3 (tok3 Y)).tailW C3 c x.1 x.2 ≤ 10 * topB3 :=
  transfer3 E exitF tw3 (tok3 Y) topB3 topB3_nonneg hw tw3_nonneg (fun c T hT => top3_sum_le Y c T hT) c S hS

end QECD1
