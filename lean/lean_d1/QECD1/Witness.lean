import QECD1.Family3

/-!
# The witness words behind the mark weight

The mark of a family word in route state `m` stands for the witness branch. This
module proves that `markW m` bounds every finite set of witness words of axis `i`:

* **on-route** (`onroute_le`): walks `w` of `c` steps in `S0`, untilted weight `ε^c`, with the witness condition
  `|z + Σ w_i| ≥ Sw = 17` at the end, `z` the displacement of the state; the bound is
  `Σ_{c ≤ 4} ε^c N_c(z) + y^5/(1 - y)`, through the walk automaton `witOn` and the Bellman function `onB`
  (exact counts `N_c` for `c ≤ 4`, all walks beyond);
* **at `Asp`** (`onroute_asp_le`): the state no longer knows `z`, so ALL walks are counted: `Σ ε^c ≤ 1/(1 - y)`;
* **off-route** (`offroute_le`): a walk, a link `v ∈ S1` (weight `ε`) and an excursion word of `exc3` (untilted,
  ending only in `Asp`); the bound is `ε |S1| exc/(1 - y) = offW`, with the excursion factor certified
  (`exc3_V_le`: `exc ≤ exB 0 / Qden`, from the excursion certificate `ex_ok`);
* `witness_le`: the on-route and off-route parts together are at most `markW m`.
-/

namespace QECD1

open QECD1.Tab QECD1.Bld

/-! ### Fibre sizes along every axis -/

theorem fiber_card_i : ∀ i : Fin 3, ∀ k ∈ Finset.Icc (-8 : ℤ) 8,
    (S0.filter fun v => coord i v = k).card = stepCount k := by decide +kernel

theorem coord_mem (i : Fin 3) (v : V3) (hv : v ∈ S0) : coord i v ∈ Finset.Icc (-8 : ℤ) 8 := by
  have := coord_natAbs_le i v hv
  rw [Finset.mem_Icc]
  omega

/-- Marginalization of a function of one coordinate along axis `i`. -/
theorem marg_count (i : Fin 3) (F : ℤ → ℝ) :
    ∑ w ∈ S0, F (coord i w) = ∑ k ∈ Finset.Icc (-8 : ℤ) 8, (stepCount k : ℝ) * F k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v : V3 => coord i v) (t := Finset.Icc (-8 : ℤ) 8)
    (fun v hv => coord_mem i v hv)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.1 hv).2]), Finset.sum_const, nsmul_eq_mul,
    fiber_card_i i k hk]

theorem Ncnt_marg (i : Fin 3) (d : ℕ) (z : ℤ) :
    ∑ w ∈ S0, (Ncnt d (z + coord i w) : ℝ) = Ncnt (d + 1) z := by
  rw [marg_count i (fun k => (Ncnt d (z + k) : ℝ))]
  simp only [Ncnt]
  push_cast
  rfl

theorem card_S0_real : ((S0.card : ℕ) : ℝ) = 4184 := by
  rw [card_S0]
  norm_num

theorem yW_eq : eps * 4184 = yW := rfl

theorem one_sub_yW_pos : 0 < 1 - yW := by linarith [yW_lt]

/-! ### On-route witness walks -/

/-- On-route witness walks of axis `i`: steps `w ∈ S0` of weight `ε`; the state is (displacement, steps so far); a
walk of at most 4 steps ends with weight `[|z| ≥ Sw]` (`Const.Sw = 17`), a longer one with weight 1 (all walks). -/
noncomputable def witOn (i : Fin 3) : WA (ℤ × ℕ) V3 where
  toks _ := S0
  next q w := (q.1 + coord i w, q.2 + 1)
  g _ _ := eps
  e q := if q.2 ≤ 4 then (if Const.Sw ≤ q.1.natAbs then 1 else 0) else 1

/-- The Bellman function of `witOn`. -/
noncomputable def onB (q : ℤ × ℕ) : ℝ :=
  if q.2 ≤ 4 then ∑ d ∈ Finset.range (5 - q.2), eps ^ d * (Ncnt d q.1 : ℝ) + yW ^ (5 - q.2) / (1 - yW)
  else 1 / (1 - yW)

theorem onB_nonneg (q : ℤ × ℕ) : 0 ≤ onB q := by
  have hy := one_sub_yW_pos
  have hy0 : 0 ≤ yW := by norm_num [yW, eps]
  unfold onB
  split_ifs
  · have h1 : 0 ≤ ∑ d ∈ Finset.range (5 - q.2), eps ^ d * (Ncnt d q.1 : ℝ) :=
      Finset.sum_nonneg fun d _ => mul_nonneg (pow_nonneg eps_nonneg _) (Nat.cast_nonneg _)
    have h2 : 0 ≤ yW ^ (5 - q.2) / (1 - yW) := div_nonneg (pow_nonneg hy0 _) hy.le
    linarith
  · exact div_nonneg zero_le_one hy.le

theorem onB_bellman (i : Fin 3) (q : ℤ × ℕ) :
    (witOn i).e q + ∑ w ∈ (witOn i).toks q, (witOn i).g q w * onB ((witOn i).next q w) ≤ onB q := by
  obtain ⟨z, c⟩ := q
  have hy := one_sub_yW_pos
  show (if c ≤ 4 then (if Const.Sw ≤ z.natAbs then (1 : ℝ) else 0) else 1) +
      ∑ w ∈ S0, eps * onB (z + coord i w, c + 1) ≤ onB (z, c)
  have hN0 : (if Const.Sw ≤ z.natAbs then (1 : ℝ) else 0) = (Ncnt 0 z : ℝ) := by
    rw [Const.Sw_val]
    simp only [Ncnt]
    split_ifs <;> simp
  rcases Nat.lt_or_ge c 4 with hc | hc
  · -- c ≤ 3: both states count exactly
    have hB : ∀ w, onB (z + coord i w, c + 1) =
        ∑ d ∈ Finset.range (4 - c), eps ^ d * (Ncnt d (z + coord i w) : ℝ) + yW ^ (4 - c) / (1 - yW) := by
      intro w
      unfold onB
      rw [if_pos (by omega)]
      have e1 : 5 - (c + 1) = 4 - c := by omega
      rw [e1]
    rw [Finset.sum_congr rfl fun w _ => by rw [hB w]]
    have hsplit : ∑ w ∈ S0, eps * (∑ d ∈ Finset.range (4 - c), eps ^ d * (Ncnt d (z + coord i w) : ℝ) +
        yW ^ (4 - c) / (1 - yW)) =
        ∑ d ∈ Finset.range (4 - c), eps ^ (d + 1) * (Ncnt (d + 1) z : ℝ) + yW ^ (5 - c) / (1 - yW) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ d ∈ Finset.range (4 - c), ∑ w ∈ S0, eps * (eps ^ d * (Ncnt d (z + coord i w) : ℝ)) =
          eps ^ (d + 1) * (Ncnt (d + 1) z : ℝ) := by
        intro d _
        rw [← Ncnt_marg i d z, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, card_S0_real]
      have e2 : 5 - c = (4 - c) + 1 := by omega
      rw [e2, pow_succ]
      unfold yW
      ring
    rw [hsplit, if_pos (by omega), hN0]
    unfold onB
    rw [if_pos (by omega)]
    have e3 : 5 - c = (4 - c) + 1 := by omega
    rw [e3, Finset.sum_range_succ' (fun d => eps ^ d * (Ncnt d z : ℝ))]
    simp only [pow_zero, one_mul]
    linarith
  · rcases Nat.eq_or_lt_of_le hc with hc4 | hc5
    · -- c = 4: the next state counts all walks
      subst hc4
      have hB : ∀ w, onB (z + coord i w, 4 + 1) = 1 / (1 - yW) := by
        intro w
        unfold onB
        rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl fun w _ => by rw [hB w], Finset.sum_const, nsmul_eq_mul, card_S0_real,
        if_pos (le_refl 4), hN0]
      unfold onB
      rw [if_pos (le_refl 4)]
      simp only [Nat.reduceSub, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one]
      have : (4184 : ℝ) * (eps * (1 / (1 - yW))) = yW / (1 - yW) := by
        unfold yW
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      linarith
    · -- c ≥ 5: all walks
      have hB : ∀ w, onB (z + coord i w, c + 1) = 1 / (1 - yW) := by
        intro w
        unfold onB
        rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl fun w _ => by rw [hB w], Finset.sum_const, nsmul_eq_mul, card_S0_real,
        if_neg (by omega)]
      unfold onB
      rw [if_neg (by omega)]
      have : (1 : ℝ) + 4184 * (eps * (1 / (1 - yW))) = 1 / (1 - yW) := by
        unfold yW
        have hne : (1 : ℝ) - eps * 4184 ≠ 0 := by norm_num [eps]
        have h := mul_inv_cancel₀ hne
        simp only [div_eq_mul_inv]
        linear_combination (-1 : ℝ) * h
      linarith

theorem witOn_V_le (i : Fin 3) (N : ℕ) (q : ℤ × ℕ) : (witOn i).V N q ≤ onB q :=
  (witOn i).V_le (fun _ _ => eps_nonneg) (fun _ => True) (fun _ _ _ _ => trivial) onB
    (fun q _ => onB_bellman i q) (fun q _ => onB_nonneg q) N q trivial

theorem witOn_e_nonneg (i : Fin 3) (q : ℤ × ℕ) : 0 ≤ (witOn i).e q := by
  show 0 ≤ (if q.2 ≤ 4 then (if Const.Sw ≤ q.1.natAbs then (1 : ℝ) else 0) else 1)
  split_ifs <;> norm_num

theorem witOn_gram (i : Fin 3) : ∀ (q : ℤ × ℕ) (w : List V3), (∀ v ∈ w, v ∈ S0) → (witOn i).Gram q w
  | _, [], _ => trivial
  | q, v :: w, h => ⟨h v (List.mem_cons_self ..), witOn_gram i _ w fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem witOn_wt (i : Fin 3) : ∀ (q : ℤ × ℕ) (w : List V3),
    (witOn i).wt q w = eps ^ w.length * (witOn i).e (q.1 + (w.map (coord i)).sum, q.2 + w.length)
  | q, [] => by simp [WA.wt]
  | q, v :: w => by
    rw [WA.wt, witOn_wt i _ w]
    show eps * (eps ^ w.length * (witOn i).e (q.1 + coord i v + (w.map (coord i)).sum, q.2 + 1 + w.length)) =
      eps ^ (w.length + 1) * (witOn i).e (q.1 + (coord i v + (w.map (coord i)).sum), q.2 + (w.length + 1))
    rw [add_assoc q.1, show q.2 + 1 + w.length = q.2 + (w.length + 1) by omega, pow_succ]
    ring

/-- The weight of an on-route witness walk with the witness condition at its end. -/
noncomputable def witWt (i : Fin 3) (z : ℤ) (w : List V3) : ℝ :=
  eps ^ w.length * (if Const.Sw ≤ (z + (w.map (coord i)).sum).natAbs then 1 else 0)

theorem witWt_le (i : Fin 3) (z : ℤ) (w : List V3) : witWt i z w ≤ (witOn i).wt (z, 0) w := by
  rw [witOn_wt]
  unfold witWt
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg eps_nonneg _)
  show (if Const.Sw ≤ (z + (w.map (coord i)).sum).natAbs then (1 : ℝ) else 0) ≤
    (if 0 + w.length ≤ 4 then (if Const.Sw ≤ (z + (w.map (coord i)).sum).natAbs then 1 else 0) else 1)
  split_ifs <;> norm_num

/-- **On-route witnesses**: every finite set of witness walks from displacement `z`. -/
theorem onroute_le (i : Fin 3) (z : ℤ) (W : Finset (List V3)) (hW : ∀ w ∈ W, ∀ v ∈ w, v ∈ S0) :
    ∑ w ∈ W, witWt i z w ≤ onB (z, 0) := by
  have h1 : ∑ w ∈ W, witWt i z w ≤ ∑ w ∈ W, (witOn i).wt (z, 0) w := Finset.sum_le_sum fun w _ => witWt_le i z w
  have h2 := (witOn i).sum_wt_le (fun _ _ => eps_nonneg) (witOn_e_nonneg i) (W.sup List.length) (z, 0) W
    fun w hw => ⟨witOn_gram i _ w (hW w hw), Finset.le_sup hw⟩
  exact le_trans h1 (le_trans h2 (witOn_V_le i _ _))

/-- **At `Asp` all walks are counted**: every finite set of walks, without any condition. -/
theorem onroute_asp_le (i : Fin 3) (W : Finset (List V3)) (hW : ∀ w ∈ W, ∀ v ∈ w, v ∈ S0) :
    ∑ w ∈ W, eps ^ w.length ≤ 1 / (1 - yW) := by
  have h1 : ∀ w ∈ W, eps ^ w.length = (witOn i).wt (0, 5) w := by
    intro w _
    rw [witOn_wt]
    show eps ^ w.length = eps ^ w.length *
      (if 5 + w.length ≤ 4 then (if Const.Sw ≤ (0 + (w.map (coord i)).sum).natAbs then (1 : ℝ) else 0) else 1)
    rw [if_neg (by omega), mul_one]
  rw [Finset.sum_congr rfl h1]
  have h2 := (witOn i).sum_wt_le (fun _ _ => eps_nonneg) (witOn_e_nonneg i) (W.sup List.length) (0, 5) W
    fun w hw => ⟨witOn_gram i _ w (hW w hw), Finset.le_sup hw⟩
  have h3 := witOn_V_le i (W.sup List.length) (0, 5)
  have h4 : onB (0, 5) = 1 / (1 - yW) := by
    unfold onB
    rw [if_neg (by norm_num)]
  linarith

theorem onB_eq_onW (m : ℕ) (hm : m ≠ 34) : onB (zOf m, 0) = onW m := by
  unfold onB onW
  rw [if_neg hm]
  dsimp only
  rw [if_pos (by norm_num)]

/-! ### The excursion automaton and off-route witnesses -/

/-- The excursion automaton of axis `i`: the route grammar, every token untilted with weight `ε`, ending only in
`Asp` (the excursion's last part spans at least `Sw` along axis `i`). -/
noncomputable def exc3 (i : Fin 3) : WA ℕ Tok where
  toks := routeToks
  next := routeNext i
  g _ _ := eps
  e n := if n = 34 then 1 else 0

theorem exlink_dom : ∑ _v ∈ S1off, eps ≤ (exLinkT : ℝ) / Qden := by
  rw [Finset.sum_const, card_S1off, nsmul_eq_mul]
  norm_num [eps, exLinkT, Qden]

theorem route_dom_ex (i : Fin 3) (m : ℕ) (hm : m < 52) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ t ∈ routeToks m, eps * F (routeNext i m t) ≤
      ((routeMoves lf lf exLinkT m).map fun mv => (mv.1 : ℝ) / Qden * F mv.2).sum := by
  have hleaf := leaf_dom i
  have hlink : ∑ t ∈ S1off.image Tok.link, eps * F (routeNext i m t) ≤ (exLinkT : ℝ) / Qden * F 0 := by
    rw [Finset.sum_image link_inj]
    simp only [routeNext]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right exlink_dom (hF 0)
  by_cases h0 : m = 0
  · subst h0
    rw [routeToks, if_pos rfl, routeMoves, if_pos rfl, Finset.sum_union disj_step_leaf,
      Finset.sum_image step_inj, Finset.sum_image leaf_inj, List.map_append, List.sum_append,
      sum_map_range17, sum_map_range17]
    simp only [routeNext, if_pos]
    refine add_le_add ?_ ?_
    · exact marg_le i (fun _ => eps) (fun j => F (j + 9)) (fun j => hF _) (fun j => (lf j : ℝ) / Qden) hleaf
    · exact marg_le i (fun _ => eps) (fun j => F (j + 35)) (fun j => hF _) (fun j => (lf j : ℝ) / Qden) hleaf
  by_cases hA : m ≤ 33
  · rw [routeToks, if_neg h0, if_pos (by omega), routeMoves, if_neg h0, if_pos hA,
      Finset.sum_union disj_step_link, Finset.sum_image step_inj, List.map_append, List.sum_append,
      sum_map_range17]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine add_le_add ?_ hlink
    simp only [routeNext, if_neg h0, if_pos hA]
    exact marg_le i (fun _ => eps) (fun j => F (aNext m j)) (fun j => hF _) (fun j => (lf j : ℝ) / Qden) hleaf
  by_cases h34 : m = 34
  · subst h34
    rw [routeToks, if_neg (by norm_num), if_pos (by norm_num), routeMoves, if_neg (by norm_num),
      if_neg (by norm_num), if_pos rfl, Finset.sum_union disj_step_link, Finset.sum_image step_inj]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine add_le_add ?_ hlink
    have hr : ∀ v, routeNext i 34 (Tok.step v) = 34 := fun v => by simp [routeNext]
    simp only [hr]
    have hc : ((((List.range 17).map lf).sum : ℕ) : ℝ) = ∑ j ∈ Finset.range 17, (lf j : ℝ) := by
      rw [Nat.cast_list_sum, List.map_map, list_sum_map_range]
      rfl
    rw [hc, Finset.sum_div, Finset.sum_mul]
    exact marg_le i (fun _ => eps) (fun _ => F 34) (fun j => hF _) (fun j => (lf j : ℝ) / Qden) hleaf
  · rw [routeToks, if_neg h0, if_neg (by omega), routeMoves, if_neg h0, if_neg hA, if_neg h34]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hlink

theorem exc3_bellman (i : Fin 3) (n : ℕ) (hn : n < 52) :
    (exc3 i).e n + ∑ t ∈ (exc3 i).toks n, (exc3 i).g n t * ((exB ((exc3 i).next n t) : ℝ) / Qden) ≤
      (exB n : ℝ) / Qden := by
  have hc := checkN_spec ex_ok n hn
  have hQ : (0 : ℝ) < Qden := by norm_num [Qden]
  have hR := (Nat.cast_le (α := ℝ)).2 hc
  simp only [Nat.cast_add, Nat.cast_mul] at hR
  rw [cast_list_sum_map] at hR
  have hd : (exE Qden n : ℝ) / Qden +
      ((routeMoves lf lf exLinkT n).map fun mv => (mv.1 : ℝ) / Qden * ((exB mv.2 : ℝ) / Qden)).sum ≤
      (exB n : ℝ) / Qden := by
    rw [sum_map_scale]
    set S := ((routeMoves lf lf exLinkT n).map fun mv => (mv.1 : ℝ) * exB mv.2).sum
    have h3 : S ≤ ((exB n : ℝ) - exE Qden n) * Qden := by linarith
    have h4 : S / (Qden : ℝ) ^ 2 ≤ ((exB n : ℝ) - exE Qden n) * Qden / (Qden : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have h5 : ((exB n : ℝ) - exE Qden n) * Qden / (Qden : ℝ) ^ 2 = ((exB n : ℝ) - exE Qden n) / Qden := by
      rw [pow_two, mul_div_mul_right _ _ hQ.ne']
    have h6 : (exE Qden n : ℝ) / Qden + ((exB n : ℝ) - exE Qden n) / Qden = (exB n : ℝ) / Qden := by ring
    linarith
  have hE : (exc3 i).e n = (exE Qden n : ℝ) / Qden := by
    show (if n = 34 then (1 : ℝ) else 0) = _
    unfold exE
    split_ifs
    · exact (div_self hQ.ne').symm
    · simp
  have hr := route_dom_ex i n hn (fun k => (exB k : ℝ) / Qden) (fun k => by positivity)
  show (exc3 i).e n + ∑ t ∈ routeToks n, eps * ((exB (routeNext i n t) : ℝ) / Qden) ≤ _
  rw [hE]
  linarith

/-- **Excursion factor**: `exc ≤ exB 0 / Qden ≈ 5.718e-5` for every word length. -/
theorem exc3_V_le (i : Fin 3) (N : ℕ) : (exc3 i).V N 0 ≤ excUp :=
  (exc3 i).V_le (fun _ _ => eps_nonneg) (fun n => n < 52)
    (fun n _ t ht => routeNext_lt i n t ht) (fun n => (exB n : ℝ) / Qden)
    (fun n hn => exc3_bellman i n hn) (fun n _ => by positivity) N 0 (by norm_num)

theorem exc3_e_nonneg (i : Fin 3) (n : ℕ) : 0 ≤ (exc3 i).e n := by
  show 0 ≤ (if n = 34 then (1 : ℝ) else 0)
  split_ifs <;> norm_num

/-- The weight of an off-route witness: a walk, a link, an excursion word. -/
noncomputable def offWt (i : Fin 3) (x : List V3 × V3 × List Tok) : ℝ :=
  eps ^ x.1.length * (eps * (exc3 i).wt 0 x.2.2)

/-- **Off-route witnesses**. -/
theorem offroute_le (i : Fin 3) (T : Finset (List V3 × V3 × List Tok))
    (hT : ∀ x ∈ T, (∀ v ∈ x.1, v ∈ S0) ∧ x.2.1 ∈ S1off ∧ (exc3 i).Gram 0 x.2.2) :
    ∑ x ∈ T, offWt i x ≤ offW := by
  set T1 := T.image Prod.fst
  set T3 := T.image fun x => x.2.2
  have hsub : T ⊆ T1 ×ˢ (S1off ×ˢ T3) := by
    intro x hx
    simp only [Finset.mem_product, T1, T3, Finset.mem_image]
    exact ⟨⟨x, hx, rfl⟩, (hT x hx).2.1, ⟨x, hx, rfl⟩⟩
  have hwt0 : ∀ r, 0 ≤ (exc3 i).wt 0 r := (exc3 i).wt_nonneg (fun _ _ => eps_nonneg) (exc3_e_nonneg i) 0
  have hnn : ∀ x : List V3 × V3 × List Tok, 0 ≤ offWt i x := fun x =>
    mul_nonneg (pow_nonneg eps_nonneg _) (mul_nonneg eps_nonneg (hwt0 _))
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hnn x)
  have hprod : ∑ x ∈ T1 ×ˢ (S1off ×ˢ T3), offWt i x =
      (∑ w ∈ T1, eps ^ w.length) * ((∑ _v ∈ S1off, eps) * ∑ r ∈ T3, (exc3 i).wt 0 r) := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold offWt
    ring
  have hA : ∑ w ∈ T1, eps ^ w.length ≤ 1 / (1 - yW) := by
    refine onroute_asp_le i T1 fun w hw v hv => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
    exact (hT x hx).1 v hv
  have hB : ∑ _v ∈ S1off, eps ≤ eps * 116920 := by
    rw [Finset.sum_const, card_S1off, nsmul_eq_mul]
    push_cast
    linarith
  have hC : ∑ r ∈ T3, (exc3 i).wt 0 r ≤ excUp := by
    refine le_trans ((exc3 i).sum_wt_le (fun _ _ => eps_nonneg) (exc3_e_nonneg i) (T3.sup List.length) 0 T3
      fun r hr => ⟨?_, Finset.le_sup hr⟩) (exc3_V_le i _)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    exact (hT x hx).2.2
  have hA0 : 0 ≤ ∑ w ∈ T1, eps ^ w.length := Finset.sum_nonneg fun w _ => pow_nonneg eps_nonneg _
  have hB0 : 0 ≤ ∑ _v ∈ S1off, eps := Finset.sum_nonneg fun _ _ => eps_nonneg
  have hC0 : 0 ≤ ∑ r ∈ T3, (exc3 i).wt 0 r := Finset.sum_nonneg fun r _ => hwt0 r
  have hy := one_sub_yW_pos
  have hBC : (∑ _v ∈ S1off, eps) * ∑ r ∈ T3, (exc3 i).wt 0 r ≤ eps * 116920 * excUp :=
    mul_le_mul hB hC hC0 (by have := eps_nonneg; positivity)
  have hABC : (∑ w ∈ T1, eps ^ w.length) * ((∑ _v ∈ S1off, eps) * ∑ r ∈ T3, (exc3 i).wt 0 r) ≤
      1 / (1 - yW) * (eps * 116920 * excUp) :=
    mul_le_mul hA hBC (mul_nonneg hB0 hC0) (div_nonneg zero_le_one hy.le)
  have hoff : 1 / (1 - yW) * (eps * 116920 * excUp) = offW := by
    unfold offW
    field_simp
  rw [hprod] at h1
  linarith

/-- **The mark weight bounds the witness words** of route state `m < 52`: on-route walks (with the witness condition,
or all walks at `Asp`) and off-route walks with an excursion. -/
theorem witness_le (i : Fin 3) (m : ℕ) (W : Finset (List V3)) (hW : ∀ w ∈ W, ∀ v ∈ w, v ∈ S0)
    (T : Finset (List V3 × V3 × List Tok))
    (hT : ∀ x ∈ T, (∀ v ∈ x.1, v ∈ S0) ∧ x.2.1 ∈ S1off ∧ (exc3 i).Gram 0 x.2.2) :
    (if m = 34 then ∑ w ∈ W, eps ^ w.length else ∑ w ∈ W, witWt i (zOf m) w) + ∑ x ∈ T, offWt i x ≤
      markW m := by
  have hoff := offroute_le i T hT
  unfold markW
  split_ifs with h34
  · have h := onroute_asp_le i W hW
    have e : onW m = 1 / (1 - yW) := by unfold onW; rw [if_pos h34]
    linarith
  · have h := onroute_le i (zOf m) W hW
    rw [onB_eq_onW m h34] at h
    linarith

end QECD1
