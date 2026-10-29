import QECD1.Weights
import QECD1.WA

/-!
# The 3D family words of one axis, bounded by the certificate (`λ = 14/1000`, `s = 7/1000`)


Family words are words over the tokens `step v`, `leaf v` (`v ∈ S0`), `link v` (`v ∈ S1`) and `mark`, read from a
landing root. States are numbered as in `QECD1.Bld`:
`0 = B`, `1..33 = A(z)`, `34 = Asp`, `35..51 = C(z)` before the mark, and `+ 52` after it. For axis `i` the state
tracks the `i`-th coordinate `z` of the displacement of the current route part from its root.

* `routeToks`: steps and leaves at `B`; steps and links at `A(z)` and `Asp`; links at `C(z)`. No link leaves `B`,
  so a route part that is only its root is a leaf `C(k)` (the 2D leaf convention).
* `routeNext`: a step from `A(z)` goes to `A(z + k)`, or to `Asp` once `|z + k| ≥ Sw = 17`; `Asp` stays `Asp`.
* `famToks`, `famNext`: the mark is allowed once and moves to the copy after it.
* `tokW`: the real T2 weights `tw v` of steps and links, `ε` of leaves, `markW m` of the mark (all walks at `Asp`).
* `famEnd`: `1` after the mark except at `B`, `0` before it.

Results:

* `marg`: summing a function of the tracked coordinate over `S0` is exact fibrewise (the per-coordinate lumping);
* `route_dom`: the one-token sums of the real automaton are bounded by the certificate's move lists;
* `fam_bellman`: the certificate vector satisfies the Bellman inequality of the real automaton;
* `famT_V_le`, `famX_V_le`, `famY_V_le`: the family factor of each axis is bounded by the certificate:
  `F0t = F0x ≤ 2734104547231 / 10^15`, `F0y ≤ 2741437430948 / 10^15`;
* `famT_words_le`, `famX_words_le`, `famY_words_le`: the same bound for every finite set of allowed family words.
-/

namespace QECD1

open QECD1.Tab QECD1.Bld

/-- Tokens of the 3D family words. -/
inductive Tok where
  | step (v : V3)
  | leaf (v : V3)
  | link (v : V3)
  | mark
  deriving DecidableEq

/-- The allowed route tokens of route state `m < 52`. -/
def routeToks (m : ℕ) : Finset Tok :=
  if m = 0 then S0.image Tok.step ∪ S0.image Tok.leaf
  else if m ≤ 34 then S0.image Tok.step ∪ S1off.image Tok.link
  else S1off.image Tok.link

/-- The allowed family tokens of state `n < 104`: the mark once, before it. -/
def famToks (n : ℕ) : Finset Tok := if n < 52 then insert Tok.mark (routeToks n) else routeToks (n - 52)

/-- The route state after a token, for axis `i`. -/
def routeNext (i : Fin 3) (m : ℕ) : Tok → ℕ
  | .step v => if m = 0 then jIdx (coord i v) + 9 else if m ≤ 33 then aNext m (jIdx (coord i v)) else 34
  | .leaf v => jIdx (coord i v) + 35
  | .link _ => 0
  | .mark => m

/-- The family state after a token, for axis `i`. -/
def famNext (i : Fin 3) (n : ℕ) (t : Tok) : ℕ :=
  if n < 52 then (if t = Tok.mark then n + 52 else routeNext i n t) else routeNext i (n - 52) t + 52

/-- Token weights. -/
noncomputable def tokW (n : ℕ) : Tok → ℝ
  | .step v => tw v
  | .leaf _ => eps
  | .link v => tw v
  | .mark => markW n

/-- End weights. -/
noncomputable def famEnd (n : ℕ) : ℝ := if n ≤ 52 then 0 else 1

/-- The family automaton of axis `i`. -/
noncomputable def fam3 (i : Fin 3) : WA ℕ Tok where
  toks := famToks
  next := famNext i
  g := tokW
  e := famEnd

theorem tokW_nonneg (n : ℕ) (t : Tok) : 0 ≤ tokW n t := by
  cases t with
  | step v => exact tw_nonneg v
  | leaf v => exact eps_nonneg
  | link v => exact tw_nonneg v
  | mark => exact markW_nonneg n

theorem famEnd_nonneg (n : ℕ) : 0 ≤ famEnd n := by
  unfold famEnd
  split_ifs <;> norm_num

/-! ### Lists and sums -/

theorem list_sum_map_range (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_map_range17 (f : ℕ → ℕ × ℕ) (F : ℕ → ℝ) :
    (((List.range 17).map f).map fun mv => (mv.1 : ℝ) / Qden * F mv.2).sum =
      ∑ j ∈ Finset.range 17, ((f j).1 : ℝ) / Qden * F (f j).2 := by
  rw [List.map_map, list_sum_map_range]
  rfl

theorem sum_map_scale (L : List (ℕ × ℕ)) (B : ℕ → ℕ) :
    (L.map fun mv => (mv.1 : ℝ) / Qden * ((B mv.2 : ℝ) / Qden)).sum =
      (L.map fun mv => (mv.1 : ℝ) * B mv.2).sum / (Qden : ℝ) ^ 2 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem cast_list_sum_map (L : List (ℕ × ℕ)) (B : ℕ → ℕ) :
    (((L.map fun mv => mv.1 * B mv.2).sum : ℕ) : ℝ) = (L.map fun mv => (mv.1 : ℝ) * B mv.2).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih]

theorem sum_map_shift (L : List (ℕ × ℕ)) (B : ℕ → ℕ) :
    ((L.map fun m => (m.1, m.2 + 52)).map fun mv => (mv.1 : ℝ) / Qden * ((B mv.2 : ℝ) / Qden)).sum =
      (L.map fun mv => (mv.1 : ℝ) / Qden * ((B (mv.2 + 52) : ℝ) / Qden)).sum := by
  rw [List.map_map]
  rfl

/-! ### Lumping and the one-token sums -/

/-- **Marginalization** along axis `i`: exact, fibre by fibre. -/
theorem marg (i : Fin 3) (w : V3 → ℝ) (G : ℕ → ℝ) :
    ∑ v ∈ S0, w v * G (jIdx (coord i v)) =
      ∑ j ∈ Finset.range 17, (∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), w v) * G j := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v => jIdx (coord i v)) (t := Finset.range 17)
    (fun v hv => Finset.mem_range.2 (jIdx_lt i v hv))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.1 hv).2]

theorem marg_le (i : Fin 3) (w : V3 → ℝ) (G : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) (b : ℕ → ℝ)
    (hb : ∀ j < 17, ∑ v ∈ S0.filter (fun v => jIdx (coord i v) = j), w v ≤ b j) :
    ∑ v ∈ S0, w v * G (jIdx (coord i v)) ≤ ∑ j ∈ Finset.range 17, b j * G j := by
  rw [marg]
  exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hb j (Finset.mem_range.1 hj)) (hG j)

theorem step_inj : Set.InjOn Tok.step (S0 : Set V3) := fun _ _ _ _ h => Tok.step.inj h
theorem leaf_inj : Set.InjOn Tok.leaf (S0 : Set V3) := fun _ _ _ _ h => Tok.leaf.inj h
theorem link_inj : Set.InjOn Tok.link (S1off : Set V3) := fun _ _ _ _ h => Tok.link.inj h

theorem disj_step_leaf : Disjoint (S0.image Tok.step) (S0.image Tok.leaf) := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨w, _, h⟩ := Finset.mem_image.1 h2
  cases h

theorem disj_step_link : Disjoint (S0.image Tok.step) (S1off.image Tok.link) := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h1
  obtain ⟨w, _, h⟩ := Finset.mem_image.1 h2
  cases h

theorem link_part (i : Fin 3) (m n : ℕ) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ t ∈ S1off.image Tok.link, tokW n t * F (routeNext i m t) ≤ (linkT : ℝ) / Qden * F 0 := by
  rw [Finset.sum_image link_inj]
  simp only [tokW, routeNext]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right link_dom (hF 0)

/-- **One-token sums**: the real route automaton is dominated by the certificate's route moves. -/
theorem route_dom (i : Fin 3) (st : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden)
    (m : ℕ) (hm : m < 52) (n : ℕ) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ t ∈ routeToks m, tokW n t * F (routeNext i m t) ≤
      ((routeMoves st lf linkT m).map fun mv => (mv.1 : ℝ) / Qden * F mv.2).sum := by
  have hstep := step_dom i st hst
  have hleaf := leaf_dom i
  by_cases h0 : m = 0
  · subst h0
    rw [routeToks, if_pos rfl, routeMoves, if_pos rfl, Finset.sum_union disj_step_leaf,
      Finset.sum_image step_inj, Finset.sum_image leaf_inj, List.map_append, List.sum_append,
      sum_map_range17, sum_map_range17]
    simp only [tokW, routeNext, if_pos]
    refine add_le_add ?_ ?_
    · exact marg_le i tw (fun j => F (j + 9)) (fun j => hF _) (fun j => (st j : ℝ) / Qden) hstep
    · exact marg_le i (fun _ => eps) (fun j => F (j + 35)) (fun j => hF _) (fun j => (lf j : ℝ) / Qden) hleaf
  by_cases hA : m ≤ 33
  · rw [routeToks, if_neg h0, if_pos (by omega), routeMoves, if_neg h0, if_pos hA,
      Finset.sum_union disj_step_link, Finset.sum_image step_inj, List.map_append, List.sum_append,
      sum_map_range17]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine add_le_add ?_ (link_part i m n F hF)
    simp only [tokW, routeNext, if_neg h0, if_pos hA]
    exact marg_le i tw (fun j => F (aNext m j)) (fun j => hF _) (fun j => (st j : ℝ) / Qden) hstep
  by_cases h34 : m = 34
  · subst h34
    rw [routeToks, if_neg (by norm_num), if_pos (by norm_num), routeMoves, if_neg (by norm_num),
      if_neg (by norm_num), if_pos rfl, Finset.sum_union disj_step_link, Finset.sum_image step_inj]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine add_le_add ?_ (link_part i 34 n F hF)
    have hr : ∀ v, routeNext i 34 (Tok.step v) = 34 := fun v => by simp [routeNext]
    simp only [tokW, hr]
    have hc : ((((List.range 17).map st).sum : ℕ) : ℝ) = ∑ j ∈ Finset.range 17, (st j : ℝ) := by
      rw [Nat.cast_list_sum, List.map_map, list_sum_map_range]
      rfl
    rw [hc, Finset.sum_div, Finset.sum_mul]
    exact marg_le i tw (fun _ => F 34) (fun j => hF _) (fun j => (st j : ℝ) / Qden) hstep
  · rw [routeToks, if_neg h0, if_neg (by omega), routeMoves, if_neg h0, if_neg hA, if_neg h34]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact link_part i m n F hF

theorem mark_notMem (m : ℕ) : Tok.mark ∉ routeToks m := by
  unfold routeToks
  split_ifs <;> simp

theorem aNext_lt (m j : ℕ) (hm : m ≤ 33) (hj : j < 17) : aNext m j < 52 := by
  rw [aNext_eq]
  split_ifs <;> omega

theorem routeNext_lt (i : Fin 3) (m : ℕ) (t : Tok) (ht : t ∈ routeToks m) : routeNext i m t < 52 := by
  unfold routeToks at ht
  split_ifs at ht with h0 h34
  · rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := jIdx_lt i v hv
      simp only [routeNext, if_pos h0]
      omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := jIdx_lt i v hv
      simp only [routeNext]
      omega
  · rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := jIdx_lt i v hv
      simp only [routeNext, if_neg h0]
      split_ifs with hA
      · exact aNext_lt m _ hA this
      · omega
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h
      simp only [routeNext]
      omega
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 ht
    simp only [routeNext]
    omega

/-! ### The Bellman inequality and the family bound -/

/-- **Bellman inequality** of the real family automaton of axis `i`, from the certificate check. -/
theorem fam_bellman (i : Fin 3) (st fB : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden)
    (hchk : checkN 104 (famMoves st lf linkT mkT) (famE Qden) Qden fB = true) (n : ℕ) (hn : n < 104) :
    famEnd n + ∑ t ∈ famToks n, tokW n t * ((fB (famNext i n t) : ℝ) / Qden) ≤ (fB n : ℝ) / Qden := by
  have hc := checkN_spec hchk n hn
  have hQ : (0 : ℝ) < Qden := by norm_num [Qden]
  have hF : ∀ k, (0 : ℝ) ≤ (fB k : ℝ) / Qden := fun k => by positivity
  -- one check line, cast to `ℝ` and divided by `Q²`
  have key : ∀ (L : List (ℕ × ℕ)) (e0 : ℕ), e0 * Qden + (L.map fun mv => mv.1 * fB mv.2).sum ≤ fB n * Qden →
      (e0 : ℝ) / Qden + (L.map fun mv => (mv.1 : ℝ) / Qden * ((fB mv.2 : ℝ) / Qden)).sum ≤
        (fB n : ℝ) / Qden := by
    intro L e0 h
    have hR := (Nat.cast_le (α := ℝ)).2 h
    simp only [Nat.cast_add, Nat.cast_mul] at hR
    rw [cast_list_sum_map] at hR
    rw [sum_map_scale]
    set S := (L.map fun mv => (mv.1 : ℝ) * fB mv.2).sum
    have h3 : S ≤ ((fB n : ℝ) - e0) * Qden := by linarith
    have h4 : S / (Qden : ℝ) ^ 2 ≤ ((fB n : ℝ) - e0) * Qden / (Qden : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have h5 : ((fB n : ℝ) - e0) * Qden / (Qden : ℝ) ^ 2 = ((fB n : ℝ) - e0) / Qden := by
      rw [pow_two, mul_div_mul_right _ _ hQ.ne']
    have h6 : (e0 : ℝ) / Qden + ((fB n : ℝ) - e0) / Qden = (fB n : ℝ) / Qden := by ring
    linarith
  by_cases hlt : n < 52
  · rw [famMoves, if_pos hlt, famE, if_pos (by omega)] at hc
    have hd := key _ 0 hc
    rw [List.map_append, List.sum_append] at hd
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_zero, zero_div,
      zero_add] at hd
    have hE : famEnd n = 0 := by unfold famEnd; rw [if_pos (by omega)]
    rw [hE, zero_add, famToks, if_pos hlt, Finset.sum_insert (mark_notMem n)]
    have hmk : tokW n Tok.mark * ((fB (famNext i n Tok.mark) : ℝ) / Qden) ≤
        (mkT n : ℝ) / Qden * ((fB (n + 52) : ℝ) / Qden) := by
      have hfm : famNext i n Tok.mark = n + 52 := by simp [famNext, hlt]
      rw [hfm]
      exact mul_le_mul_of_nonneg_right (mark_dom n hlt) (hF _)
    have hroute : ∑ t ∈ routeToks n, tokW n t * ((fB (famNext i n t) : ℝ) / Qden) ≤
        ((routeMoves st lf linkT n).map fun mv => (mv.1 : ℝ) / Qden * ((fB mv.2 : ℝ) / Qden)).sum := by
      have h := route_dom i st hst n hlt n (fun k => (fB k : ℝ) / Qden) hF
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun t ht => ?_)) h
      have hne : t ≠ Tok.mark := fun h => mark_notMem n (h ▸ ht)
      simp only [famNext, if_pos hlt, if_neg hne]
    linarith
  · have hm : n - 52 < 52 := by omega
    rw [famMoves, if_neg hlt] at hc
    have hd := key _ _ hc
    rw [sum_map_shift] at hd
    have hE : famEnd n = (famE Qden n : ℝ) / Qden := by
      unfold famEnd famE
      split_ifs
      · simp
      · exact (div_self hQ.ne').symm
    rw [hE, famToks, if_neg hlt]
    have h := route_dom i st hst (n - 52) hm n (fun k => (fB (k + 52) : ℝ) / Qden) (fun k => hF _)
    have hroute : ∑ t ∈ routeToks (n - 52), tokW n t * ((fB (famNext i n t) : ℝ) / Qden) ≤
        ((routeMoves st lf linkT (n - 52)).map fun mv => (mv.1 : ℝ) / Qden * ((fB (mv.2 + 52) : ℝ) / Qden)).sum := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_)) h
      simp only [famNext, if_neg hlt]
    linarith

/-- **The family factor of axis `i`** is bounded by the certificate vector at `B`, for every word length. -/
theorem fam3_V_le (i : Fin 3) (st fB : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden)
    (hchk : checkN 104 (famMoves st lf linkT mkT) (famE Qden) Qden fB = true) (N : ℕ) :
    (fam3 i).V N 0 ≤ (fB 0 : ℝ) / Qden := by
  refine (fam3 i).V_le (fun n t => tokW_nonneg n t) (fun n => n < 104) ?_ (fun n => (fB n : ℝ) / Qden)
    (fun n hn => fam_bellman i st fB hst hchk n hn) (fun n _ => by positivity) N 0 (by norm_num)
  intro n hn t ht
  show famNext i n t < 104
  change t ∈ famToks n at ht
  unfold famToks at ht
  unfold famNext
  split_ifs at ht ⊢ with hlt htm
  · omega
  · rcases Finset.mem_insert.1 ht with h | h
    · exact absurd h htm
    · have := routeNext_lt i n t h
      omega
  · have := routeNext_lt i (n - 52) t ht
    omega

theorem fBT0 : fBT 0 = 2734104547231 := by decide +kernel
theorem fBY0 : fBY 0 = 2741437430948 := by decide +kernel
theorem Qden_cast : ((Qden : ℕ) : ℝ) = 10 ^ 15 := by norm_num [Qden]

/-- **Family factor, axis t**: `F0t ≤ 2.205114e-3`. -/
theorem famT_V_le (N : ℕ) : (fam3 0).V N 0 ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := fam3_V_le 0 stT fBT stepQ_le_T famT_ok N
  rw [fBT0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

/-- **Family factor, axis x**: `F0x ≤ 2.205114e-3` (the same table as axis t). -/
theorem famX_V_le (N : ℕ) : (fam3 1).V N 0 ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := fam3_V_le 1 stT fBT stepQ_le_X famT_ok N
  rw [fBT0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

/-- **Family factor, axis y**: `F0y ≤ 2.208103e-3`. -/
theorem famY_V_le (N : ℕ) : (fam3 2).V N 0 ≤ (2741437430948 : ℝ) / 10 ^ 15 := by
  have h := fam3_V_le 2 stY fBY stepQ_le_Y famY_ok N
  rw [fBY0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

/-- **Family words, axis `i`**: any finite set of allowed family words from `B` (before the mark) weighs at most
the certificate value. -/
theorem fam3_words_le (i : Fin 3) (st fB : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden)
    (hchk : checkN 104 (famMoves st lf linkT mkT) (famE Qden) Qden fB = true) (R : Finset (List Tok))
    (hR : ∀ r ∈ R, (fam3 i).Gram 0 r) : ∑ r ∈ R, (fam3 i).wt 0 r ≤ (fB 0 : ℝ) / Qden := by
  set N := R.sup List.length
  refine le_trans ((fam3 i).sum_wt_le (fun n t => tokW_nonneg n t) famEnd_nonneg N 0 R fun r hr =>
    ⟨hR r hr, Finset.le_sup hr⟩) (fam3_V_le i st fB hst hchk N)

theorem famT_words_le (R : Finset (List Tok)) (hR : ∀ r ∈ R, (fam3 0).Gram 0 r) :
    ∑ r ∈ R, (fam3 0).wt 0 r ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := fam3_words_le 0 stT fBT stepQ_le_T famT_ok R hR
  rw [fBT0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

theorem famX_words_le (R : Finset (List Tok)) (hR : ∀ r ∈ R, (fam3 1).Gram 0 r) :
    ∑ r ∈ R, (fam3 1).wt 0 r ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := fam3_words_le 1 stT fBT stepQ_le_X famT_ok R hR
  rw [fBT0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

theorem famY_words_le (R : Finset (List Tok)) (hR : ∀ r ∈ R, (fam3 2).Gram 0 r) :
    ∑ r ∈ R, (fam3 2).wt 0 r ≤ (2741437430948 : ℝ) / 10 ^ 15 := by
  have h := fam3_words_le 2 stY fBY stepQ_le_Y famY_ok R hR
  rw [fBY0] at h
  rw [Qden_cast] at h
  exact_mod_cast h

end QECD1
