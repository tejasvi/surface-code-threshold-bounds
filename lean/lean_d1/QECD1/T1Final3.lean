import QECD1.T1Route3

/-!
# The 3D T1 bound and the failure bound of the decoder

The 3D analogue of the 2D `TwoD/RouteCount` (the geometric T1 count) and of the combination of the T1 and T2
terms.

* `T1Sk3`: a T1 skeleton, a start block in the bottom strip (not counted) and a route word from `A`; `T1Sk3.OK`.
* `t1SkelExistsOn3`: every error in the T1 event has a valid T1 skeleton whose counted blocks are bad lattice blocks
  (`t1_route3`).
* `route1_wt_eq`, `t1_trick3`: the T1 route weights at the y-tilt `s1 = 0.1008`, and `ε*^{|counted|} ≤
  wt₁(ms) · e^{-s1 (n_y - 47)}` for a valid skeleton.
* `t1Sets3_sum_le`, `prob_T1_le3`, `t1_bound3_count`: `P(T1) ≤ n_t n_x (h_s + 1) · α · e^{-s1 (n_y - 47)}`, with
  `α = 66.953` (`route1_words_le`), under (H_eps) at `ε*` on the undeclared blocks.
* `fail_bound3`: a failure of S3' is a T2 event (`T2ev_of_fails3`), so
  `P(S3' fails) ≤ n_t n_x (h_s + 1) · (α e^{-s1 (n_y - 47)} + RF (topB3ex + 8.3757 topB3) e^{λ (67 + 2 wh / 35)}
  e^{-s (n_y - 47)})`.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

theorem route1_gram_iff : ∀ (q : ℕ) (ms : List Tok), route1.Gram q ms ↔ route3.Gram q ms
  | _, [] => Iff.rfl
  | q, t :: ts => by
    show (t ∈ rToks q ∧ route1.Gram (rNext q t) ts) ↔ (t ∈ rToks q ∧ route3.Gram (rNext q t) ts)
    rw [route1_gram_iff (rNext q t) ts]

/-- The T1 weight of a route word in closed form: `ε*` per token, `e^{s1 v_y}` per step and link. -/
theorem route1_wt_eq : ∀ (q : ℕ) (b : V3) (ms : List Tok), Tok.mark ∉ ms →
    route1.wt q ms = eps ^ ms.length * Real.exp (s1 * (((endOf b ms).2.2 : ℝ) - (b.2.2 : ℝ)))
  | q, b, [], _ => by
    simp [WA.wt, route1, endOf]
  | q, b, .step v :: ms, hm => by
    have ih := route1_wt_eq (rNext q (.step v)) (b + v) ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show t1Tok (.step v) * route1.wt (rNext q (.step v)) ms = _
    rw [ih]
    simp only [t1Tok, t1w, List.length_cons, endOf, Prod.snd_add, Int.cast_add]
    have hx : s1 * (((endOf (b + v) ms).2.2 : ℝ) - (b.2.2 : ℝ)) =
        s1 * (v.2.2 : ℝ) + s1 * (((endOf (b + v) ms).2.2 : ℝ) - ((b.2.2 : ℝ) + (v.2.2 : ℝ))) := by ring
    rw [hx, Real.exp_add (s1 * (v.2.2 : ℝ)), pow_succ]
    ring
  | q, b, .link v :: ms, hm => by
    have ih := route1_wt_eq (rNext q (.link v)) (b + v) ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show t1Tok (.link v) * route1.wt (rNext q (.link v)) ms = _
    rw [ih]
    simp only [t1Tok, t1w, List.length_cons, endOf, Prod.snd_add, Int.cast_add]
    have hx : s1 * (((endOf (b + v) ms).2.2 : ℝ) - (b.2.2 : ℝ)) =
        s1 * (v.2.2 : ℝ) + s1 * (((endOf (b + v) ms).2.2 : ℝ) - ((b.2.2 : ℝ) + (v.2.2 : ℝ))) := by ring
    rw [hx, Real.exp_add (s1 * (v.2.2 : ℝ)), pow_succ]
    ring
  | q, b, .leaf v :: ms, hm => by
    have ih := route1_wt_eq (rNext q (.leaf v)) b ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show t1Tok (.leaf v) * route1.wt (rNext q (.leaf v)) ms = _
    rw [ih]
    simp only [t1Tok, List.length_cons, endOf]
    rw [pow_succ]
    ring
  | q, b, .mark :: ms, hm => absurd List.mem_cons_self hm

/-- A 3D T1 skeleton: a start block in the bottom strip (not counted) and a route word from `A`. -/
structure T1Sk3 where
  b0 : V3
  ms : List Tok

namespace T1Sk3

/-- The counted blocks of a T1 skeleton: the blocks of its route word. -/
def counted (sk : T1Sk3) : List V3 := blocksOf sk.b0 sk.ms

/-- **A valid T1 skeleton** (`n_y` block rows). -/
def OK (ny : ℕ) (sk : T1Sk3) : Prop :=
  sk.b0.2.2 ≤ hs3 ∧ route3.Gram 1 sk.ms ∧ (ny : ℤ) ≤ (endOf sk.b0 sk.ms).2.2 + 1 + hs3 + Const.A1 ∧
    (∀ b ∈ sk.counted, ¬ declared3 ny b) ∧ sk.counted.Pairwise (fun a b => Const.D ≤ dist3 a b)

end T1Sk3

theorem t1_counted_nodup3 {ny : ℕ} {sk : T1Sk3} (hok : sk.OK ny) : sk.counted.Nodup := by
  refine hok.2.2.2.2.imp fun {a b} hab => ?_
  rintro rfl
  rw [dist3_self, Const.D_val] at hab
  omega

/-- **The tilt on a valid T1 skeleton.** -/
theorem t1_trick3 {ny : ℕ} {sk : T1Sk3} (hok : sk.OK ny) :
    eps ^ sk.counted.length ≤ route1.wt 1 sk.ms * Real.exp (-s1 * ((ny : ℝ) - 47)) := by
  obtain ⟨hb0, hg, hht, -, -⟩ := hok
  have hm : Tok.mark ∉ sk.ms := mark_notMem_of_route3 _ _ hg
  rw [T1Sk3.counted, blocksOf_length _ _ hm, route1_wt_eq 1 sk.b0 sk.ms hm]
  have hs1 : (0 : ℝ) ≤ s1 := by
    unfold s1
    norm_num
  rw [hs3_val, Const.A1_val] at hht
  rw [hs3_val] at hb0
  have hht' : ((ny : ℤ) : ℝ) ≤ ((endOf sk.b0 sk.ms).2.2 : ℝ) + 1 + 11 + 24 := by exact_mod_cast hht
  have hb0' : (sk.b0.2.2 : ℝ) ≤ 11 := by exact_mod_cast hb0
  have h2 : 0 ≤ ((endOf sk.b0 sk.ms).2.2 : ℝ) - (sk.b0.2.2 : ℝ) - ((ny : ℝ) - 47) := by
    push_cast at hht'
    linarith
  have hexp : 0 ≤ s1 * (((endOf sk.b0 sk.ms).2.2 : ℝ) - (sk.b0.2.2 : ℝ)) + -s1 * ((ny : ℝ) - 47) := by
    nlinarith [mul_nonneg hs1 h2]
  have hpos : 0 ≤ eps ^ sk.ms.length := by
    have := eps_pos
    positivity
  calc eps ^ sk.ms.length = eps ^ sk.ms.length * 1 := (mul_one _).symm
    _ ≤ eps ^ sk.ms.length * Real.exp (s1 * (((endOf sk.b0 sk.ms).2.2 : ℝ) - (sk.b0.2.2 : ℝ)) +
          -s1 * ((ny : ℝ) - 47)) := mul_le_mul_of_nonneg_left (Real.one_le_exp hexp) hpos
    _ = _ := by
        rw [Real.exp_add]
        ring

/-- The counted-block sets of valid T1 skeletons on the lattice. -/
noncomputable def t1Sets3 (T w h ny : ℕ) : Finset (Finset V3) :=
  (latBlocks T w h).powerset.filter (fun B => ∃ sk : T1Sk3, sk.OK ny ∧ sk.b0 ∈ latBlocks T w h ∧
    (∀ b ∈ sk.counted, b ∈ latBlocks T w h) ∧ B = sk.counted.toFinset)

/-- **The counted-block sets of valid T1 skeletons**, weighted by `ε*`. -/
theorem t1Sets3_sum_le (T w h ny : ℕ) :
    ∑ B ∈ t1Sets3 T w h ny, eps ^ B.card ≤
      (botBlocks T w h).card * (alQ : ℝ) * Real.exp (-s1 * ((ny : ℝ) - 47)) := by
  have : Nonempty T1Sk3 := ⟨⟨(0, 0, 0), []⟩⟩
  have hex : ∀ B ∈ t1Sets3 T w h ny, ∃ sk : T1Sk3, sk.OK ny ∧ sk.b0 ∈ latBlocks T w h ∧
      (∀ b ∈ sk.counted, b ∈ latBlocks T w h) ∧ B = sk.counted.toFinset := fun B hB => (Finset.mem_filter.1 hB).2
  choose! skOf hskOf using hex
  have he : 0 ≤ Real.exp (-s1 * ((ny : ℝ) - 47)) := (Real.exp_pos _).le
  have hbound : ∀ B ∈ t1Sets3 T w h ny, eps ^ B.card ≤ route1.wt 1 (skOf B).ms * Real.exp (-s1 * ((ny : ℝ) - 47)) := by
    intro B hB
    obtain ⟨hok, -, -, hBeq⟩ := hskOf B hB
    have hcard : B.card = (skOf B).counted.length := by
      have hc := List.toFinset_card_of_nodup (t1_counted_nodup3 hok)
      rw [← hBeq] at hc
      exact hc
    rw [hcard]
    exact t1_trick3 hok
  have hinj : ∀ B ∈ t1Sets3 T w h ny, ∀ B' ∈ t1Sets3 T w h ny, skOf B = skOf B' → B = B' := by
    intro B hB B' hB' hBB
    rw [(hskOf B hB).2.2.2, (hskOf B' hB').2.2.2, hBB]
  -- the skeletons, grouped by their start block
  set SK := (t1Sets3 T w h ny).image skOf with hSK
  have hSKok : ∀ sk ∈ SK, sk.OK ny ∧ sk.b0 ∈ latBlocks T w h := by
    intro sk hsk
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hsk
    exact ⟨(hskOf B hB).1, (hskOf B hB).2.1⟩
  have hsum : ∑ sk ∈ SK, route1.wt 1 sk.ms ≤ (botBlocks T w h).card * (alQ : ℝ) := by
    have hmaps : ∀ sk ∈ SK, sk.b0 ∈ botBlocks T w h := fun sk hsk =>
      Finset.mem_filter.2 ⟨(hSKok sk hsk).2, (hSKok sk hsk).1.1⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ b ∈ botBlocks T w h, ∑ sk ∈ SK.filter (fun sk => sk.b0 = b), route1.wt 1 sk.ms
        ≤ ∑ _b ∈ botBlocks T w h, (alQ : ℝ) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have hinj' : ∀ sk ∈ SK.filter (fun sk => sk.b0 = b), ∀ sk' ∈ SK.filter (fun sk => sk.b0 = b),
              T1Sk3.ms sk = T1Sk3.ms sk' → sk = sk' := by
            intro sk hsk sk' hsk' hms
            obtain ⟨b1, ms1⟩ := sk
            obtain ⟨b2, ms2⟩ := sk'
            have h1 := (Finset.mem_filter.1 hsk).2
            have h2 := (Finset.mem_filter.1 hsk').2
            simp only at h1 h2 hms
            subst h1 h2 hms
            rfl
          rw [← Finset.sum_image hinj']
          refine route1_words_le _ fun ms hms => ?_
          obtain ⟨sk, hsk, rfl⟩ := Finset.mem_image.1 hms
          exact (route1_gram_iff 1 sk.ms).2 (hSKok sk (Finset.mem_filter.1 hsk).1).1.2.1
      _ = (botBlocks T w h).card * (alQ : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ B ∈ t1Sets3 T w h ny, eps ^ B.card
      ≤ ∑ B ∈ t1Sets3 T w h ny, route1.wt 1 (skOf B).ms * Real.exp (-s1 * ((ny : ℝ) - 47)) :=
        Finset.sum_le_sum hbound
    _ = (∑ sk ∈ SK, route1.wt 1 sk.ms) * Real.exp (-s1 * ((ny : ℝ) - 47)) := by
        rw [hSK, Finset.sum_image hinj, Finset.sum_mul]
    _ ≤ ((botBlocks T w h).card * (alQ : ℝ)) * Real.exp (-s1 * ((ny : ℝ) - 47)) :=
        mul_le_mul_of_nonneg_right hsum he

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **T1 skeleton existence**: every error in the T1 event has a valid T1 skeleton whose start block is a lattice
block and whose counted blocks are bad lattice blocks. -/
theorem t1SkelExistsOn3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} (hT1 : S.T1ev3 ny E) :
    ∃ sk : T1Sk3, sk.OK ny ∧ sk.b0 ∈ latBlocks T w h ∧ ∀ c ∈ sk.counted, S.bad E c ∧ c ∈ latBlocks T w h := by
  obtain ⟨Fm, hFm, hbot, htop⟩ := hT1
  obtain ⟨b0, ms, hb0F, hb0y, hg, hblk, hpw, hht⟩ := S.t1_route3 hh hFm hbot htop
  refine ⟨⟨b0, ms⟩, ⟨hb0y, hg, hht, fun b hb => not_declared_of_inter ⟨(hblk b hb).2.1, (hblk b hb).2.2⟩, hpw⟩,
    S.badSet_sub_lat ny E (S.fam_sub_bad hFm hb0F), fun c hc => ?_⟩
  obtain ⟨hcF, hca, hcb⟩ := hblk c hc
  have hnd := not_declared_of_inter ⟨hca, hcb⟩
  have hcB := S.fam_sub_bad hFm hcF
  exact ⟨S.badSet_bad ny E c hcB hnd, S.badSet_sub_lat ny E hcB⟩

/-- **The union bound for the T1 event.** -/
theorem prob_T1_le3 {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) {ny : ℕ} (hh : h + 1 = ny * 35)
    (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ ε) :
    prob p (fun X : PEdge3 T w h → Bool => S.T1ev3 ny (toZ2 X)) ≤ ∑ B ∈ t1Sets3 T w h ny, ε ^ B.card := by
  have hsymm : ∀ {a b : V3}, Const.D ≤ dist3 a b → Const.D ≤ dist3 b a := fun {a b} hab => by
    rw [dist3_comm]
    exact hab
  have hu := skel_union_le_rows hp0 hp1 hε0 (fun b X => S.bad (toZ2 X) b) (fun b => S.bad_dependsOn b) R hε
    (t1Sets3 T w h ny) (fun B => B.toList) (A := fun X => S.T1ev3 ny (toZ2 X)) (fun X hX => by
      obtain ⟨sk, hok, hb0, hbad⟩ := S.t1SkelExistsOn3 hh hX
      have hnd := t1_counted_nodup3 hok
      have hperm : sk.counted.toFinset.toList.Perm sk.counted :=
        List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) hnd (by simp)
      refine ⟨sk.counted.toFinset, ?_, (hperm.pairwise_iff hsymm).2 hok.2.2.2.2, fun b hb => ?_, fun b hb => ?_⟩
      · rw [t1Sets3, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun b hb => (hbad b (List.mem_toFinset.1 hb)).2, sk, hok, hb0, fun b hb => (hbad b hb).2, rfl⟩
      · exact hR b (hok.2.2.2.1 b (List.mem_toFinset.1 (Finset.mem_toList.1 hb)))
      · exact (hbad b (List.mem_toFinset.1 (Finset.mem_toList.1 hb))).1)
  refine hu.trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun B _ _ => pow_nonneg hε0 _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun B _ => by rw [Finset.length_toList])

/-- **The 3D T1 bound** at `ε = ε*`: `P(T1) ≤ n_t n_x (h_s + 1) · α · e^{-s1 (n_y - 47)}`. -/
theorem t1_bound3_count {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {nt nx ny : ℕ} (hT : T + 1 = nt * 35)
    (hw : w + 1 = nx * 35) (hh : h + 1 = ny * 35) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ eps) :
    prob p (fun X : PEdge3 T w h → Bool => S.T1ev3 ny (toZ2 X)) ≤
      ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (alQ : ℝ) * Real.exp (-s1 * ((ny : ℝ) - 47)) := by
  refine ((S.prob_T1_le3 hp0 hp1 eps_nonneg hh R hR hε).trans (t1Sets3_sum_le T w h ny)).trans ?_
  have hcard : ((botBlocks T w h).card : ℝ) ≤ ((nt * nx * (hs3 + 1) : ℕ) : ℝ) := by
    exact_mod_cast botBlocks_card_le hT hw
  have hal : (0 : ℝ) ≤ alQ := by norm_num [alQ]
  have he : 0 ≤ Real.exp (-s1 * ((ny : ℝ) - 47)) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hal) he

/-- **The failure bound of S3' on the 3D code** (the T1 and T2 terms). For a solver with unit bulk weights and
half-edge weights in `[0, wh]`, and (H_eps) at `ε*` on a set `R` containing the undeclared blocks,
`P(S3' fails) ≤ n_t n_x (h_s + 1) · (α e^{-s1 (n_y - 47)} + RF (topB3ex + 8.3757 topB3) e^{λ (67 + 2 wh / 35)}
e^{-s (n_y - 47)})`. -/
theorem fail_bound3 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {nt nx ny : ℕ} (hT : T + 1 = nt * 35)
    (hw : w + 1 = nx * 35) (hh : h + 1 = ny * 35)
    {wh : ℝ} (hwh0 : 0 ≤ wh) (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ eps) :
    prob p (fun X : PEdge3 T w h → Bool => failsOn3 (dec3 S Z) (toZ2 X)) ≤
      ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (alQ : ℝ) * Real.exp (-s1 * ((ny : ℝ) - 47)) +
        ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) *
          Real.exp (lam * (67 + 2 * wh / 35)) * Real.exp (-sT * ((ny : ℝ) - 47)) := by
  have hsplit : prob p (fun X : PEdge3 T w h → Bool => failsOn3 (dec3 S Z) (toZ2 X)) ≤
      prob p (fun X : PEdge3 T w h → Bool =>
        S.T1ev3 ny (toZ2 X) ∨ (S.T2ev3 Z ny (toZ2 X) ∧ ¬ S.T1ev3 ny (toZ2 X))) := by
    refine prob_mono hp0 hp1 fun X hX => ?_
    have hT2 := S.T2ev_of_fails3 Z (ny := ny) hX
    by_cases hT1 : S.T1ev3 ny (toZ2 X)
    · exact Or.inl hT1
    · exact Or.inr ⟨hT2, hT1⟩
  refine hsplit.trans ((prob_or_le hp0 hp1 _ _).trans (add_le_add ?_ ?_))
  · exact S.t1_bound3_count hp0 hp1 hT hw hh R hR hε
  · exact S.t2_bound3_count Z hp0 hp1 hT hw hh hwh0 hwt0 hunit hwh R hR hε

end Stage13

end QECD1
