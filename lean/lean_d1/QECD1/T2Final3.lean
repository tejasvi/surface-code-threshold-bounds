import QECD1.T2Trick3

/-!
# The 3D T2 bound

The 3D analogue of the 2D `TwoD/T2Sum`, `TwoD/T2Final` and `Stage1.prob_T2ev_le_t2Count`.

* `t2Sets3`: the counted-block sets of valid T2 skeletons on the lattice; `botBlocks`: the blocks of the bottom strip.
* `skW3_sum_le`: a finite set of valid skeletons with lattice bottom blocks weighs at most
  `|botBlocks| · RF · (topB3ex + 8.3757 topB3)`: group by the bottom part, bound the bottom route words by the route
  automaton (`route3_V_le`) and the tails by the transfer with an exempt first jump (`transfer3_ex_top`).
* `t2Sets3_sum_le`: with the λ-trick (`skel_trick3`), `Σ_{B ∈ t2Sets3} ε*^{|B|} ≤ |botBlocks| · RF ·
  (topB3ex + 8.3757 topB3) · e^{λ cE} · e^{-s (n_y - 47)}`.
* `prob_T2_le3`: the union bound with (H_eps) on a set `R` containing the undeclared blocks and skeleton existence
  (`t2SkelExistsOn3`): `P(T2 ∧ ¬T1) ≤ Σ_{B ∈ t2Sets3} ε^{|B|}`.
* `t2_bound3`: the 3D T2 bound at `ε = ε*`.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

/-- The counted-block sets of valid T2 skeletons on the lattice. -/
noncomputable def t2Sets3 (T w h ny : ℕ) (cE : ℝ) : Finset (Finset V3) :=
  (latBlocks T w h).powerset.filter (fun B => ∃ sk : T2Sk3, sk.OK ny cE ∧ sk.b0 ∈ latBlocks T w h ∧
    (∀ b ∈ sk.counted, b ∈ latBlocks T w h) ∧ B = sk.counted.toFinset)

/-- The blocks of the bottom strip. -/
noncomputable def botBlocks (T w h : ℕ) : Finset V3 := (latBlocks T w h).filter (fun b => b.2.2 ≤ hs3)

/-- The weight of a skeleton: its bottom route word times the transfer weight of its tail. -/
noncomputable def skW3 (ny : ℕ) (sk : T2Sk3) : ℝ :=
  route3.wt 1 sk.ms0 * (t2TD ((ny : ℤ) - 1)).tailW C3 (endOf sk.b0 sk.ms0) sk.fams sk.top

theorem counted_nodup3 {ny : ℕ} {cE : ℝ} {sk : T2Sk3} (hok : sk.OK ny cE) : sk.counted.Nodup := by
  refine hok.2.2.2.2.2.2.imp fun {a b} hab => ?_
  rintro rfl
  rw [dist3_self, Const.D_val] at hab
  omega

theorem skelW_nonneg (k : Skel3) : 0 ≤ skelW k := by
  unfold skelW
  have := eps_pos
  positivity

theorem topB3ex_nonneg : 0 ≤ topB3ex := by
  unfold topB3ex
  have := JF2_nonneg
  have := eps_nonneg
  have : (0 : ℝ) ≤ RFq := by norm_num [RFq]
  positivity

theorem route3_wt_nonneg (q : ℕ) (ms : List Tok) : 0 ≤ route3.wt q ms :=
  route3.wt_nonneg (fun _ t => tokW_nonneg 0 t) (fun _ => zero_le_one) q ms

/-- **Bottom route words**: any finite set of words from `A` weighs at most `RF`. -/
theorem bot_words_le (W : Finset (List Tok)) (hW : ∀ ms ∈ W, route3.Gram 1 ms) :
    ∑ ms ∈ W, route3.wt 1 ms ≤ (RFq : ℝ) := by
  refine (route3.sum_wt_le (fun _ t => tokW_nonneg 0 t) (fun _ => zero_le_one) (W.sup List.length) 1 W
    fun ms hms => ⟨hW ms hms, Finset.le_sup (f := List.length) hms⟩).trans ?_
  exact route3_V_le _

/-- **The sum over skeletons**: a finite set of valid skeletons with bottom blocks in the lattice weighs at most
`|botBlocks| · RF · (topB3ex + 8.3757 topB3)`. -/
theorem skW3_sum_le {ny : ℕ} {cE : ℝ} (SK : Finset T2Sk3)
    (hSK : ∀ sk ∈ SK, sk.OK ny cE ∧ sk.b0 ∈ latBlocks T w h) :
    ∑ sk ∈ SK, skW3 ny sk ≤ (botBlocks T w h).card * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) := by
  set Y : ℤ := (ny : ℤ) - 1 with hY
  have hC : 0 ≤ topB3ex + 8.3757 * topB3 := by
    have := topB3ex_nonneg
    have := topB3_nonneg
    linarith
  set Ks := SK.image (fun sk : T2Sk3 => (sk.b0, sk.ms0)) with hKs
  rw [← Finset.sum_fiberwise_of_maps_to (s := SK) (t := Ks) (g := fun sk : T2Sk3 => (sk.b0, sk.ms0))
    (fun sk hsk => Finset.mem_image_of_mem _ hsk)]
  -- each fiber: one bottom part, the tails bounded by the transfer
  have hfib : ∀ k ∈ Ks, ∑ sk ∈ SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k), skW3 ny sk ≤
      route3.wt 1 k.2 * (topB3ex + 8.3757 * topB3) := by
    intro k _
    have hrw : ∀ sk ∈ SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k),
        skW3 ny sk = route3.wt 1 k.2 * (t2TD Y).tailW C3 (endOf k.1 k.2) sk.fams sk.top := by
      intro sk hsk
      obtain ⟨-, hkey⟩ := Finset.mem_filter.1 hsk
      rw [← hkey]
      rfl
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (route3_wt_nonneg 1 k.2)
    have hinj : ∀ a ∈ SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k),
        ∀ b ∈ SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k),
          (fun sk : T2Sk3 => (sk.fams, sk.top)) a = (fun sk : T2Sk3 => (sk.fams, sk.top)) b → a = b := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      obtain ⟨ab0, ams0, afams, atop⟩ := a
      obtain ⟨bb0, bms0, bfams, btop⟩ := b
      simp only [Prod.mk.injEq] at ha' hb' hab
      obtain ⟨rfl, rfl⟩ := ha'
      obtain ⟨rfl, rfl⟩ := hb'
      obtain ⟨rfl, rfl⟩ := hab
      rfl
    calc ∑ sk ∈ SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k), (t2TD Y).tailW C3 (endOf k.1 k.2) sk.fams sk.top
        = ∑ x ∈ (SK.filter (fun sk : T2Sk3 => (sk.b0, sk.ms0) = k)).image (fun sk : T2Sk3 => (sk.fams, sk.top)),
            (t2TD Y).tailW C3 (endOf k.1 k.2) x.1 x.2 := by
          rw [Finset.sum_image hinj]
      _ ≤ topB3ex + 8.3757 * topB3 := by
          refine transfer3_ex_top skelEncoding exitSk Y skelW_nonneg (endOf k.1 k.2) _ fun x hx => ?_
          obtain ⟨sk, hsk, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨hskSK, hkey⟩ := Finset.mem_filter.1 hsk
          have htail := ((hSK sk hskSK).1).2.2.1
          rw [← hkey]
          exact htail
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.sum_mul]
  -- the bottom parts: grouped by the bottom block
  have hbot : ∑ k ∈ Ks, route3.wt 1 k.2 ≤ (botBlocks T w h).card * (RFq : ℝ) := by
    have hmaps : ∀ k ∈ Ks, k.1 ∈ botBlocks T w h := by
      intro k hk
      obtain ⟨sk, hsk, rfl⟩ := Finset.mem_image.1 hk
      exact Finset.mem_filter.2 ⟨(hSK sk hsk).2, (hSK sk hsk).1.1⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ b ∈ botBlocks T w h, ∑ k ∈ Ks.filter (fun k => k.1 = b), route3.wt 1 k.2
        ≤ ∑ _b ∈ botBlocks T w h, (RFq : ℝ) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have hinj : ∀ k ∈ Ks.filter (fun k => k.1 = b), ∀ k' ∈ Ks.filter (fun k => k.1 = b),
              Prod.snd k = Prod.snd k' → k = k' := by
            intro k hk k' hk' hkk
            exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) hkk
          rw [← Finset.sum_image hinj]
          refine bot_words_le _ fun ms hms => ?_
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hms
          obtain ⟨sk, hsk, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hk).1
          exact (hSK sk hsk).1.2.1
      _ = (botBlocks T w h).card * (RFq : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ k ∈ Ks, route3.wt 1 k.2) * (topB3ex + 8.3757 * topB3)
      ≤ ((botBlocks T w h).card * (RFq : ℝ)) * (topB3ex + 8.3757 * topB3) := mul_le_mul_of_nonneg_right hbot hC
    _ = _ := by ring

/-- **The counted-block sets of valid T2 skeletons**, weighted by `ε*`, with the λ-trick. -/
theorem t2Sets3_sum_le (T w h ny : ℕ) (cE : ℝ) :
    ∑ B ∈ t2Sets3 T w h ny cE, eps ^ B.card ≤
      (botBlocks T w h).card * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * Real.exp (lam * cE) *
        Real.exp (-sT * ((ny : ℝ) - 47)) := by
  have : Nonempty T2Sk3 := ⟨⟨(0, 0, 0), [], [], ((0, 0, 0), [], false)⟩⟩
  have hex : ∀ B ∈ t2Sets3 T w h ny cE, ∃ sk : T2Sk3, sk.OK ny cE ∧ sk.b0 ∈ latBlocks T w h ∧
      (∀ b ∈ sk.counted, b ∈ latBlocks T w h) ∧ B = sk.counted.toFinset := fun B hB => (Finset.mem_filter.1 hB).2
  choose! skOf hskOf using hex
  have hbound : ∀ B ∈ t2Sets3 T w h ny cE, eps ^ B.card ≤
      skW3 ny (skOf B) * Real.exp (lam * cE) * Real.exp (-sT * ((ny : ℝ) - 47)) := by
    intro B hB
    obtain ⟨hok, -, -, hBeq⟩ := hskOf B hB
    have hcard : B.card = (skOf B).counted.length := by
      have hc := List.toFinset_card_of_nodup (counted_nodup3 hok)
      rw [← hBeq] at hc
      exact hc
    rw [hcard]
    exact skel_trick3 (skOf B) hok
  have hinj : ∀ B ∈ t2Sets3 T w h ny cE, ∀ B' ∈ t2Sets3 T w h ny cE, skOf B = skOf B' → B = B' := by
    intro B hB B' hB' hBB
    rw [(hskOf B hB).2.2.2, (hskOf B' hB').2.2.2, hBB]
  have hsum := skW3_sum_le ((t2Sets3 T w h ny cE).image skOf) fun sk hsk => by
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hsk
    exact ⟨(hskOf B hB).1, (hskOf B hB).2.1⟩
  have he1 : 0 ≤ Real.exp (lam * cE) := (Real.exp_pos _).le
  have he2 : 0 ≤ Real.exp (-sT * ((ny : ℝ) - 47)) := (Real.exp_pos _).le
  calc ∑ B ∈ t2Sets3 T w h ny cE, eps ^ B.card
      ≤ ∑ B ∈ t2Sets3 T w h ny cE, skW3 ny (skOf B) * Real.exp (lam * cE) * Real.exp (-sT * ((ny : ℝ) - 47)) :=
        Finset.sum_le_sum hbound
    _ = (∑ sk ∈ (t2Sets3 T w h ny cE).image skOf, skW3 ny sk) * Real.exp (lam * cE) *
          Real.exp (-sT * ((ny : ℝ) - 47)) := by
        rw [Finset.sum_image hinj, Finset.sum_mul, Finset.sum_mul]
    _ ≤ ((botBlocks T w h).card * (RFq : ℝ) * (topB3ex + 8.3757 * topB3)) * Real.exp (lam * cE) *
          Real.exp (-sT * ((ny : ℝ) - 47)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum he1) he2

/-- **The blocks of the bottom strip**: at most `n_t n_x (h_s + 1)` for `T + 1 = n_t L`, `w + 1 = n_x L`. -/
theorem botBlocks_card_le {nt nx : ℕ} (hT : T + 1 = nt * 35) (hw : w + 1 = nx * 35) :
    (botBlocks T w h).card ≤ nt * nx * (hs3 + 1) := by
  have hsub : botBlocks T w h ⊆ (range nt ×ˢ range nx ×ˢ range (hs3 + 1)).image
      (fun q : ℕ × ℕ × ℕ => ((q.1 : ℤ), (q.2.1 : ℤ), (q.2.2 : ℤ))) := by
    intro b hb
    obtain ⟨hbl, hby⟩ := Finset.mem_filter.1 hb
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hbl
    have h1 := v.1.isLt
    have h2 := v.2.1.isLt
    have hy : (v.2.2.val : ℤ) / 35 ≤ hs3 := hby
    rw [hs3_val] at hy
    rw [Finset.mem_image]
    refine ⟨(v.1.val / 35, v.2.1.val / 35, v.2.2.val / 35), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range, hs3_val]
      omega
    · refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show ((v.1.val / 35 : ℕ) : ℤ) = (v.1.val : ℤ) / 35
        omega
      · show ((v.2.1.val / 35 : ℕ) : ℤ) = (v.2.1.val : ℤ) / 35
        omega
      · show ((v.2.2.val / 35 : ℕ) : ℤ) = (v.2.2.val : ℤ) / 35
        omega
  calc (botBlocks T w h).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (range nt ×ˢ range nx ×ˢ range (hs3 + 1)).card := Finset.card_image_le
    _ = nt * nx * (hs3 + 1) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range, Finset.card_range]
        ring

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **The union bound for the T2 event without T1**: with (H_eps) on a set `R` containing the undeclared blocks,
`P(T2 ∧ ¬T1)` is at most the `ε`-weighted number of counted-block sets of valid T2 skeletons. -/
theorem prob_T2_le3 {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) {ny : ℕ} (hh : h + 1 = ny * 35)
    {wh : ℝ} (hwh0 : 0 ≤ wh) (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ ε) :
    prob p (fun X : PEdge3 T w h → Bool => S.T2ev3 Z ny (toZ2 X) ∧ ¬ S.T1ev3 ny (toZ2 X)) ≤
      ∑ B ∈ t2Sets3 T w h ny (67 + 2 * wh / 35), ε ^ B.card := by
  have hsymm : ∀ {a b : V3}, Const.D ≤ dist3 a b → Const.D ≤ dist3 b a := fun {a b} hab => by
    rw [dist3_comm]
    exact hab
  have h := skel_union_le_rows hp0 hp1 hε0 (fun b X => S.bad (toZ2 X) b) (fun b => S.bad_dependsOn b) R hε
    (t2Sets3 T w h ny (67 + 2 * wh / 35)) (fun B => B.toList)
    (A := fun X => S.T2ev3 Z ny (toZ2 X) ∧ ¬ S.T1ev3 ny (toZ2 X)) (fun X hX => by
      obtain ⟨sk, hok, hb0, hbad⟩ := S.t2SkelExistsOn3 Z hh hwh0 hwt0 hunit hwh hX.1 hX.2
      have hnd := counted_nodup3 hok
      have hperm : sk.counted.toFinset.toList.Perm sk.counted :=
        List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) hnd (by simp)
      refine ⟨sk.counted.toFinset, ?_, (hperm.pairwise_iff hsymm).2 hok.2.2.2.2.2.2, fun b hb => ?_,
        fun b hb => ?_⟩
      · rw [t2Sets3, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun b hb => (hbad b (List.mem_toFinset.1 hb)).2, sk, hok, hb0, fun b hb => (hbad b hb).2, rfl⟩
      · exact hR b (hok.2.2.2.2.2.1 b (List.mem_toFinset.1 (Finset.mem_toList.1 hb)))
      · exact (hbad b (List.mem_toFinset.1 (Finset.mem_toList.1 hb))).1)
  refine h.trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun B _ _ => pow_nonneg hε0 _).trans ?_
  exact le_of_eq (Finset.sum_congr rfl fun B _ => by rw [Finset.length_toList])

/-- **The 3D T2 bound** at `ε = ε*`: `P(T2 ∧ ¬T1) ≤ |botBlocks| · RF · (topB3ex + 8.3757 topB3) ·
e^{λ (67 + 2 wh / 35)} · e^{-s (n_y - 47)}`. -/
theorem t2_bound3 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ny : ℕ} (hh : h + 1 = ny * 35)
    {wh : ℝ} (hwh0 : 0 ≤ wh) (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ eps) :
    prob p (fun X : PEdge3 T w h → Bool => S.T2ev3 Z ny (toZ2 X) ∧ ¬ S.T1ev3 ny (toZ2 X)) ≤
      (botBlocks T w h).card * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * Real.exp (lam * (67 + 2 * wh / 35)) *
        Real.exp (-sT * ((ny : ℝ) - 47)) :=
  (S.prob_T2_le3 Z hp0 hp1 eps_nonneg hh hwh0 hwt0 hunit hwh R hR hε).trans (t2Sets3_sum_le T w h ny _)

/-- **The 3D T2 bound with the bottom blocks counted**: on a code of `n_t × n_x × n_y` blocks,
`P(T2 ∧ ¬T1) ≤ n_t n_x (h_s + 1) · RF · (topB3ex + 8.3757 topB3) · e^{λ (67 + 2 wh / 35)} · e^{-s (n_y - 47)}`. -/
theorem t2_bound3_count {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {nt nx ny : ℕ} (hT : T + 1 = nt * 35)
    (hw : w + 1 = nx * 35) (hh : h + 1 = ny * 35)
    {wh : ℝ} (hwh0 : 0 ≤ wh) (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (fun X : PEdge3 T w h → Bool => S.bad (toZ2 X) b) ≤ eps) :
    prob p (fun X : PEdge3 T w h → Bool => S.T2ev3 Z ny (toZ2 X) ∧ ¬ S.T1ev3 ny (toZ2 X)) ≤
      ((nt * nx * (hs3 + 1) : ℕ) : ℝ) * (RFq : ℝ) * (topB3ex + 8.3757 * topB3) * Real.exp (lam * (67 + 2 * wh / 35)) *
        Real.exp (-sT * ((ny : ℝ) - 47)) := by
  refine (S.t2_bound3 Z hp0 hp1 hh hwh0 hwt0 hunit hwh R hR hε).trans ?_
  have hcard : ((botBlocks T w h).card : ℝ) ≤ ((nt * nx * (hs3 + 1) : ℕ) : ℝ) := by
    exact_mod_cast botBlocks_card_le hT hw
  have hRF : (0 : ℝ) ≤ RFq := by norm_num [RFq]
  have hC : 0 ≤ topB3ex + 8.3757 * topB3 := by
    have := topB3ex_nonneg
    have := topB3_nonneg
    linarith
  have he1 : 0 ≤ Real.exp (lam * (67 + 2 * wh / 35)) := (Real.exp_pos _).le
  have he2 : 0 ≤ Real.exp (-sT * ((ny : ℝ) - 47)) := (Real.exp_pos _).le
  have h1 := mul_le_mul_of_nonneg_right hcard hRF
  have h2 := mul_le_mul_of_nonneg_right h1 hC
  have h3 := mul_le_mul_of_nonneg_right h2 he1
  exact mul_le_mul_of_nonneg_right h3 he2

end Stage13

end QECD1
