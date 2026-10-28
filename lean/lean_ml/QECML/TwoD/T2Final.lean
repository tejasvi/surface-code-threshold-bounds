import QECML.TwoD.T2Assemble

/-!
# The T2 summation: numbers and the sum over skeleton keys

* Numbers at the parameters: `Jbd ≤ 2916.3`, `JFbd ≤ 3123.5`, `Sx ≤ 48.79`, `e^{0.041 · 20.5} ≤ 2.3176`,
  `e^{0.041 · 48.85} ≤ 7.4102`.
* `sum_keys_le`: over any finite set of valid skeleton keys, the skeleton weights sum to at most
  `n_x (8 · 1.81 · B + topB true + r1 · B)` with `B = 157.3`, `r1 = 0.7004`, given the family bound `FamB G 0.1935`.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-! ### Numbers -/

theorem Sx_le : (1 + (qUp : ℝ)) / (1 - qUp) ≤ 48.79 := by
  norm_num [qUp]

theorem JFbd_le : JFbd ≤ 3123.5 := by
  norm_num [JFbd, qUp, qpUp, qmUp]

theorem box_sum_eq (q : ℝ) : ∑ k ∈ Finset.Icc 1 8, q ^ k = q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5 + q ^ 6 + q ^ 7 + q ^ 8 := by
  rw [show Finset.Icc 1 8 = ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) by decide]
  simp [Finset.sum_insert]
  ring

theorem Jbd_le : Jbd ≤ 2916.3 := by
  unfold Jbd
  rw [box_sum_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [qUp, qpUp, qmUp]

theorem exp_off_le : Real.exp (0.041 * 20.5) ≤ 2.3176 := by
  have h := Real.exp_bound (x := 0.041 * 20.5) (by norm_num [abs_of_pos]) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  norm_num
  linarith [h.1, h.2]

theorem exp_half_le : Real.exp 0.5 ≤ 1.6487213 := by
  have h := Real.exp_bound (x := 0.5) (by norm_num [abs_of_pos]) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  linarith [h.1, h.2]

theorem exp_small_le : Real.exp 0.00285 ≤ 1.0028541 := by
  have h := Real.exp_bound (x := 0.00285) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  rw [abs_le] at h
  linarith [h.1, h.2]

theorem exp_ends_le : Real.exp (0.041 * 48.85) ≤ 7.4102 := by
  rw [show (0.041 : ℝ) * 48.85 = (4 : ℕ) * 0.5 + 0.00285 by norm_num, Real.exp_add, Real.exp_nat_mul]
  have h1 := exp_half_le
  have h2 := exp_small_le
  have h0 : 0 ≤ Real.exp 0.5 := (Real.exp_pos _).le
  have h3 : Real.exp 0.5 ^ 4 ≤ 1.6487213 ^ 4 := pow_le_pow_left₀ h0 h1 4
  have h4 : 0 ≤ Real.exp 0.5 ^ 4 := pow_nonneg h0 4
  calc Real.exp 0.5 ^ 4 * Real.exp 0.00285 ≤ 1.6487213 ^ 4 * 1.0028541 :=
        mul_le_mul h3 h2 (Real.exp_pos _).le (by norm_num)
    _ ≤ 7.4102 := by norm_num

theorem topB_false_le : topB false ≤ 54.404 := by
  unfold topB
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 := Jbd_le
  have h2 := Sx_le
  linarith

theorem topB_true_le : topB true ≤ 54.803 := by
  unfold topB
  simp only [↓reduceIte]
  have h1 := JFbd_le
  have h2 := Sx_le
  linarith

theorem r_le : Jbd * Real.exp (0.041 * 20.5) * 5e-4 * 0.1935 ≤ 0.654 := by
  have h1 := Jbd_le
  have h2 := exp_off_le
  have h0 := Jbd_nonneg
  have he := (Real.exp_pos (0.041 * 20.5)).le
  calc Jbd * Real.exp (0.041 * 20.5) * 5e-4 * 0.1935 ≤ 2916.3 * 2.3176 * 5e-4 * 0.1935 := by
        have := mul_le_mul h1 h2 he (by norm_num)
        nlinarith
    _ ≤ 0.654 := by norm_num

theorem r1_le : JFbd * Real.exp (0.041 * 20.5) * 5e-4 * 0.1935 ≤ 0.7004 := by
  have h1 := JFbd_le
  have h2 := exp_off_le
  have h0 := JFbd_nonneg
  have he := (Real.exp_pos (0.041 * 20.5)).le
  calc JFbd * Real.exp (0.041 * 20.5) * 5e-4 * 0.1935 ≤ 3123.5 * 2.3176 * 5e-4 * 0.1935 := by
        have := mul_le_mul h1 h2 he (by norm_num)
        nlinarith
    _ ≤ 0.7004 := by norm_num

theorem B_fix : topB false + 0.654 * 157.3 ≤ 157.3 := by
  have := topB_false_le
  linarith

/-! ### Skeleton keys -/

/-- A skeleton as data: the bottom flag, start block, bottom route and the tail. -/
abbrev SkKey (G : S3Geom) := Bool × G.Block × List G.Move × TailD G

/-- The key of a skeleton. -/
def skKey (sk : G.T2Sk) : SkKey G := (sk.bf, sk.b0, sk.ms0, (sk.fams.map famKey, sk.et, sk.mst, sk.tf))

/-- The weight of a skeleton key. -/
noncomputable def skWK (k : SkKey G) : ℝ :=
  gwt (t2g 5e-4 0.04305 0.02) k.2.1 k.2.2.1 *
    tailWK 5e-4 0.041 0.04305 0.02 20.5 (endBlock k.2.1 k.2.2.1) k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2

/-- The counted blocks of a skeleton key. -/
def countedK (k : SkKey G) : List G.Block :=
  k.2.2.1.map Move.blk ++ (k.2.2.2.1.flatMap (fun key => key.2.1) ++
    ((if k.2.2.2.2.2.2 then [k.2.2.2.2.1] else []) ++ k.2.2.2.2.2.1.map Move.blk))

theorem counted_eq_countedK (sk : G.T2Sk) : sk.counted = countedK (skKey sk) := by
  simp only [T2Sk.counted, countedK, skKey, List.flatMap_map]
  rfl

theorem skW_eq_skWK (sk : G.T2Sk) :
    skW 5e-4 0.041 0.04305 0.02 20.5 sk = skWK (skKey sk) := by
  simp only [skW, skWK, skKey]
  rw [tailW_eq_tailWK]

/-- The validity of a skeleton key. -/
def SkKeyOK (k : SkKey G) : Prop :=
  (k.1 = true → k.2.1.2.val ≤ 7 ∧ GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A k.2.1 k.2.2.1 ∧
      (∀ m ∈ k.2.2.1.getLast?, ¬ m.isLink) ∧
      TailOK false (endBlock k.2.1 k.2.2.1) k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2) ∧
  (k.1 = false → k.2.2.1 = [] ∧ k.2.1.2.val = 0 ∧
      TailOK true k.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2)

/-- **The sum over skeleton keys.** -/
theorem sum_keys_le (hD : G.D = 5) (hFB : FamB G 0.1935) (X : Finset (SkKey G)) (hX : ∀ k ∈ X, SkKeyOK k) :
    ∑ k ∈ X, skWK k ≤ (G.nx : ℝ) * (8 * 1.81 * 157.3 + (topB true + 0.7004 * 157.3)) := by
  have hF0 : (0 : ℝ) ≤ 0.1935 := by norm_num
  have hB0 : (0 : ℝ) ≤ 157.3 := by norm_num
  rw [← Finset.sum_filter_add_sum_filter_not X (fun k => k.1 = true), mul_add]
  refine add_le_add ?_ ?_
  · -- bf = true: start in the bottom strip, bottom route, tails with (R)
    set XT := X.filter (fun k => k.1 = true) with hXT
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k : SkKey G => (k.2.1, k.2.2.1))
      (t := XT.image (fun k : SkKey G => (k.2.1, k.2.2.1))) (fun k hk => Finset.mem_image_of_mem _ hk)]
    have hfib : ∀ p ∈ XT.image (fun k : SkKey G => (k.2.1, k.2.2.1)),
        ∑ k ∈ XT with (k.2.1, k.2.2.1) = p, skWK k ≤ gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 * 157.3 := by
      intro p _
      have heq : ∀ k ∈ XT.filter (fun k : SkKey G => (k.2.1, k.2.2.1) = p), skWK k =
          gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 *
            tailWK 5e-4 0.041 0.04305 0.02 20.5 (endBlock p.1 p.2) k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1
              k.2.2.2.2.2.2 := by
        intro k hk
        rw [← (Finset.mem_filter.1 hk).2]
        rfl
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      have hinj : Set.InjOn (fun k : SkKey G => k.2.2.2)
          ((XT.filter (fun k : SkKey G => (k.2.1, k.2.2.1) = p) : Finset _) : Set (SkKey G)) := by
        intro k hk k' hk' h
        have h1 := (Finset.mem_filter.1 hk).2
        have h2 := (Finset.mem_filter.1 hk').2
        have h3 := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
        have h4 := (Finset.mem_filter.1 (Finset.mem_filter.1 hk').1).2
        have e12 := h1.trans h2.symm
        simp only [Prod.mk.injEq] at e12
        exact Prod.ext (h3.trans h4.symm) (Prod.ext e12.1 (Prod.ext e12.2 h))
      rw [← Finset.sum_image (f := fun t : TailD G =>
        tailWK 5e-4 0.041 0.04305 0.02 20.5 (endBlock p.1 p.2) t.1 t.2.1 t.2.2.1 t.2.2.2) hinj]
      have hg : 0 ≤ gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 :=
        gwt_nonneg (t2g_nonneg (ε := 5e-4) (by norm_num) _ _) _ _
      set U := (XT.filter (fun k : SkKey G => (k.2.1, k.2.2.1) = p)).image (fun k : SkKey G => k.2.2.2) with hU
      have hT : ∀ t ∈ U, t.1.length ≤ U.sup (fun t : TailD G => t.1.length) ∧
          TailOK false (endBlock p.1 p.2) t.1 t.2.1 t.2.2.1 t.2.2.2 := by
        intro t ht
        refine ⟨Finset.le_sup (f := fun t : TailD G => t.1.length) ht, ?_⟩
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht
        have hp := (Finset.mem_filter.1 hk).2
        have hkX := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
        have hbf := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
        have hok := ((hX k hkX).1 hbf).2.2.2
        rw [← hp]
        exact hok
      have htr := tail_transfer hD hF0 hFB r_le hB0 B_fix (U.sup (fun t : TailD G => t.1.length))
        (endBlock p.1 p.2) U hT
      exact mul_le_mul_of_nonneg_left htr hg
    calc ∑ p ∈ XT.image (fun k : SkKey G => (k.2.1, k.2.2.1)), ∑ k ∈ XT with (k.2.1, k.2.2.1) = p, skWK k
        ≤ ∑ p ∈ XT.image (fun k : SkKey G => (k.2.1, k.2.2.1)), gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 * 157.3 :=
          Finset.sum_le_sum hfib
      _ = (∑ p ∈ XT.image (fun k : SkKey G => (k.2.1, k.2.2.1)), gwt (t2g 5e-4 0.04305 0.02) p.1 p.2) * 157.3 := by
          rw [Finset.sum_mul]
      _ ≤ ((G.nx : ℝ) * 8 * 1.81) * 157.3 := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          set P := XT.image (fun k : SkKey G => (k.2.1, k.2.2.1)) with hP
          rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := P.image Prod.fst)
            (fun p hp => Finset.mem_image_of_mem _ hp)]
          have hb : ∀ b0 ∈ P.image Prod.fst, ∑ p ∈ P with p.1 = b0, gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 ≤ 1.81 := by
            intro b0 _
            have heq : ∀ p ∈ P.filter (fun p => p.1 = b0), gwt (t2g 5e-4 0.04305 0.02) p.1 p.2 =
                gwt (t2g 5e-4 0.04305 0.02) b0 p.2 := by
              intro p hp
              rw [(Finset.mem_filter.1 hp).2]
            rw [Finset.sum_congr rfl heq]
            have hinj : Set.InjOn (fun p : G.Block × List G.Move => p.2)
                ((P.filter (fun p => p.1 = b0) : Finset _) : Set (G.Block × List G.Move)) := by
              intro p hp p' hp' h
              exact Prod.ext ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hp').2.symm) h
            rw [← Finset.sum_image (f := fun ms => gwt (t2g 5e-4 0.04305 0.02) b0 ms) hinj]
            refine bot_sum_le hD b0 _ fun ms hms => ?_
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hms
            obtain ⟨hpP, hpb⟩ := Finset.mem_filter.1 hp
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hpP
            have hkX := (Finset.mem_filter.1 hk).1
            have hbf := (Finset.mem_filter.1 hk).2
            obtain ⟨-, hgram, hlast, -⟩ := (hX k hkX).1 hbf
            simp only at hpb
            rw [hpb] at hgram
            exact ⟨hgram, hlast⟩
          calc ∑ b0 ∈ P.image Prod.fst, ∑ p ∈ P with p.1 = b0, gwt (t2g 5e-4 0.04305 0.02) p.1 p.2
              ≤ ∑ _b0 ∈ P.image Prod.fst, (1.81 : ℝ) := Finset.sum_le_sum hb
            _ = ((P.image Prod.fst).card : ℝ) * 1.81 := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((G.nx : ℝ) * 8) * 1.81 := by
                refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
                have hsub : P.image Prod.fst ⊆ univ.filter (fun b : G.Block => b.2.val ≤ 7) := by
                  intro b hb
                  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
                  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
                  have hkX := (Finset.mem_filter.1 hk).1
                  have hbf := (Finset.mem_filter.1 hk).2
                  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hX k hkX).1 hbf).1⟩
                have h1 := Finset.card_le_card hsub
                have h2 := card_strip_le (G := G) 7
                have h3 : ((P.image Prod.fst).card : ℝ) ≤ ((G.nx * (7 + 1) : ℕ) : ℝ) := by
                  exact_mod_cast h1.trans h2
                push_cast at h3
                linarith
      _ = (G.nx : ℝ) * (8 * 1.81 * 157.3) := by ring
  · -- bf = false: start next to b₁ in row 0, no bottom route, first jump exempt
    set XF := X.filter (fun k => ¬ k.1 = true) with hXF
    have hw : ∀ k ∈ XF, skWK k = tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.1 k.2.2.2.1 k.2.2.2.2.1
        k.2.2.2.2.2.1 k.2.2.2.2.2.2 := by
      intro k hk
      have hbf : k.1 = false := by simpa using (Finset.mem_filter.1 hk).2
      obtain ⟨hms, -, -⟩ := (hX k (Finset.mem_filter.1 hk).1).2 hbf
      simp only [skWK, hms, gwt, endBlock, one_mul]
    rw [Finset.sum_congr rfl hw]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k : SkKey G => k.2.1)
      (t := XF.image (fun k : SkKey G => k.2.1)) (fun k hk => Finset.mem_image_of_mem _ hk)]
    have hfib : ∀ b0 ∈ XF.image (fun k : SkKey G => k.2.1),
        ∑ k ∈ XF with k.2.1 = b0, tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.1 k.2.2.2.1 k.2.2.2.2.1
          k.2.2.2.2.2.1 k.2.2.2.2.2.2 ≤ topB true + 0.7004 * 157.3 := by
      intro b0 _
      have heq : ∀ k ∈ XF.filter (fun k : SkKey G => k.2.1 = b0),
          tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2 =
          tailWK 5e-4 0.041 0.04305 0.02 20.5 b0 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2 := by
        intro k hk
        rw [(Finset.mem_filter.1 hk).2]
      rw [Finset.sum_congr rfl heq]
      have hinj : Set.InjOn (fun k : SkKey G => k.2.2.2)
          ((XF.filter (fun k : SkKey G => k.2.1 = b0) : Finset _) : Set (SkKey G)) := by
        intro k hk k' hk' h
        have hkX := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
        have hkX' := (Finset.mem_filter.1 (Finset.mem_filter.1 hk').1).1
        have hbf : k.1 = false := by simpa using (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
        have hbf' : k'.1 = false := by simpa using (Finset.mem_filter.1 (Finset.mem_filter.1 hk').1).2
        have hm := ((hX k hkX).2 hbf).1
        have hm' := ((hX k' hkX').2 hbf').1
        have hb := (Finset.mem_filter.1 hk).2
        have hb' := (Finset.mem_filter.1 hk').2
        exact Prod.ext (hbf.trans hbf'.symm) (Prod.ext (hb.trans hb'.symm) (Prod.ext (hm.trans hm'.symm) h))
      rw [← Finset.sum_image (f := fun t : TailD G =>
        tailWK 5e-4 0.041 0.04305 0.02 20.5 b0 t.1 t.2.1 t.2.2.1 t.2.2.2) hinj]
      refine tail_transfer_ex hD hF0 hFB r_le hB0 B_fix r1_le b0 _ fun t ht => ?_
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ht
      have hkX := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
      have hbf : k.1 = false := by simpa using (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
      have hb := (Finset.mem_filter.1 hk).2
      have hok := ((hX k hkX).2 hbf).2.2
      rw [← hb]
      exact hok
    calc ∑ b0 ∈ XF.image (fun k : SkKey G => k.2.1), ∑ k ∈ XF with k.2.1 = b0,
          tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2
        ≤ ∑ _b0 ∈ XF.image (fun k : SkKey G => k.2.1), (topB true + 0.7004 * 157.3) := Finset.sum_le_sum hfib
      _ = ((XF.image (fun k : SkKey G => k.2.1)).card : ℝ) * (topB true + 0.7004 * 157.3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (G.nx : ℝ) * (topB true + 0.7004 * 157.3) := by
          have htop : 0 ≤ topB true + 0.7004 * 157.3 := by
            unfold topB
            have := JFbd_nonneg
            obtain ⟨hq0, hq1, -⟩ := rq_bounds
            have : 0 ≤ (1 + (qUp : ℝ)) / (1 - qUp) := div_nonneg (by linarith) (by linarith)
            simp only [↓reduceIte]
            positivity
          refine mul_le_mul_of_nonneg_right ?_ htop
          have hsub : XF.image (fun k : SkKey G => k.2.1) ⊆ univ.filter (fun b : G.Block => b.2.val ≤ 0) := by
            intro b hb
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
            have hkX := (Finset.mem_filter.1 hk).1
            have hbf : k.1 = false := by simpa using (Finset.mem_filter.1 hk).2
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_eq ((hX k hkX).2 hbf).2.1⟩
          have h1 := Finset.card_le_card hsub
          have h2 := card_strip_le (G := G) 0
          have h3 : ((XF.image (fun k : SkKey G => k.2.1)).card : ℝ) ≤ ((G.nx * (0 + 1) : ℕ) : ℝ) := by
            exact_mod_cast h1.trans h2
          push_cast at h3
          linarith

/-! ### The T2 count -/

/-- The key of a valid skeleton is a valid key. -/
theorem skKeyOK_of (hD : G.D = 5) {κ cH : ℝ} (sk : G.T2Sk)
    (hok : sk.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (Stage1.hs 12) (12 + 2 - G.D) κ cH) : SkKeyOK (skKey sk) := by
  obtain ⟨⟨hb0, hmv, hgr, hhd, hlast, -, hbf⟩, hfam, ⟨-, hmvt, hgrt, hhdt, -, -, -, htf⟩, hR, -, -, -⟩ := hok
  have hhs : Stage1.hs 12 = 7 := by norm_num [Stage1.hs]
  have htop : sk.tf = true → GramFrom G.D (G.D - 1 + 4) (G.D - 1 + 12) .A sk.et sk.mst := fun _ =>
    gram_of_moves sk.mst .A sk.et hmvt hgrt fun m hm => hhdt m hm
  have hfam' : ∀ f ∈ sk.fams, f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
      f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1 := fun f hf => ⟨(hfam f hf).1, (hfam f hf).2.1⟩
  refine ⟨fun h => ⟨?_, ?_, hlast, ?_⟩, fun h => ⟨(hbf h).1, (hbf h).2, ?_⟩⟩
  · rw [← hhs]
    exact hb0
  · exact gram_of_moves sk.ms0 .A sk.b0 hmv hgr fun m hm => hhd m hm
  · refine tailOK_of hD sk.et sk.mst sk.tf htop htf sk.fams false _ hfam' fun i hi _ htf' => ?_
    exact hR i hi (Or.inl h) htf'
  · have hσ : endBlock sk.b0 sk.ms0 = sk.b0 := by rw [(hbf h).1]; rfl
    have := tailOK_of hD sk.et sk.mst sk.tf htop htf sk.fams true (endBlock sk.b0 sk.ms0) hfam'
      fun i hi hi0 htf' => hR i hi (by
        rcases hi0 with h0 | h0
        · exact absurd h0 (by simp)
        · exact Or.inr h0) htf'
    rw [hσ] at this
    exact this

/-- A default skeleton. -/
def T2Sk.default (G : S3Geom) : G.T2Sk :=
  ⟨(⟨0, G.hnx⟩, ⟨0, G.hny⟩), [], true, [], (⟨0, G.hnx⟩, ⟨0, G.hny⟩), [], true⟩

/-- **The T2 count, from the family bound** (`(D, a0, a1) = (5, 4, 12)`, `ε = 5e-4`, metric ratio `κ ≤ 1.05`,
boundary constant `cH ≤ 1.05`): `t2Count ≤ 2·10⁴ n_x e^{-0.02 (n_y - 31)}`. -/
theorem t2Count_le (hD : G.D = 5) (hFB : FamB G 0.1935) {κ cH : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1.05)
    (hcH : cH ≤ 1.05) : G.t2Count 4 12 κ cH 5e-4 ≤ 2e4 * G.nx * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := by
  unfold t2Count
  set sets := G.t2SkelSets G.D (G.D - 1 + 4) (G.D - 1 + 12) (Stage1.hs 12) (12 + 2 - G.D) κ cH with hsets
  -- one skeleton per counted set
  let P : Finset G.Block → G.T2Sk → Prop := fun B sk =>
    sk.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (Stage1.hs 12) (12 + 2 - G.D) κ cH ∧ B = sk.counted.toFinset
  let χ : Finset G.Block → G.T2Sk := fun B => if h : ∃ sk, P B sk then Classical.choose h else T2Sk.default G
  have hχ : ∀ B ∈ sets, P B (χ B) := by
    intro B hB
    have h : ∃ sk, P B sk := (Finset.mem_filter.1 hB).2
    simp only [χ, dite_eq_left h]
    exact Classical.choose_spec h
  have hhs : Stage1.hs 12 = 7 := by norm_num [Stage1.hs]
  -- each set: the λ-trick
  have hone : ∀ B ∈ sets, (5e-4 : ℝ) ^ B.card ≤ skWK (skKey (χ B)) * Real.exp (0.041 * 48.85) *
      Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := by
    intro B hB
    obtain ⟨hok, hBeq⟩ := hχ B hB
    have hnd : (χ B).counted.Nodup := by
      have hpw := hok.2.2.2.2.2.2
      refine hpw.imp fun {b b'} h hbb => ?_
      rw [hbb, G.blockDist_self] at h
      omega
    have hcard : B.card = (χ B).counted.length := by
      calc B.card = ((χ B).counted.toFinset).card := by rw [← hBeq]
        _ = (χ B).counted.length := List.toFinset_card_of_nodup hnd
    have h := skel_trick (χ B) hok (ε := 5e-4) (lam := 0.041) (s := 0.02) (kb := 1.05) (cb := 1.05)
      (by norm_num) (by norm_num) (by norm_num) hκ0 hκ hcH
    have e1 : (0.041 : ℝ) * 1.05 = 0.04305 := by norm_num
    have e2 : 2 * ((G.D : ℕ) : ℝ) * (1 + 1.05) = 20.5 := by rw [hD]; norm_num
    have e3 : (0.041 : ℝ) * (2 * ((G.D : ℕ) : ℝ) + 1.05 * ((G.D : ℕ) : ℝ) + 1.05 * ((Stage1.hs 12 : ℕ) : ℝ) +
        1.05 * (((Stage1.hs 12 : ℕ) : ℝ) + ((G.D - 1 + 12 : ℕ) : ℝ) + 1) + 1.05) = 0.041 * 48.85 := by
      rw [hD, hhs]
      norm_num
    have e4 : -0.02 * ((G.ny : ℝ) - (2 * ((Stage1.hs 12 : ℕ) : ℝ) + ((G.D - 1 + 12 : ℕ) : ℝ) + 1)) =
        -0.02 * ((G.ny : ℝ) - 31) := by
      rw [hD, hhs]
      norm_num
    rw [e1, e2, e3, e4, skW_eq_skWK] at h
    rw [hcard]
    exact h
  -- the sum over sets as a sum over keys
  have hinj : Set.InjOn (fun B => skKey (χ B)) (sets : Set (Finset G.Block)) := by
    intro B hB B' hB' h
    obtain ⟨-, hBeq⟩ := hχ B hB
    obtain ⟨-, hBeq'⟩ := hχ B' hB'
    simp only at h
    rw [hBeq, hBeq', counted_eq_countedK, counted_eq_countedK, h]
  have hkeys : ∀ k ∈ sets.image (fun B => skKey (χ B)), SkKeyOK k := by
    intro k hk
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hk
    exact skKeyOK_of hD (χ B) (hχ B hB).1
  have hsum := sum_keys_le hD hFB _ hkeys
  rw [Finset.sum_image (f := skWK) hinj] at hsum
  have hE := exp_ends_le
  have hT := topB_true_le
  have he0 : 0 ≤ Real.exp (0.041 * 48.85) := (Real.exp_pos _).le
  have hf0 : 0 ≤ Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := (Real.exp_pos _).le
  have hnx : (0 : ℝ) ≤ G.nx := Nat.cast_nonneg _
  calc ∑ B ∈ sets, (5e-4 : ℝ) ^ B.card
      ≤ ∑ B ∈ sets, skWK (skKey (χ B)) * Real.exp (0.041 * 48.85) * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) :=
        Finset.sum_le_sum hone
    _ = (∑ B ∈ sets, skWK (skKey (χ B))) * (Real.exp (0.041 * 48.85) * Real.exp (-0.02 * ((G.ny : ℝ) - 31))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun B _ => by ring
    _ ≤ ((G.nx : ℝ) * (8 * 1.81 * 157.3 + (topB true + 0.7004 * 157.3))) *
          (Real.exp (0.041 * 48.85) * Real.exp (-0.02 * ((G.ny : ℝ) - 31))) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg he0 hf0)
    _ ≤ 2e4 * G.nx * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := by
        have h1 : (G.nx : ℝ) * (8 * 1.81 * 157.3 + (topB true + 0.7004 * 157.3)) ≤ (G.nx : ℝ) * 2442.7 := by
          refine mul_le_mul_of_nonneg_left ?_ hnx
          linarith
        have h2 : Real.exp (0.041 * 48.85) * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) ≤
            7.4102 * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := mul_le_mul_of_nonneg_right hE hf0
        have h3 : 0 ≤ (G.nx : ℝ) * (8 * 1.81 * 157.3 + (topB true + 0.7004 * 157.3)) := by
          refine mul_nonneg hnx ?_
          have := topB_true_le
          unfold topB
          have := JFbd_nonneg
          obtain ⟨hq0, hq1, -⟩ := rq_bounds
          have : 0 ≤ (1 + (qUp : ℝ)) / (1 - qUp) := div_nonneg (by linarith) (by linarith)
          simp only [↓reduceIte]
          positivity
        calc ((G.nx : ℝ) * (8 * 1.81 * 157.3 + (topB true + 0.7004 * 157.3))) *
              (Real.exp (0.041 * 48.85) * Real.exp (-0.02 * ((G.ny : ℝ) - 31)))
            ≤ ((G.nx : ℝ) * 2442.7) * (7.4102 * Real.exp (-0.02 * ((G.ny : ℝ) - 31))) :=
              mul_le_mul h1 h2 (mul_nonneg he0 hf0) (mul_nonneg hnx (by norm_num))
          _ ≤ 2e4 * G.nx * Real.exp (-0.02 * ((G.ny : ℝ) - 31)) := by nlinarith

end S3Geom

end QECML
