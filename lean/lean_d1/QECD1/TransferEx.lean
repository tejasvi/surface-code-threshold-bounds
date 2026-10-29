import QECD1.Top

/-!
# The exempt first jump, and the bridge from blocks to offsets

The 2D `tail_transfer_ex` (TwoD/T2Transfer) treats the first jump of a tail as exempt from `(R)`. That jump has no
landing-distance condition, so its sum runs over the full lattice (`JFbd`). This module ports it.

* `full_prod_le`, `jump_full3`: jumps from `c` to any finite set of blocks weigh at most `JF2`, the full tilted lattice
  sum `((1 + q)/(1 - q))² (1 + q₋/(1 - q₋) + q₊/(1 - q₊))`, about 3.8875e6 (at `λ = 0.014`, `s = 0.007`).
* `TData.transfer_ex`: tails whose first jump is exempt weigh at most `topBex + JF · C · F0 · topB / (1 - r)`.
* 3D:
  * `topgen_sum_le` is the top-part sum for any jump condition with a jump bound;
  * `top3ex_sum_le` handles exempt counted top roots, with `topB3ex = JF2 ε* RF + 1` (the uncounted part is the
    vertical projection of the exit);
  * `r1_le` gives `r1 = JF2 e^{30 λ} ε* F0s ≤ 0.8987` (value 0.8986), and `r3_le'` the ratio `r ≤ 0.8927`;
  * `transfer3_ex_top` bounds the tails with an exempt first jump by `topB3ex + 8.3757 topB3`, the exact transfer
    factor `r1/(1 - r)`.
* `sum_blocks_le_offsets`: a sum over the blocks `b` with `D ≤ |b - c|∞ ≤ A` of a nonnegative function of `b - c` is
  at most the sum over the offset set `{D ≤ |v|∞ ≤ A}`. This is how sums over actual blocks of a finite 3D code reduce
  to the `S0`/`S1` sums of this development (`sum_blocks_S0`, `sum_blocks_S1`), as the 2D `sum_offsets_le`.
-/

namespace QECD1

open QECD1.Tab

/-! ### Full-lattice jumps -/

theorem full_prod_le (f g : ℤ → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ c, 0 ≤ g c) (Fu Gu : ℝ)
    (hFu : ∀ K : ℕ, ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a ≤ Fu)
    (hGu : ∀ K : ℕ, ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c ≤ Gu) (S : Finset V3) :
    ∑ v ∈ S, f v.1 * f v.2.1 * g v.2.2 ≤ Fu * (Fu * Gu) := by
  set K := S.sup linf
  have hsub : S ⊆ box K := fun v hv => (mem_box v K).2 (Finset.le_sup hv)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => mul_nonneg (mul_nonneg (hf v.1) (hf v.2.1)) (hg v.2.2))
  rw [sum_box_prod] at h1
  have hP0 : 0 ≤ ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a := Finset.sum_nonneg fun a _ => hf a
  have hG0 : 0 ≤ ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c := Finset.sum_nonneg fun c _ => hg c
  have hFu0 : 0 ≤ Fu := le_trans hP0 (hFu K)
  have h2 := mul_le_mul (hFu K) (mul_le_mul (hFu K) (hGu K) hG0 hFu0) (mul_nonneg hP0 hG0) hFu0
  linarith

/-- The full tilted lattice sum with rational parameters. -/
noncomputable def JF2 : ℝ :=
  ((1 + (qUpT : ℝ)) / (1 - qUpT)) * (((1 + (qUpT : ℝ)) / (1 - qUpT)) *
    (1 + (qmUp : ℝ) / (1 - qmUp) + (qpUp : ℝ) / (1 - qpUp)))

/-- **Exempt jumps**: from `c` to any finite set of blocks. -/
theorem jump_full3 (c : V3) (E : Finset V3) : ∑ e ∈ E, jw3 c e ≤ JF2 := by
  have hqU : Real.exp (-lam) ≤ (qUpT : ℝ) := exp_neg_lamT_le
  set q := Real.exp (-lam)
  set qm := Real.exp (-(lam - sT))
  set qp := Real.exp (-(lam + sT))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqm0 : 0 ≤ qm := (Real.exp_pos _).le
  have hqp0 : 0 ≤ qp := (Real.exp_pos _).le
  have hU1 : (qUpT : ℝ) < 1 := by norm_num [qUpT]
  have hmU1 : (qmUp : ℝ) < 1 := by norm_num [qmUp]
  have hpU1 : (qpUp : ℝ) < 1 := by norm_num [qpUp]
  have hq1 : q < 1 := lt_of_le_of_lt hqU hU1
  have hqm1 : qm < 1 := lt_of_le_of_lt exp_qm_le hmU1
  have hqp1 : qp < 1 := lt_of_le_of_lt exp_qp_le hpU1
  set f : ℤ → ℝ := fun a => q ^ a.natAbs
  set g : ℤ → ℝ := fun c => if 0 ≤ c then qm ^ c.natAbs else qp ^ c.natAbs
  have hinj : Set.InjOn (fun e : V3 => e - c) (E : Set V3) := fun e _ e' _ h => sub_left_injective h
  have hre : ∑ e ∈ E, jw3 c e = ∑ v ∈ E.image (fun e => e - c), f v.1 * f v.2.1 * g v.2.2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact exp_tilt_split (e - c)
  rw [hre]
  have hf : ∀ a, 0 ≤ f a := fun a => pow_nonneg hq0 _
  have hg : ∀ c, 0 ≤ g c := fun c => by
    show 0 ≤ (if 0 ≤ c then qm ^ c.natAbs else qp ^ c.natAbs)
    split_ifs
    · exact pow_nonneg hqm0 _
    · exact pow_nonneg hqp0 _
  have hFu : ∀ K : ℕ, ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a ≤ (1 + (qUpT : ℝ)) / (1 - qUpT) := by
    intro K
    have h1 : ∑ a ∈ Finset.Icc (-(K : ℤ)) K, f a = S1 q K := rfl
    rw [h1]
    refine le_trans (S1_le q hq0 hq1 K) ?_
    have hpos : 0 < 1 - q := by linarith
    have hposU : (0 : ℝ) < 1 - qUpT := by linarith
    rw [div_le_div_iff₀ hpos hposU]
    nlinarith
  have hGu : ∀ K : ℕ, ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c ≤
      1 + (qmUp : ℝ) / (1 - qmUp) + (qpUp : ℝ) / (1 - qpUp) := by
    intro K
    have h1 : ∑ c ∈ Finset.Icc (-(K : ℤ)) K, g c = Ty qm qp K := rfl
    rw [h1]
    refine le_trans (Ty_le qm qp hqm0 hqm1 hqp0 hqp1 K) ?_
    have := frac_mono qm qmUp hmU1 exp_qm_le
    have := frac_mono qp qpUp hpU1 exp_qp_le
    linarith
  exact full_prod_le f g hf hg _ _ hFu hGu _

theorem JF2_nonneg : 0 ≤ JF2 := by
  have h := jump_full3 0 ∅
  simpa using h

/-! ### The transfer with an exempt first jump -/

namespace TData

variable {P FK Top : Type} (D : TData P FK Top)

/-- Tails whose first jump is exempt from the jump condition; `tokEx`: tops entered by an exempt jump. -/
def TailOKex (tokEx : P → Top → Prop) : P → List (P × FK) → Top → Prop
  | c, [], t => tokEx c t
  | _, s :: ss, t => D.root s.2 = s.1 ∧ D.fok s.2 ∧ D.TailOK (D.exit s.2) ss t

/-- **The transfer with an exempt first jump** (2D `tail_transfer_ex`). -/
theorem transfer_ex [DecidableEq P] [DecidableEq FK] [DecidableEq Top] (C Jbd JF F0 topB topBex : ℝ)
    (tokEx : P → Top → Prop) (hC : 0 ≤ C) (hJbd : 0 ≤ Jbd) (hJF : 0 ≤ JF) (hF0 : 0 ≤ F0) (htopB : 0 ≤ topB)
    (hjw : ∀ c e, 0 ≤ D.jw c e) (hfw : ∀ k, 0 ≤ D.fw k) (htw : ∀ c t, 0 ≤ D.tw c t)
    (hJ : ∀ (c : P) (E : Finset P), (∀ e ∈ E, D.jok c e) → ∑ e ∈ E, D.jw c e ≤ Jbd)
    (hJF' : ∀ (c : P) (E : Finset P), ∑ e ∈ E, D.jw c e ≤ JF)
    (hF : ∀ (e : P) (K : Finset FK), (∀ k ∈ K, D.root k = e ∧ D.fok k) → ∑ k ∈ K, D.fw k ≤ F0)
    (hT : ∀ (c : P) (T : Finset Top), (∀ t ∈ T, D.tok c t) → ∑ t ∈ T, D.tw c t ≤ topB)
    (hTex : ∀ (c : P) (T : Finset Top), (∀ t ∈ T, tokEx c t) → ∑ t ∈ T, D.tw c t ≤ topBex)
    (hr : Jbd * C * F0 < 1) (c : P) (S : Finset (List (P × FK) × Top))
    (hS : ∀ x ∈ S, D.TailOKex tokEx c x.1 x.2) :
    ∑ x ∈ S, D.tailW C c x.1 x.2 ≤ topBex + JF * C * F0 * (topB / (1 - Jbd * C * F0)) := by
  set B := topB / (1 - Jbd * C * F0)
  have h1r : 0 < 1 - Jbd * C * F0 := by linarith
  have hB0 : 0 ≤ B := div_nonneg htopB h1r.le
  rw [← Finset.sum_filter_add_sum_filter_not S (fun x => x.1 = [])]
  -- tails without families: tops entered by an exempt jump
  have hA : ∑ x ∈ S.filter (fun x => x.1 = []), D.tailW C c x.1 x.2 ≤ topBex := by
    set S0' := S.filter fun x => x.1 = []
    have hnil : ∀ x ∈ S0', x.1 = [] := fun x hx => (Finset.mem_filter.1 hx).2
    have hinj : Set.InjOn Prod.snd (S0' : Set (List (P × FK) × Top)) := by
      intro x hx y hy h
      exact Prod.ext ((hnil x hx).trans (hnil y hy).symm) h
    have heq : ∑ x ∈ S0', D.tailW C c x.1 x.2 = ∑ t ∈ S0'.image Prod.snd, D.tw c t := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hnil x hx]
      rfl
    rw [heq]
    refine hTex c _ fun t ht => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    have h := hS x (Finset.mem_filter.1 hx).1
    rw [hnil x hx] at h
    exact h
  -- tails with a family: the first step, then a regular tail
  set S1 := S.filter fun x => ¬ x.1 = []
  set H := S1.biUnion fun x => (x.1.head?).toFinset
  have hmem : ∀ x ∈ S1, ∃ h ∈ H, x.1 = h :: x.1.tail := by
    intro x hx
    have hne := (Finset.mem_filter.1 hx).2
    cases hx1 : x.1 with
    | nil => exact absurd hx1 hne
    | cons a l =>
      refine ⟨a, Finset.mem_biUnion.2 ⟨x, hx, ?_⟩, rfl⟩
      rw [hx1]
      simp
  have hmaps : ∀ x ∈ S1, x.1.head? ∈ H.image some := by
    intro x hx
    obtain ⟨h, hh, hx1⟩ := hmem x hx
    rw [hx1]
    exact Finset.mem_image_of_mem _ hh
  have hsum1 : ∑ x ∈ S1, D.tailW C c x.1 x.2 =
      ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * ∑ y ∈ restOf S1 h, D.tailW C (D.exit h.2) y.1 y.2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_image (fun _ _ _ _ e => Option.some.inj e)]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hinj : Set.InjOn (fun x : List (P × FK) × Top => (x.1.tail, x.2))
        ((S1.filter fun x => x.1.head? = some h : Finset (List (P × FK) × Top)) :
          Set (List (P × FK) × Top)) := by
      intro x hx y hy e
      have ex := (Finset.mem_filter.1 hx).2
      have ey := (Finset.mem_filter.1 hy).2
      simp only [Prod.mk.injEq] at e
      refine Prod.ext ?_ e.2
      cases hx1 : x.1 with
      | nil => rw [hx1] at ex; simp at ex
      | cons a l =>
        cases hy1 : y.1 with
        | nil => rw [hy1] at ey; simp at ey
        | cons b m =>
          rw [hx1] at ex e
          rw [hy1] at ey e
          simp only [List.head?_cons, Option.some.injEq] at ex ey
          simp only [List.tail_cons] at e
          rw [ex, ey, e.1]
    unfold restOf
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have ex := (Finset.mem_filter.1 hx).2
    cases hx1 : x.1 with
    | nil => rw [hx1] at ex; simp at ex
    | cons a l =>
      rw [hx1] at ex
      simp only [List.head?_cons, Option.some.injEq] at ex
      subst ex
      show D.tailW C c (a :: l) x.2 = D.jw c a.1 * C * D.fw a.2 * D.tailW C (D.exit a.2) (a :: l).tail x.2
      rfl
  have hH : ∀ h ∈ H, D.root h.2 = h.1 ∧ D.fok h.2 := by
    intro h hh
    obtain ⟨x, hx, hxh⟩ := Finset.mem_biUnion.1 hh
    have hok := hS x (Finset.mem_filter.1 hx).1
    cases hx1 : x.1 with
    | nil => rw [hx1] at hxh; simp at hxh
    | cons a l =>
      rw [hx1] at hxh hok
      simp only [List.head?_cons, Option.mem_toFinset, Option.mem_def, Option.some.injEq] at hxh
      subst hxh
      exact ⟨hok.1, hok.2.1⟩
  have hrest : ∀ h ∈ H, ∑ y ∈ restOf S1 h, D.tailW C (D.exit h.2) y.1 y.2 ≤ B := by
    intro h _
    refine D.transfer C Jbd F0 topB hC hJbd hF0 htopB hjw hfw htw hJ hF hT hr (D.exit h.2) _ fun y hy => ?_
    unfold restOf at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hxS1, hxh⟩ := Finset.mem_filter.1 hx
    have hok := hS x (Finset.mem_filter.1 hxS1).1
    cases hx1 : x.1 with
    | nil => rw [hx1] at hxh; simp at hxh
    | cons a l =>
      rw [hx1] at hxh hok
      simp only [List.head?_cons, Option.some.injEq] at hxh
      subst hxh
      exact hok.2.2
  have hgroup : ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * ∑ y ∈ restOf S1 h, D.tailW C (D.exit h.2) y.1 y.2 ≤
      ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * B :=
    Finset.sum_le_sum fun h hh =>
      mul_le_mul_of_nonneg_left (hrest h hh) (mul_nonneg (mul_nonneg (hjw _ _) hC) (hfw _))
  have hfirst : ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * B ≤ JF * F0 * C * B := by
    set E := H.image Prod.fst
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := E) (fun h hh => Finset.mem_image_of_mem _ hh)]
    have hE : ∀ e ∈ E, ∑ h ∈ H.filter (fun h => h.1 = e), D.jw c h.1 * C * D.fw h.2 * B ≤
        D.jw c e * (F0 * C * B) := by
      intro e _
      have hinj : Set.InjOn Prod.snd ((H.filter (fun h => h.1 = e) : Finset (P × FK)) : Set (P × FK)) := by
        intro h hh h' hh' eq
        exact Prod.ext ((Finset.mem_filter.1 hh).2.trans (Finset.mem_filter.1 hh').2.symm) eq
      have h1 : ∑ h ∈ H.filter (fun h => h.1 = e), D.jw c h.1 * C * D.fw h.2 * B =
          D.jw c e * C * B * ∑ k ∈ (H.filter (fun h => h.1 = e)).image Prod.snd, D.fw k := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [(Finset.mem_filter.1 hh).2]
        ring
      have h2 : ∑ k ∈ (H.filter (fun h => h.1 = e)).image Prod.snd, D.fw k ≤ F0 := by
        refine hF e _ fun k hk => ?_
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hk
        obtain ⟨hhH, hhe⟩ := Finset.mem_filter.1 hh
        obtain ⟨hroot, hfok⟩ := hH h hhH
        exact ⟨hroot.trans hhe, hfok⟩
      rw [h1]
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (hjw c e) hC) hB0)
      linarith
    refine le_trans (Finset.sum_le_sum hE) ?_
    rw [← Finset.sum_mul]
    have hJE := hJF' c E
    have := mul_le_mul_of_nonneg_right hJE (mul_nonneg (mul_nonneg hF0 hC) hB0)
    linarith
  have hB1 : JF * F0 * C * B = JF * C * F0 * B := by ring
  linarith

end TData

/-! ### The 3D instance -/

/-- The top-part sum for any jump condition `jv` with a jump bound `Jb`. -/
theorem topgen_sum_le (jv : V3 → V3 → Prop) (Jb : ℝ)
    (hJb : ∀ (c : V3) (E : Finset V3), (∀ e ∈ E, jv c e) → ∑ e ∈ E, jw3 c e ≤ Jb)
    (Y : ℤ) (c : V3) (T : Finset Top3)
    (hT : ∀ t ∈ T, if t.2.2 then jv c t.1 ∧ route3.Gram 1 t.2.1 else
      t.2.1 = [] ∧ t.1 = ((c.1, c.2.1, Y) : V3) ∧ c.2.2 ≤ Y) :
    ∑ t ∈ T, tw3 c t ≤ Jb * eps * (RFq : ℝ) + 1 := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.2.2 = true)]
  refine add_le_add ?_ ?_
  · set T1 := T.filter fun t => t.2.2 = true
    have hT1 : ∀ t ∈ T1, jv c t.1 ∧ route3.Gram 1 t.2.1 ∧ t.2.2 = true := by
      intro t ht
      obtain ⟨htT, htf⟩ := Finset.mem_filter.1 ht
      have h := hT t htT
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
    have hJ : ∑ et ∈ T1.image Prod.fst, jw3 c et ≤ Jb := by
      refine hJb c _ fun et het => ?_
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 het
      exact (hT1 t ht).1
    have h0 : (0 : ℝ) ≤ eps * RFq := mul_nonneg eps_nonneg (by norm_num [RFq])
    have := mul_le_mul_of_nonneg_right hJ h0
    linarith
  · set T0 := T.filter fun t => ¬ t.2.2 = true
    set p : Top3 := (((c.1, c.2.1, Y) : V3), ([] : List Tok), false)
    have hT0 : ∀ t ∈ T0, t = p ∧ c.2.2 ≤ Y := by
      intro t ht
      obtain ⟨htT, htf⟩ := Finset.mem_filter.1 ht
      have h := hT t htT
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

/-- Top parts entered by an exempt jump (the uncounted part is the vertical projection of `c`). -/
def tok3ex (Y : ℤ) (c : V3) (t : Top3) : Prop :=
  if t.2.2 then route3.Gram 1 t.2.1 else t.2.1 = [] ∧ t.1 = ((c.1, c.2.1, Y) : V3) ∧ c.2.2 ≤ Y

/-- The top factor with an exempt jump: `JF2 ε* RF + 1`. -/
noncomputable def topB3ex : ℝ := JF2 * eps * (RFq : ℝ) + 1

theorem top3ex_sum_le (Y : ℤ) (c : V3) (T : Finset Top3) (hT : ∀ t ∈ T, tok3ex Y c t) :
    ∑ t ∈ T, tw3 c t ≤ topB3ex := by
  refine topgen_sum_le (fun _ _ => True) JF2 (fun c E _ => jump_full3 c E) Y c T fun t ht => ?_
  have h := hT t ht
  unfold tok3ex at h
  split_ifs at h ⊢
  · exact ⟨trivial, h⟩
  · exact h

theorem r1_num : JF2 * (eoffUpT : ℝ) * (37 / 2000000) * F0s ≤ 8987 / 10000 := by
  unfold JF2 F0s
  norm_num [qUpT, qmUp, qpUp, eoffUpT]

theorem r1_le : JF2 * C3 * F0s ≤ 8987 / 10000 := by
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := exp_offT_le
  have h := r1_num
  have e : (37 / 2000000 : ℝ) = eps := rfl
  rw [e] at h
  unfold C3
  have h1 : JF2 * (Real.exp (lam * 30) * eps) * F0s ≤ JF2 * ((eoffUpT : ℝ) * eps) * F0s := by
    have := mul_le_mul_of_nonneg_right hE eps_nonneg
    have := mul_le_mul_of_nonneg_left this JF2_nonneg
    exact mul_le_mul_of_nonneg_right this F0s_nonneg
  have h2 : JF2 * ((eoffUpT : ℝ) * eps) * F0s = JF2 * (eoffUpT : ℝ) * eps * F0s := by ring
  linarith

/-- The transfer ratio, sharper than `r3_le`: at most `0.8927`. -/
theorem r3_num' : Jbar2 * (eoffUpT : ℝ) * (37 / 2000000) * F0s ≤ 8927 / 10000 := by
  unfold Jbar2 F0s
  norm_num [qUpT, qLoT, qmUp, qmLo, qpUp, qpLo, eoffUpT]

theorem r3_le' : Jbar2 * C3 * F0s ≤ 8927 / 10000 := by
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := exp_offT_le
  have h := r3_num'
  have e : (37 / 2000000 : ℝ) = eps := rfl
  rw [e] at h
  unfold C3
  have h1 : Jbar2 * (Real.exp (lam * 30) * eps) * F0s ≤ Jbar2 * ((eoffUpT : ℝ) * eps) * F0s := by
    have := mul_le_mul_of_nonneg_right hE eps_nonneg
    have := mul_le_mul_of_nonneg_left this Jbar2_nonneg
    exact mul_le_mul_of_nonneg_right this F0s_nonneg
  have h2 : Jbar2 * ((eoffUpT : ℝ) * eps) * F0s = Jbar2 * (eoffUpT : ℝ) * eps * F0s := by ring
  linarith

/-- **Tails with an exempt first jump and 3D top parts** weigh at most `topB3ex + 8.3757 topB3`: the transfer
factor `r1/(1 - r) ≤ 0.8987/(1 - 0.8927) = 8.3756`. -/
theorem transfer3_ex_top {FK : Type} [DecidableEq FK] (E : Encoding3DRooted FK) (exitF : FK → V3) (Y : ℤ)
    (hw : ∀ k, 0 ≤ E.w k) (c : V3) (S : Finset (List (V3 × FK) × Top3))
    (hS : ∀ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw3 (tok3 Y)).TailOKex (tok3ex Y) c x.1 x.2) :
    ∑ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw3 (tok3 Y)).tailW C3 c x.1 x.2 ≤
      topB3ex + 8.3757 * topB3 := by
  have hC : 0 ≤ C3 := mul_nonneg (Real.exp_pos _).le eps_nonneg
  have hr := r3_le
  have h := (TData.mk jw3 jok3 E.root exitF E.fok E.w tw3 (tok3 Y)).transfer_ex C3 Jbar2 JF2 F0s topB3 topB3ex
    (tok3ex Y) hC Jbar2_nonneg JF2_nonneg F0s_nonneg topB3_nonneg (fun _ _ => (Real.exp_pos _).le) hw tw3_nonneg
    (fun c E hE => landing3 c E hE) (fun c E => jump_full3 c E) (fun e K hK => famB3_rooted E e K hK)
    (fun c T hT => top3_sum_le Y c T hT) (fun c T hT => top3ex_sum_le Y c T hT) (by linarith) c S hS
  have hr' := r3_le'
  have h1 : 0 < 1 - Jbar2 * C3 * F0s := by linarith
  have h2 : topB3 / (1 - Jbar2 * C3 * F0s) ≤ 10000 / 1073 * topB3 := by
    rw [div_le_iff₀ h1]
    have := topB3_nonneg
    nlinarith
  have h3 := r1_le
  have hB0 : 0 ≤ topB3 / (1 - Jbar2 * C3 * F0s) := div_nonneg topB3_nonneg h1.le
  have h4 : JF2 * C3 * F0s * (topB3 / (1 - Jbar2 * C3 * F0s)) ≤ 8987 / 10000 * (10000 / 1073 * topB3) := by
    have hr1 : 0 ≤ JF2 * C3 * F0s := mul_nonneg (mul_nonneg JF2_nonneg hC) F0s_nonneg
    exact mul_le_mul h3 h2 hB0 (by norm_num)
  have h5 : 8987 / 10000 * (10000 / 1073 * topB3) ≤ 8.3757 * topB3 := by
    have := topB3_nonneg
    nlinarith
  linarith

/-! ### From blocks to offsets -/

/-- **Blocks to offsets**: a sum over blocks at `ℓ∞` distance in `[D, A]` from `cur` of a nonnegative function of the
offset is at most the sum over the offset set. -/
theorem sum_blocks_le_offsets (cur : V3) (B : Finset V3) (D A : ℕ) (f : V3 → ℝ) (hf : ∀ v, 0 ≤ f v) :
    ∑ b ∈ B.filter (fun b => D ≤ linf (b - cur) ∧ linf (b - cur) ≤ A), f (b - cur) ≤
      ∑ v ∈ (box A).filter (fun v => D ≤ linf v), f v := by
  have hinj : Set.InjOn (fun b : V3 => b - cur)
      ((B.filter (fun b => D ≤ linf (b - cur) ∧ linf (b - cur) ≤ A) : Finset V3) : Set V3) :=
    fun b _ b' _ h => sub_left_injective h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => hf v)
  intro v hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hb
  exact Finset.mem_filter.2 ⟨(mem_box _ _).2 h2, h1⟩

theorem sum_blocks_S0 (cur : V3) (B : Finset V3) (f : V3 → ℝ) (hf : ∀ v, 0 ≤ f v) :
    ∑ b ∈ B.filter (fun b => 5 ≤ linf (b - cur) ∧ linf (b - cur) ≤ 8), f (b - cur) ≤ ∑ v ∈ S0, f v :=
  sum_blocks_le_offsets cur B 5 8 f hf

theorem sum_blocks_S1 (cur : V3) (B : Finset V3) (f : V3 → ℝ) (hf : ∀ v, 0 ≤ f v) :
    ∑ b ∈ B.filter (fun b => 5 ≤ linf (b - cur) ∧ linf (b - cur) ≤ 24), f (b - cur) ≤ ∑ v ∈ S1off, f v :=
  sum_blocks_le_offsets cur B 5 24 f hf

end QECD1
