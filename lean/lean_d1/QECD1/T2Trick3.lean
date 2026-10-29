import QECD1.T2Exist3

/-!
# The λ-trick on a 3D T2 skeleton (weight domination)

The 3D analogue of the 2D `TwoD/T2Trick`. The weight of a skeleton is the weight of its bottom route word
(`route3.wt 1`) times the transfer weight of its tail (`tailW` of `t2TD`, per-family factor `C3 = e^{30 λ} ε*`). In
closed form (`route3_wt_eq`, `tailW_eq3`) it is `ε*^{|counted|} e^{λ X + s Δy}`, where
`X = rlen ms0 + ssum + 30 m + rlen mst - jsum` and `Δy` is the rise from the bottom block to the end of the top part.
For a valid skeleton the metric constraint gives `X ≥ -cE`, and the heights give `Δy ≥ n_y - H0` with
`H0 = 2 h_s + A1 + 1 = 47`. Hence (`skel_trick3`)

  `ε*^{|counted|} ≤ wt(ms0) · tailW · e^{λ cE} · e^{-s (n_y - 47)}`.
-/

open Finset Classical

namespace QECD1

/-- The weight of a route word in closed form: `ε*` per token, `e^{λ |v|₁ + s v_y}` per step and link. -/
theorem route3_wt_eq : ∀ (q : ℕ) (b : V3) (ms : List Tok), Tok.mark ∉ ms →
    route3.wt q ms = eps ^ ms.length * Real.exp (lam * (rlen ms : ℝ) + sT * (((endOf b ms).2.2 : ℝ) - (b.2.2 : ℝ)))
  | q, b, [], _ => by
    simp [WA.wt, route3, rlen, endOf]
  | q, b, .step v :: ms, hm => by
    have ih := route3_wt_eq (rNext q (.step v)) (b + v) ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show tokW 0 (.step v) * route3.wt (rNext q (.step v)) ms = _
    rw [ih]
    simp only [tokW, tw, List.length_cons, rlen, endOf, Prod.snd_add, Int.cast_add, Nat.cast_add]
    have hx : lam * ((l1 v : ℝ) + (rlen ms : ℝ)) + sT * (((endOf (b + v) ms).2.2 : ℝ) - (b.2.2 : ℝ)) =
        (lam * (l1 v : ℝ) + sT * (v.2.2 : ℝ)) +
          (lam * (rlen ms : ℝ) + sT * (((endOf (b + v) ms).2.2 : ℝ) - ((b.2.2 : ℝ) + (v.2.2 : ℝ)))) := by ring
    rw [hx, Real.exp_add (lam * (l1 v : ℝ) + sT * (v.2.2 : ℝ)), pow_succ]
    ring
  | q, b, .link v :: ms, hm => by
    have ih := route3_wt_eq (rNext q (.link v)) (b + v) ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show tokW 0 (.link v) * route3.wt (rNext q (.link v)) ms = _
    rw [ih]
    simp only [tokW, tw, List.length_cons, rlen, endOf, Prod.snd_add, Int.cast_add, Nat.cast_add]
    have hx : lam * ((l1 v : ℝ) + (rlen ms : ℝ)) + sT * (((endOf (b + v) ms).2.2 : ℝ) - (b.2.2 : ℝ)) =
        (lam * (l1 v : ℝ) + sT * (v.2.2 : ℝ)) +
          (lam * (rlen ms : ℝ) + sT * (((endOf (b + v) ms).2.2 : ℝ) - ((b.2.2 : ℝ) + (v.2.2 : ℝ)))) := by ring
    rw [hx, Real.exp_add (lam * (l1 v : ℝ) + sT * (v.2.2 : ℝ)), pow_succ]
    ring
  | q, b, .leaf v :: ms, hm => by
    have ih := route3_wt_eq (rNext q (.leaf v)) b ms (fun hh => hm (List.mem_cons_of_mem _ hh))
    show tokW 0 (.leaf v) * route3.wt (rNext q (.leaf v)) ms = _
    rw [ih]
    simp only [tokW, List.length_cons, rlen, endOf]
    rw [pow_succ]
    ring
  | q, b, .mark :: ms, hm => absurd List.mem_cons_self hm

/-- The exponent of a tail after the cover `c`. -/
noncomputable def tailExp3 (c : V3) (fams : List (V3 × Skel3)) (top : Top3) : ℝ :=
  lam * (30 * (fams.length : ℝ) + (ssum3 fams : ℝ) + (rlen top.2.1 : ℝ) - (jsum3 c fams top.1 : ℝ)) +
    sT * (((endOf top.1 top.2.1).2.2 : ℝ) - (c.2.2 : ℝ))

/-- The number of `ε*` factors of a tail: per family its key length, and the top root and top route. -/
def tailLen3 (fams : List (V3 × Skel3)) (top : Top3) : ℕ :=
  (fams.map (fun f => 1 + (f.2.2.2.1.length + witLen f.2.2.2.2.1 + f.2.2.2.2.2.length))).sum +
    (if top.2.2 then 1 + top.2.1.length else 0)

/-- **The tail weight in closed form.** -/
theorem tailW_eq3 (Y : ℤ) (top : Top3) (htf : top.2.2 = false → top.2.1 = []) (hm : Tok.mark ∉ top.2.1) :
    ∀ (fams : List (V3 × Skel3)) (c : V3), (∀ f ∈ fams, f.2.1 = f.1) →
      (t2TD Y).tailW C3 c fams top = eps ^ tailLen3 fams top * Real.exp (tailExp3 c fams top)
  | [], c, _ => by
    obtain ⟨et, mst, tf⟩ := top
    cases tf with
    | false =>
      have hmst : mst = [] := htf rfl
      subst hmst
      have hE : tailExp3 c [] (et, [], false) = -lam * (l1 (et - c) : ℝ) + sT * ((et - c).2.2 : ℝ) := by
        unfold tailExp3
        simp only [List.length_nil, Nat.cast_zero, ssum3, jsum3, rlen, endOf, Prod.snd_sub, Int.cast_sub]
        ring
      have hL : tailLen3 [] (et, [], false) = 0 := by simp [tailLen3]
      show jw3 c et = _
      rw [hE, hL, pow_zero, one_mul]
      rfl
    | true =>
      have hE : tailExp3 c [] (et, mst, true) = (-lam * (l1 (et - c) : ℝ) + sT * ((et - c).2.2 : ℝ)) +
          (lam * (rlen mst : ℝ) + sT * (((endOf et mst).2.2 : ℝ) - (et.2.2 : ℝ))) := by
        unfold tailExp3
        simp only [List.length_nil, Nat.cast_zero, ssum3, jsum3, Prod.snd_sub, Int.cast_sub]
        ring
      have hL : tailLen3 [] (et, mst, true) = 1 + mst.length := by simp [tailLen3]
      show eps * jw3 c et * route3.wt 1 mst = _
      rw [route3_wt_eq 1 et mst hm, hE, hL]
      unfold jw3
      rw [Real.exp_add (-lam * (l1 (et - c) : ℝ) + sT * ((et - c).2.2 : ℝ)), pow_add, pow_one]
      ring
  | f :: fs, c, hroot => by
    have ih := tailW_eq3 Y top htf hm fs (exitSk f.2) (fun g hg => hroot g (List.mem_cons_of_mem _ hg))
    have hr := hroot f List.mem_cons_self
    have hE : tailExp3 c (f :: fs) top = (-lam * (l1 (f.1 - c) : ℝ) + sT * ((f.1 - c).2.2 : ℝ)) + lam * 30 +
        (lam * (l1 (exitSk f.2 - f.1) : ℝ) + sT * ((exitSk f.2 - f.1).2.2 : ℝ)) + tailExp3 (exitSk f.2) fs top := by
      unfold tailExp3
      simp only [List.length_cons, ssum3, jsum3, Prod.snd_sub, Int.cast_sub]
      push_cast
      ring
    have hL : tailLen3 (f :: fs) top =
        (1 + (f.2.2.2.1.length + witLen f.2.2.2.2.1 + f.2.2.2.2.2.length)) + tailLen3 fs top := by
      unfold tailLen3
      simp only [List.map_cons, List.sum_cons]
      ring
    show jw3 c f.1 * C3 * skelW f.2 * (t2TD Y).tailW C3 (exitSk f.2) fs top = _
    rw [ih, hE, hL]
    have hexit : endOf f.2.1 (f.2.2.2.1 ++ f.2.2.2.2.2) = exitSk f.2 := rfl
    unfold jw3 C3 skelW
    rw [hexit, hr]
    simp only [Real.exp_add, pow_add, pow_one]
    ring

/-- From a valid tail: every family's skeleton is good and rooted at its landing root; the top route is empty unless
the top is a family, and then a word from `A`. -/
theorem tailOK_facts (Y : ℤ) (top : Top3) : ∀ (c : V3) (fams : List (V3 × Skel3)),
    (t2TD Y).TailOK c fams top →
      (∀ f ∈ fams, f.2.1 = f.1 ∧ SkelOK f.2) ∧ (top.2.2 = true → route3.Gram 1 top.2.1) ∧
        (top.2.2 = false → top.2.1 = [])
  | c, [], hok => by
    have h' : tok3 Y c top := hok
    unfold tok3 at h'
    refine ⟨fun f hf => absurd hf (by simp), fun ht => ?_, fun hf => ?_⟩
    · rw [if_pos ht] at h'
      exact h'.2
    · rw [if_neg (by simp [hf])] at h'
      exact h'.1
  | c, f :: fs, hok => by
    obtain ⟨-, hroot, hfok, hrest⟩ := hok
    obtain ⟨h1, h2, h3⟩ := tailOK_facts Y top (exitSk f.2) fs hrest
    refine ⟨fun g hg => ?_, h2, h3⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨hroot, hfok⟩
    · exact h1 g hg

theorem tailOKex_facts (Y : ℤ) (top : Top3) (c : V3) (fams : List (V3 × Skel3))
    (hok : (t2TD Y).TailOKex (tok3ex Y) c fams top) :
    (∀ f ∈ fams, f.2.1 = f.1 ∧ SkelOK f.2) ∧ (top.2.2 = true → route3.Gram 1 top.2.1) ∧
      (top.2.2 = false → top.2.1 = []) := by
  cases fams with
  | nil =>
    have h' : tok3ex Y c top := hok
    unfold tok3ex at h'
    refine ⟨fun f hf => absurd hf (by simp), fun ht => ?_, fun hf => ?_⟩
    · rw [if_pos ht] at h'
      exact h'
    · rw [if_neg (by simp [hf])] at h'
      exact h'.1
  | cons f fs =>
    obtain ⟨hroot, hfok, hrest⟩ := hok
    obtain ⟨h1, h2, h3⟩ := tailOK_facts Y top (exitSk f.2) fs hrest
    refine ⟨fun g hg => ?_, h2, h3⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨hroot, hfok⟩
    · exact h1 g hg

theorem eps_pos : 0 < eps := by
  unfold eps
  norm_num

/-- The counted blocks of a valid skeleton: one per `ε*` factor of its weight. -/
theorem counted_length3 (sk : T2Sk3) (hm0 : Tok.mark ∉ sk.ms0) (hmt : Tok.mark ∉ sk.top.2.1)
    (hfok : ∀ f ∈ sk.fams, SkelOK f.2) :
    sk.counted.length = sk.ms0.length + tailLen3 sk.fams sk.top := by
  unfold T2Sk3.counted tailLen3
  rw [List.length_append, List.length_append, List.length_flatMap, blocksOf_length _ _ hm0]
  have hmap : sk.fams.map (fun f => (keyBlocks f.1 f.2.2.2).length) =
      sk.fams.map (fun f => 1 + (f.2.2.2.1.length + witLen f.2.2.2.2.1 + f.2.2.2.2.2.length)) := by
    refine List.map_congr_left fun f hf => ?_
    rw [keyBlocks_length f.2.2.1 f.1 (hfok f hf).1]
    ring
  rw [hmap]
  split_ifs with htf
  · rw [List.length_cons, blocksOf_length _ _ hmt]
    ring
  · simp

/-- **The λ-trick and the height tilt on a valid 3D T2 skeleton.** -/
theorem skel_trick3 {ny : ℕ} {cE : ℝ} (sk : T2Sk3) (hok : sk.OK ny cE) :
    eps ^ sk.counted.length ≤ route3.wt 1 sk.ms0 *
      (t2TD ((ny : ℤ) - 1)).tailW C3 (endOf sk.b0 sk.ms0) sk.fams sk.top *
      Real.exp (lam * cE) * Real.exp (-sT * ((ny : ℝ) - 47)) := by
  obtain ⟨hb0, hg0, htail, hht, hmet, -, -⟩ := hok
  obtain ⟨hfams, htopg, htopf⟩ := tailOKex_facts _ _ _ _ htail
  have hm0 : Tok.mark ∉ sk.ms0 := mark_notMem_of_route3 _ _ hg0
  have hmt : Tok.mark ∉ sk.top.2.1 := by
    by_cases htf : sk.top.2.2 = true
    · exact mark_notMem_of_route3 _ _ (htopg htf)
    · rw [htopf (by simpa using htf)]
      exact List.not_mem_nil
  rw [counted_length3 sk hm0 hmt (fun f hf => (hfams f hf).2), route3_wt_eq 1 sk.b0 sk.ms0 hm0,
    tailW_eq3 _ sk.top htopf hmt sk.fams _ (fun f hf => (hfams f hf).1), pow_add]
  have hpos : 0 ≤ eps ^ sk.ms0.length * eps ^ tailLen3 sk.fams sk.top := by
    have := eps_pos
    positivity
  have hlam : (0 : ℝ) ≤ lam := by
    unfold lam
    norm_num
  have hsT : (0 : ℝ) ≤ sT := by
    unfold sT
    norm_num
  rw [hs3_val, Const.A1_val] at hht
  rw [hs3_val] at hb0
  have hht' : ((ny : ℤ) : ℝ) ≤ ((endOf sk.top.1 sk.top.2.1).2.2 : ℝ) + 1 + 11 + 24 := by exact_mod_cast hht
  have hb0' : (sk.b0.2.2 : ℝ) ≤ 11 := by exact_mod_cast hb0
  have h1 : 0 ≤ (rlen sk.ms0 : ℝ) + (30 * (sk.fams.length : ℝ) + (ssum3 sk.fams : ℝ) + (rlen sk.top.2.1 : ℝ) -
      (jsum3 (endOf sk.b0 sk.ms0) sk.fams sk.top.1 : ℝ)) + cE := by linarith
  have h2 : 0 ≤ ((endOf sk.top.1 sk.top.2.1).2.2 : ℝ) - (sk.b0.2.2 : ℝ) - ((ny : ℝ) - 47) := by
    push_cast at hht'
    linarith
  have hexp : 0 ≤ (lam * (rlen sk.ms0 : ℝ) + sT * (((endOf sk.b0 sk.ms0).2.2 : ℝ) - (sk.b0.2.2 : ℝ))) +
      tailExp3 (endOf sk.b0 sk.ms0) sk.fams sk.top + lam * cE + -sT * ((ny : ℝ) - 47) := by
    unfold tailExp3
    nlinarith [mul_nonneg hlam h1, mul_nonneg hsT h2]
  calc eps ^ sk.ms0.length * eps ^ tailLen3 sk.fams sk.top
      = eps ^ sk.ms0.length * eps ^ tailLen3 sk.fams sk.top * 1 := (mul_one _).symm
    _ ≤ eps ^ sk.ms0.length * eps ^ tailLen3 sk.fams sk.top *
        Real.exp ((lam * (rlen sk.ms0 : ℝ) + sT * (((endOf sk.b0 sk.ms0).2.2 : ℝ) - (sk.b0.2.2 : ℝ))) +
          tailExp3 (endOf sk.b0 sk.ms0) sk.fams sk.top + lam * cE + -sT * ((ny : ℝ) - 47)) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp hexp) hpos
    _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
        ring

end QECD1
