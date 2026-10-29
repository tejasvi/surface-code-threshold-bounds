import QECD1.Witness
import QECD1.RatioS

/-!
# Family keys of one axis: route words with the witness branch

A key of axis `i` is a triple `(r1, w, r2)`:

* `r1`, the route word from the landing root up to the mark (no mark in it);
* `w`, the witness (`Wit`): an on-route walk, or an off-route walk with a link and an excursion word;
* `r2`, the route word after the mark, read from the marked copy of the state where `r1` ends.

`keyWt` multiplies the token weights of `r1`, the witness weight and the weight of `r2`; it is the family word weight
with the mark weight `markW` replaced by the actual witness weight. `keys_le`: every finite set of valid keys
weighs at most the certificate value `F0_i` of the axis (`keysT_le`, `keysX_le`, `keysY_le`). The proof groups the
keys by their route words, bounds each group's witnesses by `markW` (`wit_sum_le`), and uses that
`(r1, r2) ↦ r1 ++ mark :: r2` is injective when `r1` has no mark (`split_mark_inj`).
-/

namespace QECD1

open QECD1.Tab QECD1.Bld

namespace WA

variable {σ τ : Type} (M : WA σ τ)

/-- The product of the token weights along a word. -/
noncomputable def wtPre : σ → List τ → ℝ
  | _, [] => 1
  | q, t :: ts => M.g q t * wtPre (M.next q t) ts

/-- The state after a word. -/
def stAfter : σ → List τ → σ
  | q, [] => q
  | q, t :: ts => stAfter (M.next q t) ts

theorem wt_append : ∀ (q : σ) (r1 r2 : List τ), M.wt q (r1 ++ r2) = M.wtPre q r1 * M.wt (M.stAfter q r1) r2
  | q, [], r2 => by simp [wtPre, stAfter]
  | q, t :: ts, r2 => by
    simp only [List.cons_append, wt, wtPre, stAfter]
    rw [wt_append]
    ring

theorem gram_append : ∀ (q : σ) (r1 r2 : List τ),
    M.Gram q (r1 ++ r2) ↔ M.Gram q r1 ∧ M.Gram (M.stAfter q r1) r2
  | q, [], r2 => by simp [Gram, stAfter]
  | q, t :: ts, r2 => by
    simp only [List.cons_append, Gram, stAfter]
    rw [gram_append]
    tauto

theorem wtPre_nonneg (hg : ∀ q t, 0 ≤ M.g q t) : ∀ (q : σ) (r : List τ), 0 ≤ M.wtPre q r
  | _, [] => zero_le_one
  | q, t :: ts => mul_nonneg (hg q t) (wtPre_nonneg hg _ ts)

end WA

/-! ### Witnesses -/

/-- A witness: an on-route walk, or an off-route walk with a link and an excursion word. -/
abbrev Wit := List V3 ⊕ (List V3 × V3 × List Tok)

noncomputable instance : DecidableEq Wit := Classical.decEq _

/-- Valid witnesses of axis `i`. -/
def witValid (i : Fin 3) : Wit → Prop
  | .inl w => ∀ v ∈ w, v ∈ S0
  | .inr x => (∀ v ∈ x.1, v ∈ S0) ∧ x.2.1 ∈ S1off ∧ (exc3 i).Gram 0 x.2.2

/-- The witness weight from route state `m`: the witness condition on-route, all walks at `Asp`. -/
noncomputable def witW (i : Fin 3) (m : ℕ) : Wit → ℝ
  | .inl w => if m = 34 then eps ^ w.length else witWt i (zOf m) w
  | .inr x => offWt i x

/-- **The witnesses of a route state weigh at most its mark weight.** -/
theorem wit_sum_le (i : Fin 3) (m : ℕ) (W : Finset Wit) (hW : ∀ w ∈ W, witValid i w) :
    ∑ w ∈ W, witW i m w ≤ markW m := by
  rw [← Finset.toLeft_disjSum_toRight (u := W), Finset.sum_disjSum]
  have hL : ∀ w ∈ W.toLeft, ∀ v ∈ w, v ∈ S0 := fun w hw => hW (.inl w) (Finset.mem_toLeft.1 hw)
  have hR : ∀ x ∈ W.toRight, (∀ v ∈ x.1, v ∈ S0) ∧ x.2.1 ∈ S1off ∧ (exc3 i).Gram 0 x.2.2 :=
    fun x hx => hW (.inr x) (Finset.mem_toRight.1 hx)
  have h := witness_le i m W.toLeft hL W.toRight hR
  have hl : ∑ w ∈ W.toLeft, witW i m (.inl w) =
      if m = 34 then ∑ w ∈ W.toLeft, eps ^ w.length else ∑ w ∈ W.toLeft, witWt i (zOf m) w := by
    simp only [witW]
    split_ifs <;> rfl
  have hr : ∑ x ∈ W.toRight, witW i m (.inr x) = ∑ x ∈ W.toRight, offWt i x := rfl
  rw [hl, hr]
  exact h

theorem witW_nonneg (i : Fin 3) (m : ℕ) (w : Wit) : 0 ≤ witW i m w := by
  cases w with
  | inl w =>
    simp only [witW]
    split_ifs
    · exact pow_nonneg eps_nonneg _
    · unfold witWt
      refine mul_nonneg (pow_nonneg eps_nonneg _) ?_
      split_ifs <;> norm_num
  | inr x =>
    simp only [witW, offWt]
    refine mul_nonneg (pow_nonneg eps_nonneg _) (mul_nonneg eps_nonneg ?_)
    exact (exc3 i).wt_nonneg (fun _ _ => eps_nonneg) (exc3_e_nonneg i) 0 _

/-! ### Keys -/

/-- A family key of axis `i`. -/
abbrev Key := List Tok × Wit × List Tok

/-- Valid keys: `r1` allowed from the landing root and without a mark, a valid witness, `r2` allowed from the marked
copy of the state after `r1`. -/
def KeyOK (i : Fin 3) (k : Key) : Prop :=
  (fam3 i).Gram 0 k.1 ∧ Tok.mark ∉ k.1 ∧ witValid i k.2.1 ∧
    (fam3 i).Gram ((fam3 i).stAfter 0 k.1 + 52) k.2.2

/-- The weight of a key. -/
noncomputable def keyWt (i : Fin 3) (k : Key) : ℝ :=
  (fam3 i).wtPre 0 k.1 * witW i ((fam3 i).stAfter 0 k.1) k.2.1 *
    (fam3 i).wt ((fam3 i).stAfter 0 k.1 + 52) k.2.2

theorem split_mark_inj : ∀ (r1 r1' r2 r2' : List Tok), Tok.mark ∉ r1 → Tok.mark ∉ r1' →
    r1 ++ Tok.mark :: r2 = r1' ++ Tok.mark :: r2' → r1 = r1' ∧ r2 = r2'
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], b :: s', _, _, _, h1', h => by
    exfalso
    have := (List.cons.inj h).1
    exact h1' (this ▸ List.mem_cons_self ..)
  | a :: s, [], _, _, h1, _, h => by
    exfalso
    have := (List.cons.inj h).1
    exact h1 (this ▸ List.mem_cons_self ..)
  | a :: s, b :: s', r2, r2', h1, h1', h => by
    obtain ⟨hab, hrest⟩ := List.cons.inj h
    have ih := split_mark_inj s s' r2 r2' (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h1' (List.mem_cons_of_mem _ hm)) hrest
    exact ⟨by rw [hab, ih.1], ih.2⟩

/-- Route words without a mark stay in the states before the mark. -/
theorem stAfter_lt (i : Fin 3) : ∀ (n : ℕ) (r : List Tok), n < 52 → (fam3 i).Gram n r → Tok.mark ∉ r →
    (fam3 i).stAfter n r < 52
  | n, [], hn, _, _ => hn
  | n, t :: ts, hn, hg, hm => by
    have htm : t ≠ Tok.mark := fun h => hm (h ▸ List.mem_cons_self ..)
    have ht : t ∈ routeToks n := by
      have h := hg.1
      change t ∈ famToks n at h
      unfold famToks at h
      rw [if_pos hn] at h
      exact (Finset.mem_insert.1 h).resolve_left htm
    have hnext : (fam3 i).next n t = routeNext i n t := by
      show famNext i n t = routeNext i n t
      unfold famNext
      rw [if_pos hn, if_neg htm]
    show (fam3 i).stAfter ((fam3 i).next n t) ts < 52
    exact stAfter_lt i _ ts (hnext ▸ routeNext_lt i n t ht) hg.2 (fun h => hm (List.mem_cons_of_mem _ h))

/-- The family word of a key, and its weight. -/
theorem wt_marked (i : Fin 3) (r1 r2 : List Tok) (hq : (fam3 i).stAfter 0 r1 < 52) :
    (fam3 i).wt 0 (r1 ++ Tok.mark :: r2) =
      (fam3 i).wtPre 0 r1 * markW ((fam3 i).stAfter 0 r1) * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := by
  rw [WA.wt_append]
  set q := (fam3 i).stAfter 0 r1
  have hnext : (fam3 i).next q Tok.mark = q + 52 := by
    show famNext i q Tok.mark = q + 52
    unfold famNext
    rw [if_pos hq, if_pos rfl]
  show (fam3 i).wtPre 0 r1 * ((fam3 i).g q Tok.mark * (fam3 i).wt ((fam3 i).next q Tok.mark) r2) = _
  rw [hnext]
  show (fam3 i).wtPre 0 r1 * (markW q * (fam3 i).wt (q + 52) r2) = _
  ring

theorem gram_marked (i : Fin 3) (r1 r2 : List Tok) (hq : (fam3 i).stAfter 0 r1 < 52)
    (h1 : (fam3 i).Gram 0 r1) (h2 : (fam3 i).Gram ((fam3 i).stAfter 0 r1 + 52) r2) :
    (fam3 i).Gram 0 (r1 ++ Tok.mark :: r2) := by
  rw [WA.gram_append]
  refine ⟨h1, ?_, ?_⟩
  · show Tok.mark ∈ famToks ((fam3 i).stAfter 0 r1)
    unfold famToks
    rw [if_pos hq]
    exact Finset.mem_insert_self _ _
  · have hnext : (fam3 i).next ((fam3 i).stAfter 0 r1) Tok.mark = (fam3 i).stAfter 0 r1 + 52 := by
      show famNext i _ Tok.mark = _
      unfold famNext
      rw [if_pos hq, if_pos rfl]
    rw [hnext]
    exact h2

/-- **Family keys of axis `i`** weigh at most the certificate value. -/
theorem keys_le (i : Fin 3) (st fB : ℕ → ℕ) (hst : ∀ j < 17, stepQ i j ≤ (st j : ℚ) / Qden)
    (hchk : checkN 104 (famMoves st lf linkT mkT) (famE Qden) Qden fB = true) (K : Finset Key)
    (hK : ∀ k ∈ K, KeyOK i k) : ∑ k ∈ K, keyWt i k ≤ (fB 0 : ℝ) / Qden := by
  set P := K.image fun k : Key => (k.1, k.2.2)
  have hq : ∀ k ∈ K, (fam3 i).stAfter 0 k.1 < 52 := fun k hk =>
    stAfter_lt i 0 k.1 (by norm_num) (hK k hk).1 (hK k hk).2.1
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k : Key => (k.1, k.2.2)) (t := P)
    (fun k hk => Finset.mem_image_of_mem _ hk)]
  -- each group of keys with the same route words
  have hgroup : ∀ p ∈ P, ∑ k ∈ K with (k.1, k.2.2) = p, keyWt i k ≤ (fam3 i).wt 0 (p.1 ++ Tok.mark :: p.2) := by
    intro p hp
    obtain ⟨k0, hk0, hk0p⟩ := Finset.mem_image.1 hp
    have hq0 : (fam3 i).stAfter 0 p.1 < 52 := by rw [← hk0p]; exact hq k0 hk0
    set F := K.filter fun k : Key => (k.1, k.2.2) = p
    have hF : ∀ k ∈ F, k.1 = p.1 ∧ k.2.2 = p.2 := by
      intro k hk
      have h := (Finset.mem_filter.1 hk).2
      rw [← h]
      exact ⟨rfl, rfl⟩
    have hsum : ∑ k ∈ F, keyWt i k =
        (fam3 i).wtPre 0 p.1 * (∑ w ∈ F.image fun k : Key => k.2.1, witW i ((fam3 i).stAfter 0 p.1) w) *
          (fam3 i).wt ((fam3 i).stAfter 0 p.1 + 52) p.2 := by
      have hinj : Set.InjOn (fun k : Key => k.2.1) (F : Set Key) := by
        intro k hk k' hk' h
        obtain ⟨a1, a2⟩ := hF k hk
        obtain ⟨b1, b2⟩ := hF k' hk'
        exact Prod.ext (a1.trans b1.symm) (Prod.ext h (a2.trans b2.symm))
      rw [Finset.sum_image hinj, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      obtain ⟨a1, a2⟩ := hF k hk
      unfold keyWt
      rw [a1, a2]
    have hwit : ∑ w ∈ F.image (fun k : Key => k.2.1), witW i ((fam3 i).stAfter 0 p.1) w ≤
        markW ((fam3 i).stAfter 0 p.1) := by
      refine wit_sum_le i _ _ fun w hw => ?_
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
      exact (hK k (Finset.mem_filter.1 hk).1).2.2.1
    have hpre := (fam3 i).wtPre_nonneg (fun n t => tokW_nonneg n t) 0 p.1
    have hpost := (fam3 i).wt_nonneg (fun n t => tokW_nonneg n t) famEnd_nonneg ((fam3 i).stAfter 0 p.1 + 52) p.2
    rw [hsum, wt_marked i p.1 p.2 hq0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwit hpre) hpost
  refine le_trans (Finset.sum_le_sum hgroup) ?_
  -- the family words of the groups are distinct and allowed
  have hinj : Set.InjOn (fun p : List Tok × List Tok => p.1 ++ Tok.mark :: p.2) (P : Set (List Tok × List Tok)) := by
    intro p hp p' hp' h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hp'
    have := split_mark_inj k.1 k'.1 k.2.2 k'.2.2 (hK k hk).2.1 (hK k' hk').2.1 h
    exact Prod.ext this.1 this.2
  rw [← Finset.sum_image hinj]
  refine fam3_words_le i st fB hst hchk _ fun r hr => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
  exact gram_marked i k.1 k.2.2 (hq k hk) (hK k hk).1 (hK k hk).2.2.2

theorem keysT_le (K : Finset Key) (hK : ∀ k ∈ K, KeyOK 0 k) :
    ∑ k ∈ K, keyWt 0 k ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := keys_le 0 stT fBT stepQ_le_T famT_ok K hK
  rw [fBT0, Qden_cast] at h
  exact_mod_cast h

theorem keysX_le (K : Finset Key) (hK : ∀ k ∈ K, KeyOK 1 k) :
    ∑ k ∈ K, keyWt 1 k ≤ (2734104547231 : ℝ) / 10 ^ 15 := by
  have h := keys_le 1 stT fBT stepQ_le_X famT_ok K hK
  rw [fBT0, Qden_cast] at h
  exact_mod_cast h

theorem keysY_le (K : Finset Key) (hK : ∀ k ∈ K, KeyOK 2 k) :
    ∑ k ∈ K, keyWt 2 k ≤ (2741437430948 : ℝ) / 10 ^ 15 := by
  have h := keys_le 2 stY fBY stepQ_le_Y famY_ok K hK
  rw [fBY0, Qden_cast] at h
  exact_mod_cast h

/-- **Keys of the three axes**: the union bound's three family sums total at most `F0s = 2 F0t + F0y`, and with the
tilted landing sum the transfer ratio is at most 0.9. -/
theorem keys_ratio_le (S : Finset V3) (hS : ∀ v ∈ S, Const.J ≤ linf v) (K0 K1 K2 : Finset Key)
    (h0 : ∀ k ∈ K0, KeyOK 0 k) (h1 : ∀ k ∈ K1, KeyOK 1 k) (h2 : ∀ k ∈ K2, KeyOK 2 k) :
    (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) * eps *
      (∑ k ∈ K0, keyWt 0 k + ∑ k ∈ K1, keyWt 1 k + ∑ k ∈ K2, keyWt 2 k) ≤ 9 / 10 := by
  have hJ := landing_tilt_le S fun v hv => by
    have h := hS v hv
    rw [Const.J_val] at h
    exact h
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := by
    exact exp_offT_le
  have hK : ∑ k ∈ K0, keyWt 0 k + ∑ k ∈ K1, keyWt 1 k + ∑ k ∈ K2, keyWt 2 k ≤ F0s := by
    unfold F0s
    linarith [keysT_le K0 h0, keysX_le K1 h1, keysY_le K2 h2]
  have hnn : ∀ (j : Fin 3) (k : Key), 0 ≤ keyWt j k := fun j k =>
    mul_nonneg (mul_nonneg ((fam3 j).wtPre_nonneg (fun n t => tokW_nonneg n t) 0 k.1) (witW_nonneg j _ _))
      ((fam3 j).wt_nonneg (fun n t => tokW_nonneg n t) famEnd_nonneg _ _)
  have hK0 : 0 ≤ ∑ k ∈ K0, keyWt 0 k + ∑ k ∈ K1, keyWt 1 k + ∑ k ∈ K2, keyWt 2 k := by
    have a := Finset.sum_nonneg fun k (_ : k ∈ K0) => hnn 0 k
    have b := Finset.sum_nonneg fun k (_ : k ∈ K1) => hnn 1 k
    have c := Finset.sum_nonneg fun k (_ : k ∈ K2) => hnn 2 k
    linarith
  have hs0 : 0 ≤ ∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have he0 : (0 : ℝ) ≤ eps := eps_nonneg
  have hm1 : (∑ v ∈ S, Real.exp (-lam * l1 v + sT * v.2.2)) * Real.exp (lam * 30) ≤ Jbar2 * (eoffUpT : ℝ) :=
    mul_le_mul hJ hE (Real.exp_pos _).le (le_trans hs0 hJ)
  have hJ0 : 0 ≤ Jbar2 * (eoffUpT : ℝ) := le_trans (mul_nonneg hs0 (Real.exp_pos _).le) hm1
  have hm2 := mul_le_mul_of_nonneg_right hm1 he0
  have hm3 := mul_le_mul hm2 hK hK0 (mul_nonneg hJ0 he0)
  have h4 : Jbar2 * (eoffUpT : ℝ) * eps * F0s ≤ 9 / 10 := by
    have e : eps = 37 / 2000000 := rfl
    rw [e]
    exact ratio_s_num
  linarith

end QECD1
