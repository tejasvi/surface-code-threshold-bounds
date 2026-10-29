import QECD1.Main

/-!
# The T2 transfer over the families of a tail (abstract), and its 3D instance

The 2D `tail_transfer` (TwoD/T2Transfer) sums the weights of the tails entered from a cover: a tail is a list of
families, each entered by a jump from the previous exit cover to its landing root, then a top part. This module
states the transfer abstractly and instantiates it in 3D.

* `TData`: points `P`, family keys `FK` with landing root, exit cover, validity and weight, tops `Top` with validity
  and weight, and jump weights `jw c e` with validity `jok c e`.
* `TData.transfer`: suppose
  * every set of valid jumps from a point weighs at most `Jbd` (the landing bound);
  * every set of valid families from one landing root weighs at most `F0` (`FamB`);
  * every set of valid tops weighs at most `topB`;
  * `r = Jbd · C · F0 < 1`.

  Then every finite set of valid tails weighs at most `topB / (1 - r)`. Here `C` is the per-family factor
  `e^{λ off} ε`. The proof is that of 2D: induction over the tail length, grouping the tails by their first jump and
  family.
* 3D: the jump weight is `jw3 c e = e^{-λ |e - c|₁ + s (e - c)_y}`, valid for `|e - c|∞ ≥ J = 17` (`landing3` gives
  `Jbd = Jbar2`). The family bound comes from a per-root encoding (`Encoding3DRooted`, `famB3_rooted`), with
  `C = e^{30 λ} ε*`. `transfer3`: every finite set of valid 3D tails weighs at most `topB / (1 - r3)`, where
  `r3 ≤ 0.9`, so at most `10 topB`.
-/

namespace QECD1

/-- Abstract data of the T2 transfer. -/
structure TData (P FK Top : Type) where
  jw : P → P → ℝ
  jok : P → P → Prop
  root : FK → P
  exit : FK → P
  fok : FK → Prop
  fw : FK → ℝ
  tw : P → Top → ℝ
  tok : P → Top → Prop

namespace TData

variable {P FK Top : Type} (D : TData P FK Top)

/-- Valid tails from the exit cover `c`: jumps with families, then a top. -/
def TailOK : P → List (P × FK) → Top → Prop
  | c, [], t => D.tok c t
  | c, s :: ss, t => D.jok c s.1 ∧ D.root s.2 = s.1 ∧ D.fok s.2 ∧ TailOK (D.exit s.2) ss t

/-- The weight of a tail; `C` is the per-family factor. -/
noncomputable def tailW (C : ℝ) : P → List (P × FK) → Top → ℝ
  | c, [], t => D.tw c t
  | c, s :: ss, t => D.jw c s.1 * C * D.fw s.2 * tailW C (D.exit s.2) ss t

/-- The tails whose first step is `h`, with that step removed. -/
def restOf (S : Finset (List (P × FK) × Top)) (h : P × FK) [DecidableEq P] [DecidableEq FK] [DecidableEq Top] :
    Finset (List (P × FK) × Top) :=
  (S.filter fun x => x.1.head? = some h).image fun x => (x.1.tail, x.2)

/-- **The transfer.** -/
theorem transfer [DecidableEq P] [DecidableEq FK] [DecidableEq Top] (C Jbd F0 topB : ℝ) (hC : 0 ≤ C)
    (hJbd : 0 ≤ Jbd) (hF0 : 0 ≤ F0) (htopB : 0 ≤ topB)
    (hjw : ∀ c e, 0 ≤ D.jw c e) (hfw : ∀ k, 0 ≤ D.fw k) (htw : ∀ c t, 0 ≤ D.tw c t)
    (hJ : ∀ (c : P) (E : Finset P), (∀ e ∈ E, D.jok c e) → ∑ e ∈ E, D.jw c e ≤ Jbd)
    (hF : ∀ (e : P) (K : Finset FK), (∀ k ∈ K, D.root k = e ∧ D.fok k) → ∑ k ∈ K, D.fw k ≤ F0)
    (hT : ∀ (c : P) (T : Finset Top), (∀ t ∈ T, D.tok c t) → ∑ t ∈ T, D.tw c t ≤ topB)
    (hr : Jbd * C * F0 < 1) :
    ∀ (c : P) (S : Finset (List (P × FK) × Top)), (∀ x ∈ S, D.TailOK c x.1 x.2) →
      ∑ x ∈ S, D.tailW C c x.1 x.2 ≤ topB / (1 - Jbd * C * F0) := by
  set r := Jbd * C * F0
  have hr0 : 0 ≤ r := mul_nonneg (mul_nonneg hJbd hC) hF0
  have h1r : 0 < 1 - r := by linarith
  set B := topB / (1 - r)
  have hB0 : 0 ≤ B := div_nonneg htopB h1r.le
  have hBeq : topB + r * B = B := by
    have : B * (1 - r) = topB := div_mul_cancel₀ topB h1r.ne'
    linarith
  -- tails without families: their tops
  have htops : ∀ (c : P) (S : Finset (List (P × FK) × Top)), (∀ x ∈ S, D.TailOK c x.1 x.2 ∧ x.1 = []) →
      ∑ x ∈ S, D.tailW C c x.1 x.2 ≤ topB := by
    intro c S hS
    have hinj : Set.InjOn Prod.snd (S : Set (List (P × FK) × Top)) := by
      intro x hx y hy h
      exact Prod.ext ((hS x hx).2.trans (hS y hy).2.symm) h
    have heq : ∑ x ∈ S, D.tailW C c x.1 x.2 = ∑ t ∈ S.image Prod.snd, D.tw c t := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(hS x hx).2]
      rfl
    rw [heq]
    refine hT c _ fun t ht => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    have h := (hS x hx).1
    rw [(hS x hx).2] at h
    exact h
  -- induction over the tail length
  have key : ∀ (n : ℕ) (c : P) (S : Finset (List (P × FK) × Top)),
      (∀ x ∈ S, D.TailOK c x.1 x.2 ∧ x.1.length ≤ n) → ∑ x ∈ S, D.tailW C c x.1 x.2 ≤ B := by
    intro n
    induction n with
    | zero =>
      intro c S hS
      have h := htops c S fun x hx => ⟨(hS x hx).1, List.eq_nil_of_length_eq_zero (by have := (hS x hx).2; omega)⟩
      have : topB ≤ B := by
        rw [le_div_iff₀ h1r]
        nlinarith
      linarith
    | succ n ih =>
      intro c S hS
      rw [← Finset.sum_filter_add_sum_filter_not S (fun x => x.1 = [])]
      have hA := htops c (S.filter fun x => x.1 = []) fun x hx =>
        ⟨(hS x (Finset.mem_filter.1 hx).1).1, (Finset.mem_filter.1 hx).2⟩
      set S1 := S.filter fun x => ¬ x.1 = []
      -- the first steps of the tails with at least one family
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
      -- regroup the sum over the first step
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
      have hH : ∀ h ∈ H, D.jok c h.1 ∧ D.root h.2 = h.1 ∧ D.fok h.2 := by
        intro h hh
        obtain ⟨x, hx, hxh⟩ := Finset.mem_biUnion.1 hh
        have hok := (hS x (Finset.mem_filter.1 hx).1).1
        cases hx1 : x.1 with
        | nil => rw [hx1] at hxh; simp at hxh
        | cons a l =>
          rw [hx1] at hxh hok
          simp only [List.head?_cons, Option.mem_toFinset, Option.mem_def, Option.some.injEq] at hxh
          subst hxh
          exact ⟨hok.1, hok.2.1, hok.2.2.1⟩
      have hrest : ∀ h ∈ H, ∑ y ∈ restOf S1 h, D.tailW C (D.exit h.2) y.1 y.2 ≤ B := by
        intro h _
        refine ih (D.exit h.2) _ fun y hy => ?_
        unfold restOf at hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        obtain ⟨hxS1, hxh⟩ := Finset.mem_filter.1 hx
        obtain ⟨hok, hlen⟩ := hS x (Finset.mem_filter.1 hxS1).1
        cases hx1 : x.1 with
        | nil => rw [hx1] at hxh; simp at hxh
        | cons a l =>
          rw [hx1] at hxh hok hlen
          simp only [List.head?_cons, Option.some.injEq] at hxh
          subst hxh
          refine ⟨hok.2.2.2, ?_⟩
          simp only [List.length_cons] at hlen
          show l.length ≤ n
          omega
      have hgroup : ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * ∑ y ∈ restOf S1 h, D.tailW C (D.exit h.2) y.1 y.2 ≤
          ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * B :=
        Finset.sum_le_sum fun h hh =>
          mul_le_mul_of_nonneg_left (hrest h hh) (mul_nonneg (mul_nonneg (hjw _ _) hC) (hfw _))
      -- the first steps: jumps times families
      have hfirst : ∑ h ∈ H, D.jw c h.1 * C * D.fw h.2 * B ≤ Jbd * F0 * C * B := by
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
            obtain ⟨_, hroot, hfok⟩ := hH h hhH
            exact ⟨hroot.trans hhe, hfok⟩
          rw [h1]
          have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (hjw c e) hC) hB0)
          linarith
        refine le_trans (Finset.sum_le_sum hE) ?_
        rw [← Finset.sum_mul]
        have hJE : ∑ e ∈ E, D.jw c e ≤ Jbd := by
          refine hJ c E fun e he => ?_
          obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 he
          exact (hH h hh).1
        have := mul_le_mul_of_nonneg_right hJE (mul_nonneg (mul_nonneg hF0 hC) hB0)
        linarith
      have hrB : Jbd * F0 * C * B = r * B := by
        simp only [r]
        ring
      rw [hsum1] at *
      linarith
  intro c S hS
  exact key (S.sup fun x => x.1.length) c S fun x hx =>
    ⟨hS x hx, Finset.le_sup (f := fun x : List (P × FK) × Top => x.1.length) hx⟩

end TData

/-! ### The 3D instance -/

/-- The 3D jump weight from an exit cover `c` to a landing root `e`. -/
noncomputable def jw3 (c e : V3) : ℝ := Real.exp (-lam * l1 (e - c) + sT * (e - c).2.2)

/-- Valid 3D jumps: landing distance at least `J` (`Const.J`, `= 17` by `Const.J_val`; `landing_ge_J`). -/
def jok3 (c e : V3) : Prop := Const.J ≤ linf (e - c)

/-- **The 3D landing bound** from any exit cover. -/
theorem landing3 (c : V3) (E : Finset V3) (hE : ∀ e ∈ E, jok3 c e) : ∑ e ∈ E, jw3 c e ≤ Jbar2 := by
  have hinj : Set.InjOn (fun e : V3 => e - c) (E : Set V3) := fun e _ e' _ h => sub_left_injective h
  have h := landing_tilt_le (E.image fun e => e - c) fun v hv => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hv
    have h := hE e he
    unfold jok3 at h
    rw [Const.J_val] at h
    exact h
  rw [Finset.sum_image hinj] at h
  exact h

/-- **Named hypothesis, per landing root**: the family keys `FK` with their landing roots, validity and weights,
encoded per axis; the encoding is injective among valid keys with the same landing root. -/
structure Encoding3DRooted (FK : Type) where
  root : FK → V3
  fok : FK → Prop
  w : FK → ℝ
  ax : FK → Fin 3
  enc : FK → Key
  ok : ∀ k, fok k → KeyOK (ax k) (enc k)
  le : ∀ k, fok k → w k ≤ keyWt (ax k) (enc k)
  inj : ∀ k k', fok k → fok k' → root k = root k' → ax k = ax k' → enc k = enc k' → k = k'

/-- **`FamB3` per landing root.** -/
theorem famB3_rooted {FK : Type} (E : Encoding3DRooted FK) (e : V3) (K : Finset FK)
    (hK : ∀ k ∈ K, E.root k = e ∧ E.fok k) : ∑ k ∈ K, E.w k ≤ F0s := by
  classical
  let E' : Encoding3D {k : FK // k ∈ K} :=
    { w := fun k => E.w k.1
      ax := fun k => E.ax k.1
      enc := fun k => E.enc k.1
      ok := fun k => E.ok k.1 (hK k.1 k.2).2
      le := fun k => E.le k.1 (hK k.1 k.2).2
      inj := fun k k' hax henc => Subtype.ext (E.inj k.1 k'.1 (hK k.1 k.2).2 (hK k'.1 k'.2).2
        ((hK k.1 k.2).1.trans (hK k'.1 k'.2).1.symm) hax henc) }
  have h := famB3 E' Finset.univ
  have heq : ∑ k ∈ (Finset.univ : Finset {k : FK // k ∈ K}), E'.w k = ∑ k ∈ K, E.w k :=
    Finset.sum_coe_sort K (fun k => E.w k)
  linarith

/-- The 3D per-family factor `C = e^{30 λ} ε*`. -/
noncomputable def C3 : ℝ := Real.exp (lam * 30) * eps

theorem Jbar2_nonneg : 0 ≤ Jbar2 := by
  have h := landing_tilt_le ∅ fun v hv => absurd hv (Finset.notMem_empty v)
  simpa using h

theorem F0s_nonneg : 0 ≤ F0s := by
  unfold F0s
  norm_num

theorem r3_le : Jbar2 * C3 * F0s ≤ 9 / 10 := by
  have hE : Real.exp (lam * 30) ≤ (eoffUpT : ℝ) := by
    exact exp_offT_le
  have h := ratio_s_num
  have e : (37 / 2000000 : ℝ) = eps := rfl
  rw [e] at h
  unfold C3
  have h1 : Jbar2 * (Real.exp (lam * 30) * eps) * F0s ≤ Jbar2 * ((eoffUpT : ℝ) * eps) * F0s := by
    have := mul_le_mul_of_nonneg_right hE eps_nonneg
    have := mul_le_mul_of_nonneg_left this Jbar2_nonneg
    exact mul_le_mul_of_nonneg_right this F0s_nonneg
  have h2 : Jbar2 * ((eoffUpT : ℝ) * eps) * F0s = Jbar2 * (eoffUpT : ℝ) * eps * F0s := by ring
  linarith

/-- **The 3D transfer**: tails of families entered by jumps of landing distance at least 17, with the families
bounded through a per-root encoding and the tops by `topB`, weigh at most `topB / (1 - r3) ≤ 10 topB`. -/
theorem transfer3 {FK Top : Type} [DecidableEq FK] [DecidableEq Top] (E : Encoding3DRooted FK)
    (exitF : FK → V3) (tw : V3 → Top → ℝ) (tok : V3 → Top → Prop) (topB : ℝ) (htopB : 0 ≤ topB)
    (hw : ∀ k, 0 ≤ E.w k) (htw : ∀ c t, 0 ≤ tw c t)
    (hT : ∀ (c : V3) (T : Finset Top), (∀ t ∈ T, tok c t) → ∑ t ∈ T, tw c t ≤ topB)
    (c : V3) (S : Finset (List (V3 × FK) × Top))
    (hS : ∀ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).TailOK c x.1 x.2) :
    ∑ x ∈ S, (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).tailW C3 c x.1 x.2 ≤ 10 * topB := by
  have hC : 0 ≤ C3 := mul_nonneg (Real.exp_pos _).le eps_nonneg
  have hr := r3_le
  have h := (TData.mk jw3 jok3 E.root exitF E.fok E.w tw tok).transfer C3 Jbar2 F0s topB hC Jbar2_nonneg
    F0s_nonneg htopB (fun _ _ => (Real.exp_pos _).le) hw htw (fun c E hE => landing3 c E hE)
    (fun e K hK => famB3_rooted E e K hK) hT (by linarith) c S hS
  have h1 : 0 < 1 - Jbar2 * C3 * F0s := by linarith
  have h2 : topB / (1 - Jbar2 * C3 * F0s) ≤ 10 * topB := by
    rw [div_le_iff₀ h1]
    nlinarith
  linarith

end QECD1
