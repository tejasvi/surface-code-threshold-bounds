import QECML.TwoD.T2Sum

/-!
# The T2 summation: the transfer over the families of a skeleton

`tail_transfer`: for a finite set of valid tails (families, then a top part) entered from a cover, with `(R)` on every
jump, the tail weights sum to at most `topB false / (1 - r)`, `r = Jbd · e^{λ off} · ε · F0`, given the family bound
`FamB F0` (the weights of the families with a given landing root sum to at most `F0`). `tail_transfer_ex`: the same
when the first jump is exempt from `(R)`: `topB true + r1 · topB false / (1 - r)`, `r1 = JFbd · e^{λ off} · ε · F0`.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- A family key comes from a valid family with landing root `r0`. -/
def KeyOK (r0 : G.Block) (k : G.Block × List G.Block × G.Block) : Prop :=
  ∃ f : G.CRoute × G.Wit, famKey f = k ∧ f.1.r 0 = r0 ∧ f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
    f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1

/-- **The family bound** (to be supplied by the family factor): for every landing root, the family keys from it weigh
at most `F0` (without the landing root's `ε` and without the jump). -/
def FamB (G : S3Geom) (F0 : ℝ) : Prop :=
  ∀ (r0 : G.Block) (K : Finset (G.Block × List G.Block × G.Block)), (∀ k ∈ K, KeyOK r0 k) →
    ∑ k ∈ K, (5e-4 : ℝ) ^ (k.2.1.length - 1) *
      Real.exp (0.04305 * (bl1 r0 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (r0.2.val : ℝ))) ≤ F0

theorem CRoute.blocks_ne_nil (cr : G.CRoute) : cr.blocks ≠ [] := by
  unfold CRoute.blocks
  intro h
  have : cr.r 0 ∈ (List.range (cr.n + 1)).flatMap fun i => cr.r i :: (cr.a i ++ (cr.lf i).toList) :=
    List.mem_flatMap.2 ⟨0, List.mem_range.2 (Nat.succ_pos _), List.mem_cons_self⟩
  rw [h] at this
  simp at this

theorem KeyOK.len_pos {r0 : G.Block} {k : G.Block × List G.Block × G.Block} (h : KeyOK r0 k) : 1 ≤ k.2.1.length := by
  obtain ⟨f, rfl, -⟩ := h
  simp only [famKey, List.length_append]
  have := List.length_pos_of_ne_nil (CRoute.blocks_ne_nil f.1)
  omega

theorem KeyOK.root {r0 : G.Block} {k : G.Block × List G.Block × G.Block} (h : KeyOK r0 k) : k.1 = r0 := by
  obtain ⟨f, rfl, hr, -⟩ := h
  exact hr

/-- The validity of a tail entered from a cover (`ex`: the first jump is exempt from `(R)`). -/
def TailOK : Bool → G.Block → List (G.Block × List G.Block × G.Block) → G.Block → List G.Move → Bool → Prop
  | ex, c, [], et, mst, tf => TopOK ex c et mst tf
  | ex, c, k :: ks, et, mst, tf => (ex = false → 9 ≤ G.blockDist c k.1) ∧ KeyOK k.1 k ∧
      TailOK false k.2.2 ks et mst tf

/-- The weight of a family key splits into the jump, `e^{λ off}`, the landing root's `ε` and the family weight. -/
theorem wFamK_eq (c : G.Block) (k : G.Block × List G.Block × G.Block) (hk : 1 ≤ k.2.1.length) :
    wFamK 5e-4 0.041 0.04305 0.02 20.5 c k = jwt 0.041 0.02 c k.1 * Real.exp (0.041 * 20.5) * 5e-4 *
      ((5e-4 : ℝ) ^ (k.2.1.length - 1) *
        Real.exp (0.04305 * (bl1 k.1 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ)))) := by
  unfold wFamK jwt
  obtain ⟨n, hn⟩ : ∃ n, k.2.1.length = n + 1 := ⟨k.2.1.length - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel, pow_succ]
  rw [show (-0.041 * (bl1 c k.1 : ℝ) + 0.02 * ((k.1.2.val : ℝ) - (c.2.val : ℝ)) + 0.041 * 20.5 +
      0.04305 * (bl1 k.1 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ))) =
      (-0.041 * (bl1 c k.1 : ℝ) + 0.02 * ((k.1.2.val : ℝ) - (c.2.val : ℝ))) + 0.041 * 20.5 +
      (0.04305 * (bl1 k.1 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ))) by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **The family step of the transfer**: the head keys entered from `c` (each with its landing root), weighted by
`wFamK`, sum to at most `J · e^{λ off} · ε · F0`, `J = Jbd` with `(R)` on the jumps, `JFbd` without. -/
theorem heads_le {F0 : ℝ} (hF0 : 0 ≤ F0) (hFB : FamB G F0) (ex : Bool) (c : G.Block)
    (K : Finset (G.Block × List G.Block × G.Block))
    (hK : ∀ k ∈ K, (ex = false → 9 ≤ G.blockDist c k.1) ∧ KeyOK k.1 k) :
    ∑ k ∈ K, wFamK 5e-4 0.041 0.04305 0.02 20.5 c k ≤
      (if ex then JFbd else Jbd) * Real.exp (0.041 * 20.5) * 5e-4 * F0 := by
  rw [Finset.sum_congr rfl fun k hk => wFamK_eq c k (hK k hk).2.len_pos]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := K.image Prod.fst)
    (fun k hk => Finset.mem_image_of_mem _ hk)]
  have hfib : ∀ r0 ∈ K.image Prod.fst, ∑ k ∈ K with k.1 = r0, jwt 0.041 0.02 c k.1 * Real.exp (0.041 * 20.5) *
      5e-4 * ((5e-4 : ℝ) ^ (k.2.1.length - 1) *
        Real.exp (0.04305 * (bl1 k.1 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ)))) ≤
      jwt 0.041 0.02 c r0 * Real.exp (0.041 * 20.5) * 5e-4 * F0 := by
    intro r0 _
    have heq : ∀ k ∈ K.filter (fun k => k.1 = r0), jwt 0.041 0.02 c k.1 * Real.exp (0.041 * 20.5) * 5e-4 *
        ((5e-4 : ℝ) ^ (k.2.1.length - 1) *
          Real.exp (0.04305 * (bl1 k.1 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (k.1.2.val : ℝ)))) =
        jwt 0.041 0.02 c r0 * Real.exp (0.041 * 20.5) * 5e-4 * ((5e-4 : ℝ) ^ (k.2.1.length - 1) *
          Real.exp (0.04305 * (bl1 r0 k.2.2 : ℝ) + 0.02 * ((k.2.2.2.val : ℝ) - (r0.2.val : ℝ)))) := by
      intro k hk
      rw [(Finset.mem_filter.1 hk).2]
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    have hc : 0 ≤ jwt 0.041 0.02 c r0 * Real.exp (0.041 * 20.5) * 5e-4 :=
      mul_nonneg (mul_nonneg (jwt_nonneg _ _ _ _) (Real.exp_pos _).le) (by norm_num)
    refine mul_le_mul_of_nonneg_left (hFB r0 _ fun k hk => ?_) hc
    have h1 := (hK k (Finset.mem_filter.1 hk).1).2
    have h2 := (Finset.mem_filter.1 hk).2
    rw [h2] at h1
    exact h1
  calc _ ≤ ∑ r0 ∈ K.image Prod.fst, jwt 0.041 0.02 c r0 * Real.exp (0.041 * 20.5) * 5e-4 * F0 :=
        Finset.sum_le_sum hfib
    _ = (∑ r0 ∈ K.image Prod.fst, jwt 0.041 0.02 c r0) * (Real.exp (0.041 * 20.5) * 5e-4 * F0) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r0 _ => by ring
    _ ≤ (if ex then JFbd else Jbd) * (Real.exp (0.041 * 20.5) * 5e-4 * F0) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simp only [jwt_eq_jw]
        cases ex with
        | true => exact jump_full_le c _
        | false =>
          refine jump_le c _ fun r0 hr0 => ?_
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hr0
          exact (hK k hk).1 rfl
    _ = _ := by ring

/-! ### The transfer -/

/-- The tail of a skeleton as data: family keys, top root, top route, top flag. -/
abbrev TailD (G : S3Geom) := List (G.Block × List G.Block × G.Block) × G.Block × List G.Move × Bool

/-- The tails without families: their weight is the top weight. -/
theorem tails_nil_le (hD : G.D = 5) (ex : Bool) (c : G.Block) (T : Finset (TailD G))
    (hT : ∀ t ∈ T, t.1 = [] ∧ TailOK ex c t.1 t.2.1 t.2.2.1 t.2.2.2) :
    ∑ t ∈ T, tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ topB ex := by
  have hw : ∀ t ∈ T, tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 =
      wTop 5e-4 0.041 0.04305 0.02 c t.2.1 t.2.2.1 t.2.2.2 := by
    intro t ht
    rw [(hT t ht).1]
    rfl
  rw [Finset.sum_congr rfl hw]
  have hinj : Set.InjOn (fun t : TailD G => t.2) ((T : Finset _) : Set (TailD G)) := by
    intro t ht t' ht' h
    exact Prod.ext ((hT t ht).1.trans (hT t' ht').1.symm) h
  rw [← Finset.sum_image (f := fun u : G.Block × List G.Move × Bool =>
    wTop 5e-4 0.041 0.04305 0.02 c u.1 u.2.1 u.2.2) hinj]
  refine top_sum_le hD ex c _ fun u hu => ?_
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
  have h := (hT t ht).2
  rw [(hT t ht).1] at h
  exact h

/-- The tails with families, grouped by their first family key. -/
theorem tails_cons_le (c : G.Block) (T : Finset (TailD G)) (hT : ∀ t ∈ T, t.1 ≠ []) (B : ℝ)
    (hrest : ∀ k, ∀ U : Finset (TailD G), (∀ u ∈ U, (k :: u.1, u.2) ∈ T) →
      ∑ u ∈ U, tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2 ≤ B) :
    ∑ t ∈ T, tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 ≤
      (∑ k ∈ T.image (fun t => t.1.headD (c, [], c)), wFamK 5e-4 0.041 0.04305 0.02 20.5 c k) * B := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : TailD G => t.1.headD (c, [], c))
    (t := T.image (fun t => t.1.headD (c, [], c))) (fun t ht => Finset.mem_image_of_mem _ ht), Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  -- the fiber of `k`
  have hform : ∀ t ∈ T.filter (fun t => t.1.headD (c, [], c) = k), t = (k :: t.1.tail, t.2) := by
    intro t ht
    obtain ⟨htT, hk⟩ := Finset.mem_filter.1 ht
    obtain ⟨t1, t2⟩ := t
    cases t1 with
    | nil => exact absurd rfl (hT _ htT)
    | cons a l =>
      simp only [List.headD_cons] at hk
      subst hk
      rfl
  have hw : ∀ t ∈ T.filter (fun t => t.1.headD (c, [], c) = k),
      tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 =
      wFamK 5e-4 0.041 0.04305 0.02 20.5 c k *
        tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.2 t.1.tail t.2.1 t.2.2.1 t.2.2.2 := by
    intro t ht
    conv_lhs => rw [hform t ht]
    rfl
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun t : TailD G => ((t.1.tail, t.2) : TailD G))
      ((T.filter (fun t => t.1.headD (c, [], c) = k) : Finset _) : Set (TailD G)) := by
    intro t ht t' ht' h
    rw [hform t ht, hform t' ht']
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  rw [← Finset.sum_image (f := fun u : TailD G =>
    tailWK 5e-4 0.041 0.04305 0.02 20.5 k.2.2 u.1 u.2.1 u.2.2.1 u.2.2.2) hinj]
  have hwk : 0 ≤ wFamK 5e-4 0.041 0.04305 0.02 20.5 c k := by
    unfold wFamK
    exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left (hrest k _ fun u hu => ?_) hwk
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
  rw [← hform t ht]
  exact (Finset.mem_filter.1 ht).1

/-- **The transfer** (all jumps with `(R)`): for every `B ≥ 0` with `topB false + r B ≤ B`, the weights of any finite
set of valid tails entered from a cover sum to at most `B`. -/
theorem tail_transfer (hD : G.D = 5) {F0 r B : ℝ} (hF0 : 0 ≤ F0) (hFB : FamB G F0)
    (hr : Jbd * Real.exp (0.041 * 20.5) * 5e-4 * F0 ≤ r) (hB0 : 0 ≤ B) (hB : topB false + r * B ≤ B) :
    ∀ (n : ℕ) (c : G.Block) (T : Finset (TailD G)),
      (∀ t ∈ T, t.1.length ≤ n ∧ TailOK false c t.1 t.2.1 t.2.2.1 t.2.2.2) →
      ∑ t ∈ T, tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ B := by
  intro n
  induction n with
  | zero =>
    intro c T hT
    have h := tails_nil_le hD false c T fun t ht => ⟨List.eq_nil_of_length_eq_zero (by have := (hT t ht).1; omega),
      (hT t ht).2⟩
    have hrB : 0 ≤ r * B := by
      have : 0 ≤ Jbd * Real.exp (0.041 * 20.5) * 5e-4 * F0 :=
        mul_nonneg (mul_nonneg (mul_nonneg Jbd_nonneg (Real.exp_pos _).le) (by norm_num)) hF0
      exact mul_nonneg (this.trans hr) hB0
    linarith
  | succ n ih =>
    intro c T hT
    rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.1 = [])]
    have h0 := tails_nil_le hD false c (T.filter (fun t => t.1 = [])) fun t ht =>
      ⟨(Finset.mem_filter.1 ht).2, (hT t (Finset.mem_filter.1 ht).1).2⟩
    have h1 := tails_cons_le c (T.filter (fun t => ¬ t.1 = [])) (fun t ht => (Finset.mem_filter.1 ht).2) B
      (fun k U hU => ih k.2.2 U fun u hu => by
        have hmem := hU u hu
        obtain ⟨hlen, hok⟩ := hT _ (Finset.mem_filter.1 hmem).1
        simp only [List.length_cons] at hlen
        exact ⟨by omega, hok.2.2⟩)
    have hheads := heads_le hF0 hFB false c ((T.filter (fun t => ¬ t.1 = [])).image
      (fun t => t.1.headD (c, [], c))) (fun k hk => by
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hk
        obtain ⟨htT, hne⟩ := Finset.mem_filter.1 ht
        obtain ⟨-, hok⟩ := hT t htT
        obtain ⟨t1, t2⟩ := t
        cases t1 with
        | nil => exact absurd rfl hne
        | cons a l =>
          rw [List.headD_cons]
          exact ⟨hok.1, hok.2.1⟩)
    simp only [Bool.false_eq_true, ↓reduceIte] at hheads
    have h2 := mul_le_mul_of_nonneg_right (hheads.trans hr) hB0
    linarith

/-- **The transfer with an exempt first jump**: `topB true + r1 · B`. -/
theorem tail_transfer_ex (hD : G.D = 5) {F0 r B r1 : ℝ} (hF0 : 0 ≤ F0) (hFB : FamB G F0)
    (hr : Jbd * Real.exp (0.041 * 20.5) * 5e-4 * F0 ≤ r) (hB0 : 0 ≤ B) (hB : topB false + r * B ≤ B)
    (hr1 : JFbd * Real.exp (0.041 * 20.5) * 5e-4 * F0 ≤ r1) (c : G.Block) (T : Finset (TailD G))
    (hT : ∀ t ∈ T, TailOK true c t.1 t.2.1 t.2.2.1 t.2.2.2) :
    ∑ t ∈ T, tailWK 5e-4 0.041 0.04305 0.02 20.5 c t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ topB true + r1 * B := by
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.1 = [])]
  have h0 := tails_nil_le hD true c (T.filter (fun t => t.1 = [])) fun t ht =>
    ⟨(Finset.mem_filter.1 ht).2, hT t (Finset.mem_filter.1 ht).1⟩
  have h1 := tails_cons_le c (T.filter (fun t => ¬ t.1 = [])) (fun t ht => (Finset.mem_filter.1 ht).2) B
    (fun k U hU => tail_transfer hD hF0 hFB hr hB0 hB (U.sup fun u => u.1.length) k.2.2 U fun u hu => by
      have hmem := hU u hu
      have hok := hT _ (Finset.mem_filter.1 hmem).1
      exact ⟨Finset.le_sup (f := fun u : TailD G => u.1.length) hu, hok.2.2⟩)
  have hheads := heads_le hF0 hFB true c ((T.filter (fun t => ¬ t.1 = [])).image
    (fun t => t.1.headD (c, [], c))) (fun k hk => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hk
      obtain ⟨htT, hne⟩ := Finset.mem_filter.1 ht
      have hok := hT t htT
      obtain ⟨t1, t2⟩ := t
      cases t1 with
      | nil => exact absurd rfl hne
      | cons a l =>
        rw [List.headD_cons]
        exact ⟨hok.1, hok.2.1⟩)
  simp only [↓reduceIte] at hheads
  have h2 := mul_le_mul_of_nonneg_right (hheads.trans hr1) hB0
  linarith

end S3Geom

end QECML
