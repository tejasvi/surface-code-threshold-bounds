import QECML.TwoD.RouteCount

/-!
# Grammar words with general move weights (groundwork for the T2 generating function)

`RouteCount` bounds the weighted number of grammar words when each move carries `ε e^{s v_y}`. The T2 count
(the T2 summation) weights moves differently: `ε e^{λ κ |v|_1 + s v_y}` for steps and links (the exchange tilt and the
height tilt) and `ε` for leaves. Here the weight of a move from `cur` is any nonnegative `g cur m`, and `gwt g cur ms`
is the product along the word. The transfer bound (`GWsum_le`) is the fixed-point argument of `Wsum_le`.

* `sum_gwt_le`: any finite set of grammar words of length at most `N` has total weight at most `GWsum N`.
* `GWsum_le`: if the one-move sums of steps, links and leaves are at most `u0`, `u1`, `l0` from every block, any
  fixed point `α ≥ 1 + u0 α + u1 β`, `β ≥ 1 + u0 α + l0 γ`, `γ ≥ 1 + u1 β` bounds `GWsum` in the states `A, B, C`.
* `sum_offsets_le_gen`: a one-move sum over the blocks at offsets `D ≤ |v|∞ ≤ A` is at most the sum of the same
  weight over `offBox D A`, when the weight depends on the offset only.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The weight of a word with move weights `g`: the product of `g` along the word. -/
noncomputable def gwt (g : G.Block → G.Move → ℝ) : G.Block → List G.Move → ℝ
  | _, [] => 1
  | cur, m :: ms => g cur m * gwt g (nextBlk cur m) ms

theorem gwt_nonneg {g : G.Block → G.Move → ℝ} (hg : ∀ cur m, 0 ≤ g cur m) :
    ∀ (cur : G.Block) (ms : List G.Move), 0 ≤ gwt g cur ms
  | _, [] => zero_le_one
  | cur, m :: ms => mul_nonneg (hg cur m) (gwt_nonneg hg _ ms)

/-- The weighted sum over all grammar words of length at most `N` from a state and a block. -/
noncomputable def GWsum (D A0 A1 : ℕ) (g : G.Block → G.Move → ℝ) : ℕ → GState → G.Block → ℝ
  | 0, _, _ => 1
  | N + 1, X, cur => 1 + ∑ m : G.Move, if allowed D A0 A1 X cur m then
      g cur m * GWsum D A0 A1 g N (nextSt m) (nextBlk cur m) else 0

/-- **Transfer bound, combinatorial part.** Any finite set of grammar words of length at most `N` has total
weight at most `GWsum N`. -/
theorem sum_gwt_le (D A0 A1 : ℕ) {g : G.Block → G.Move → ℝ} (hg : ∀ cur m, 0 ≤ g cur m) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block) (R : Finset (List G.Move)),
      (∀ r ∈ R, GramFrom D A0 A1 X cur r ∧ r.length ≤ N) →
        ∑ r ∈ R, gwt g cur r ≤ GWsum D A0 A1 g N X cur := by
  induction N with
  | zero =>
    intro X cur R hR
    have hsub : R ⊆ {[]} := fun r hr => by
      have h := (hR r hr).2
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    calc ∑ r ∈ R, gwt g cur r ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), gwt g cur r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => gwt_nonneg hg cur r
      _ = GWsum D A0 A1 g 0 X cur := by rw [Finset.sum_singleton]; rfl
  | succ N ih =>
    intro X cur R hR
    rw [← Finset.sum_fiberwise R List.head? (fun r => gwt g cur r), Fintype.sum_option]
    have h1 : ∑ r ∈ R with r.head? = none, gwt g cur r ≤ 1 := by
      have hsub : (R.filter fun r => r.head? = none) ⊆ {[]} := fun r hr => by
        rw [Finset.mem_filter] at hr
        rw [Finset.mem_singleton]
        exact List.head?_eq_none_iff.1 hr.2
      calc _ ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), gwt g cur r :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => gwt_nonneg hg cur r
        _ = 1 := by rw [Finset.sum_singleton]; rfl
    have h2 : ∀ m : G.Move, ∑ r ∈ R with r.head? = some m, gwt g cur r ≤
        if allowed D A0 A1 X cur m then g cur m * GWsum D A0 A1 g N (nextSt m) (nextBlk cur m) else 0 := by
      intro m
      have hform : ∀ r ∈ R.filter (fun r => r.head? = some m), r = m :: r.tail := by
        intro r hr
        rw [Finset.mem_filter] at hr
        cases r with
        | nil => simp at hr
        | cons a t =>
          simp only [List.head?_cons, Option.some.injEq] at hr
          rw [hr.2]
          rfl
      split_ifs with hal
      · have hinj : Set.InjOn List.tail ((R.filter (fun r => r.head? = some m) : Finset (List G.Move)) :
            Set (List G.Move)) := fun r hr r' hr' h => by
          rw [hform r hr, hform r' hr', h]
        calc ∑ r ∈ R with r.head? = some m, gwt g cur r
            = ∑ r ∈ R with r.head? = some m, g cur m * gwt g (nextBlk cur m) r.tail := by
              refine Finset.sum_congr rfl fun r hr => ?_
              conv_lhs => rw [hform r hr]
              rfl
          _ = g cur m * ∑ t ∈ (R.filter (fun r => r.head? = some m)).image List.tail,
                gwt g (nextBlk cur m) t := by
              rw [Finset.sum_image hinj, Finset.mul_sum]
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (ih _ _ _ fun t ht => ?_) (hg cur m)
              obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
              have hrR := (Finset.mem_filter.1 hr).1
              obtain ⟨hgr, hlen⟩ := hR r hrR
              rw [hform r hr] at hgr hlen
              refine ⟨hgr.2, ?_⟩
              simp only [List.length_cons] at hlen
              omega
      · have hempty : R.filter (fun r => r.head? = some m) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
          have hrR := (Finset.mem_filter.1 hr).1
          have hgr := (hR r hrR).1
          rw [hform r hr] at hgr
          exact hal hgr.1
        rw [hempty, Finset.sum_empty]
    calc (∑ r ∈ R with r.head? = none, gwt g cur r) + ∑ m, ∑ r ∈ R with r.head? = some m, gwt g cur r
        ≤ 1 + ∑ m : G.Move, (if allowed D A0 A1 X cur m then
            g cur m * GWsum D A0 A1 g N (nextSt m) (nextBlk cur m) else 0) :=
          add_le_add h1 (Finset.sum_le_sum fun m _ => h2 m)
      _ = GWsum D A0 A1 g (N + 1) X cur := rfl

/-- **Transfer bound with general move weights.** If the one-move sums of steps, links and leaves are at most
`u0`, `u1`, `l0` from every block and `α, β, γ ≥ 0` satisfy the three fixed-point inequalities, then
`GWsum ≤ α, β, γ` in the states `A, B, C`. -/
theorem GWsum_le {D A0 A1 : ℕ} {g : G.Block → G.Move → ℝ} {u0 u1 l0 α β γ : ℝ} (hg : ∀ cur m, 0 ≤ g cur m)
    (hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
      g cur (.step b) ≤ u0)
    (hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1),
      g cur (.link b) ≤ u1)
    (hl0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
      g cur (.leaf b) ≤ l0)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hu00 : 0 ≤ u0) (hu10 : 0 ≤ u1) (hl00 : 0 ≤ l0)
    (hα : 1 + u0 * α + u1 * β ≤ α) (hβ : 1 + u0 * α + l0 * γ ≤ β) (hγ : 1 + u1 * β ≤ γ) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block), GWsum D A0 A1 g N X cur ≤ X.val α β γ := by
  have h1α : 1 ≤ α := by nlinarith
  have h1β : 1 ≤ β := by nlinarith
  have h1γ : 1 ≤ γ := by nlinarith
  induction N with
  | zero => intro X cur; cases X <;> simp only [GWsum, GState.val] <;> assumption
  | succ N ih =>
    intro X cur
    have hWA : ∀ b, GWsum D A0 A1 g N .A b ≤ α := fun b => ih .A b
    have hWB : ∀ b, GWsum D A0 A1 g N .B b ≤ β := fun b => ih .B b
    have hWC : ∀ b, GWsum D A0 A1 g N .C b ≤ γ := fun b => ih .C b
    have hu0' := mul_le_mul_of_nonneg_left (hu0 cur) hα0
    have hu1' := mul_le_mul_of_nonneg_left (hu1 cur) hβ0
    have hl0' := mul_le_mul_of_nonneg_left (hl0 cur) hγ0
    show 1 + ∑ m : G.Move, _ ≤ _
    rw [sum_move]
    cases X with
    | A =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun b => g cur (.step b)) (fun b => rfl) (fun b => hg cur _) hα0 (fun b _ => hWA b))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1) (fun b h => h)
          (fun b => g cur (.link b)) (fun b => rfl) (fun b => hg cur _) hβ0 (fun b _ => hWB b)))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))) ?_
      show _ ≤ α
      linarith
    | B =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun b => g cur (.step b)) (fun b => rfl) (fun b => hg cur _) hα0 (fun b _ => hWA b))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun b => g cur (.leaf b)) (fun b => rfl) (fun b => hg cur _) hγ0 (fun _ _ => hWC cur)))) ?_
      show _ ≤ β
      linarith
    | C =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1) (fun b h => h)
          (fun b => g cur (.link b)) (fun b => rfl) (fun b => hg cur _) hβ0 (fun b _ => hWB b)))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))) ?_
      show _ ≤ γ
      linarith

/-- **One-move sums with an offset weight.** If the weight of `b` depends only on the offset `b - cur`, the sum over
the blocks at offsets `D ≤ |v|∞ ≤ A` is at most the sum over `offBox D A`. -/
theorem sum_offsets_le_gen (D A : ℕ) (f : ℤ × ℤ → ℝ) (hf : ∀ v, 0 ≤ f v) (cur : G.Block) :
    ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A),
      f ((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val) ≤ ∑ v ∈ offBox D A, f v := by
  have hinj : Set.InjOn (fun b : G.Block => ((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val))
      ((univ.filter (fun b : G.Block => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A) : Finset G.Block) :
        Set G.Block) := fun b _ b' _ h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hsub : (univ.filter (fun b : G.Block => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A)).image
      (fun b : G.Block => ((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val)) ⊆ offBox D A := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_filter] at hb
    obtain ⟨h1, h2⟩ := hb.2
    have e1 := ndist_eq_natAbs cur.1.val b.1.val
    have e2 := ndist_eq_natAbs cur.2.val b.2.val
    have hd : G.blockDist cur b = max (ndist cur.1.val b.1.val) (ndist cur.2.val b.2.val) := rfl
    simp only [offBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;> omega
  rw [← Finset.sum_image (f := f) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf _

/-! ### The T2 move weights -/

/-- The block `ℓ1` displacement. -/
def bdl1 (b b' : G.Block) : ℕ := ndist b.1.val b'.1.val + ndist b.2.val b'.2.val

/-- **The T2 move weights**: `ε e^{μ |v|_1 + s v_y}` for steps and links (`μ = λ κ`), `ε` for leaves. -/
noncomputable def t2g (ε μ s : ℝ) (cur : G.Block) : G.Move → ℝ
  | .step b => ε * Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))
  | .link b => ε * Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))
  | .leaf _ => ε

theorem t2g_nonneg {ε : ℝ} (hε : 0 ≤ ε) (μ s : ℝ) (cur : G.Block) (m : G.Move) : 0 ≤ t2g ε μ s cur m := by
  cases m with
  | step b => exact mul_nonneg hε (Real.exp_pos _).le
  | link b => exact mul_nonneg hε (Real.exp_pos _).le
  | leaf b => exact hε

/-- The route norm of a word: the sum of the block `ℓ1` displacements of its steps and links. -/
def rnorm : G.Block → List G.Move → ℕ
  | _, [] => 0
  | cur, .step b :: ms => bdl1 cur b + rnorm b ms
  | cur, .link b :: ms => bdl1 cur b + rnorm b ms
  | cur, .leaf _ :: ms => rnorm cur ms

/-- The weight of a word under the T2 move weights: `ε^len e^{μ · (route norm) + s · (net climb)}`. -/
theorem gwt_t2g (ε μ s : ℝ) : ∀ (cur : G.Block) (ms : List G.Move),
    gwt (t2g ε μ s) cur ms = ε ^ ms.length *
      Real.exp (μ * (rnorm cur ms : ℝ) + s * (((endBlock cur ms).2.val : ℝ) - (cur.2.val : ℝ)))
  | cur, [] => by simp [gwt, rnorm, endBlock]
  | cur, .step b :: ms => by
    rw [gwt, gwt_t2g ε μ s (nextBlk cur (.step b)) ms, endBlock_cons, List.length_cons, pow_succ]
    simp only [t2g, nextBlk, rnorm]
    push_cast
    rw [show ε * Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) *
        (ε ^ ms.length * Real.exp (μ * (rnorm b ms : ℝ) + s * (((endBlock b ms).2.val : ℝ) - (b.2.val : ℝ)))) =
        ε ^ ms.length * ε * (Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) *
          Real.exp (μ * (rnorm b ms : ℝ) + s * (((endBlock b ms).2.val : ℝ) - (b.2.val : ℝ)))) by ring,
      ← Real.exp_add]
    ring_nf
  | cur, .link b :: ms => by
    rw [gwt, gwt_t2g ε μ s (nextBlk cur (.link b)) ms, endBlock_cons, List.length_cons, pow_succ]
    simp only [t2g, nextBlk, rnorm]
    push_cast
    rw [show ε * Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) *
        (ε ^ ms.length * Real.exp (μ * (rnorm b ms : ℝ) + s * (((endBlock b ms).2.val : ℝ) - (b.2.val : ℝ)))) =
        ε ^ ms.length * ε * (Real.exp (μ * (bdl1 cur b : ℝ) + s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) *
          Real.exp (μ * (rnorm b ms : ℝ) + s * (((endBlock b ms).2.val : ℝ) - (b.2.val : ℝ)))) by ring,
      ← Real.exp_add]
    ring_nf
  | cur, .leaf b :: ms => by
    rw [gwt, gwt_t2g ε μ s (nextBlk cur (.leaf b)) ms, endBlock_cons, List.length_cons, pow_succ]
    simp only [t2g, nextBlk, rnorm]
    ring

theorem bdl1_triangle (a b c : G.Block) : bdl1 a c ≤ bdl1 a b + bdl1 b c := by
  simp only [bdl1, ndist]
  omega

/-- The route norm dominates the block `ℓ1` displacement from the start to the end of the word. -/
theorem bdl1_le_rnorm : ∀ (cur : G.Block) (ms : List G.Move), bdl1 cur (endBlock cur ms) ≤ rnorm cur ms
  | cur, [] => by simp [bdl1, ndist, endBlock, rnorm]
  | cur, .step b :: ms => by
    rw [endBlock_cons]
    have ih := bdl1_le_rnorm b ms
    have ht := bdl1_triangle cur b (endBlock b ms)
    simp only [nextBlk, rnorm]
    omega
  | cur, .link b :: ms => by
    rw [endBlock_cons]
    have ih := bdl1_le_rnorm b ms
    have ht := bdl1_triangle cur b (endBlock b ms)
    simp only [nextBlk, rnorm]
    omega
  | cur, .leaf b :: ms => by
    rw [endBlock_cons]
    simp only [nextBlk, rnorm]
    exact bdl1_le_rnorm cur ms

end S3Geom

end QECML
