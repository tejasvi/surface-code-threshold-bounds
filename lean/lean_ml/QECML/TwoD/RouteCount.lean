import QECML.TwoD.RouteExist

/-!
# The T1 count

`H2D_T1count` bounds the `ε`-weighted number of counted-block sets of valid routes. Here it is reduced to a
transfer bound. Routes are words of a three-state grammar (`A`: at the start or after a step; `B`: after a link;
`C`: after a leaf), each move weighted by `ε e^{s v_y}` (`v_y` the signed row offset of the move; a leaf does not
move the route). The weighted sum over the grammar words of bounded length (`Wsum`) is at most `α` for any
`α, β, γ ≥ 0` with `α ≥ 1 + u0 α + u1 β`, `β ≥ 1 + u0 α + l0 γ`, `γ ≥ 1 + u1 β`, where `u0`, `u1`, `l0` bound the
one-move sums of steps, links and leaves (`Wsum_le`). A valid route climbs at least `n_y - H0` rows,
`H0 = 2 h_s + A1 + 1`, so `routeCount ≤ n_x (h_s + 1) α e^{-s (n_y - H0)}` (`routeCount_le`).

The automaton counts each grammar word once; the constant `(h_s + 1) W1 (1 + ε T1 W1) / (1 - V1)` of the paper's
proof counts a word ending with a link and a run of steps twice and is therefore larger than `(h_s + 1) α` at the
fixed point.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The moves as a sum type. -/
def moveEquiv : G.Block ⊕ G.Block ⊕ G.Block ≃ G.Move where
  toFun x := match x with
    | .inl b => .step b
    | .inr (.inl b) => .link b
    | .inr (.inr b) => .leaf b
  invFun m := match m with
    | .step b => .inl b
    | .link b => .inr (.inl b)
    | .leaf b => .inr (.inr b)
  left_inv x := by rcases x with b | b | b <;> rfl
  right_inv m := by cases m <;> rfl

noncomputable instance : Fintype G.Move := Fintype.ofEquiv _ moveEquiv

theorem sum_move (F : G.Move → ℝ) :
    ∑ m, F m = ∑ b, F (.step b) + ∑ b, F (.link b) + ∑ b, F (.leaf b) := by
  rw [← Fintype.sum_equiv moveEquiv (fun x => F (moveEquiv x)) F (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, add_assoc]
  rfl

/-- Grammar states: `A` at the start or after a step, `B` after a link, `C` after a leaf. -/
inductive GState where
  | A
  | B
  | C

/-- The moves allowed in a state from the current block. -/
def allowed (D A0 A1 : ℕ) : GState → G.Block → G.Move → Prop
  | .A, cur, .step b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .A, cur, .link b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
  | .A, _, .leaf _ => False
  | .B, cur, .step b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .B, _, .link _ => False
  | .B, cur, .leaf b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
  | .C, _, .step _ => False
  | .C, cur, .link b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
  | .C, _, .leaf _ => False

/-- The state after a move. -/
def nextSt : G.Move → GState
  | .step _ => .A
  | .link _ => .B
  | .leaf _ => .C

/-- The current block after a move (a leaf does not move the route). -/
def nextBlk : G.Block → G.Move → G.Block
  | _, .step b => b
  | _, .link b => b
  | cur, .leaf _ => cur

/-- Grammar words from a state and a current block. -/
def GramFrom (D A0 A1 : ℕ) : GState → G.Block → List G.Move → Prop
  | _, _, [] => True
  | X, cur, m :: ms => allowed D A0 A1 X cur m ∧ GramFrom D A0 A1 (nextSt m) (nextBlk cur m) ms

theorem endBlock_cons (cur : G.Block) (m : G.Move) (ms : List G.Move) :
    endBlock cur (m :: ms) = endBlock (nextBlk cur m) ms := by
  cases m <;> rfl

/-- The constraint of a state on the next move. -/
def compat : GState → G.Move → Prop
  | .A, m => ¬ m.isLeaf
  | .B, m => ¬ m.isLink
  | .C, m => m.isLink

theorem compat_next {m m' : G.Move} (h : GramOK m m') : compat (nextSt m) m' := by
  cases m <;> cases m' <;> simp_all [GramOK, compat, nextSt, Move.isLeaf, Move.isLink, Move.isStep]

/-- Offsets and grammar of a move list make it a grammar word. -/
theorem gram_of_moves {D A0 A1 : ℕ} (ms : List G.Move) :
    ∀ (X : GState) (cur : G.Block), MovesOK D A0 A1 cur ms → List.IsChain GramOK ms →
      (∀ m ∈ ms.head?, compat X m) → GramFrom D A0 A1 X cur ms := by
  induction ms with
  | nil => intro _ _ _ _ _; trivial
  | cons m ms ih =>
    intro X cur hmv hch hhd
    have hc : compat X m := hhd m rfl
    have hnext : ∀ m' ∈ ms.head?, compat (nextSt m) m' := by
      intro m' hm'
      cases ms with
      | nil => simp at hm'
      | cons m'' ms' =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm'
        subst hm'
        exact compat_next (List.isChain_cons_cons.1 hch).1
    have hch' : List.IsChain GramOK ms := hch.tail
    cases m with
    | step b =>
      obtain ⟨h1, h2, h3⟩ := hmv
      cases X with
      | A => exact ⟨⟨h1, h2⟩, ih _ _ h3 hch' hnext⟩
      | B => exact ⟨⟨h1, h2⟩, ih _ _ h3 hch' hnext⟩
      | C => exact absurd hc (fun h => h)
    | link b =>
      obtain ⟨h1, h2, h3⟩ := hmv
      cases X with
      | A => exact ⟨⟨h1, h2⟩, ih _ _ h3 hch' hnext⟩
      | B => exact absurd trivial hc
      | C => exact ⟨⟨h1, h2⟩, ih _ _ h3 hch' hnext⟩
    | leaf b =>
      obtain ⟨h1, h2, h3⟩ := hmv
      cases X with
      | A => exact absurd trivial hc
      | B => exact ⟨⟨h1, h2⟩, ih _ _ h3 hch' hnext⟩
      | C => exact absurd hc (fun h => h)

/-- The weight of a move word from `cur`: `ε` per move and the tilt `e^{s Δ}` of its net row climb `Δ`. -/
noncomputable def wt (ε s : ℝ) (cur : G.Block) (ms : List G.Move) : ℝ :=
  ε ^ ms.length * Real.exp (s * (((endBlock cur ms).2.val : ℝ) - (cur.2.val : ℝ)))

theorem wt_nil (ε s : ℝ) (cur : G.Block) : wt ε s cur [] = 1 := by
  simp [wt, endBlock]

theorem wt_cons (ε s : ℝ) (cur : G.Block) (m : G.Move) (ms : List G.Move) :
    wt ε s cur (m :: ms) = ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
      wt ε s (nextBlk cur m) ms := by
  simp only [wt, endBlock_cons, List.length_cons, pow_succ]
  rw [show s * (((endBlock (nextBlk cur m) ms).2.val : ℝ) - (cur.2.val : ℝ)) =
      s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ)) +
        s * (((endBlock (nextBlk cur m) ms).2.val : ℝ) - ((nextBlk cur m).2.val : ℝ)) by ring, Real.exp_add]
  ring

theorem wt_nonneg {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) (cur : G.Block) (ms : List G.Move) : 0 ≤ wt ε s cur ms :=
  mul_nonneg (pow_nonneg hε _) (Real.exp_pos _).le

/-- The weighted sum over all grammar words of length at most `N` from a state and a block. -/
noncomputable def Wsum (D A0 A1 : ℕ) (ε s : ℝ) : ℕ → GState → G.Block → ℝ
  | 0, _, _ => 1
  | N + 1, X, cur => 1 + ∑ m : G.Move, if allowed D A0 A1 X cur m then
      ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
        Wsum D A0 A1 ε s N (nextSt m) (nextBlk cur m) else 0

/-- **Transfer bound, combinatorial part.** Any finite set of grammar words of length at most `N` has total
weight at most `Wsum N`. -/
theorem sum_wt_le (D A0 A1 : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block) (R : Finset (List G.Move)),
      (∀ r ∈ R, GramFrom D A0 A1 X cur r ∧ r.length ≤ N) →
        ∑ r ∈ R, wt ε s cur r ≤ Wsum D A0 A1 ε s N X cur := by
  induction N with
  | zero =>
    intro X cur R hR
    have hsub : R ⊆ {[]} := fun r hr => by
      have h := (hR r hr).2
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    calc ∑ r ∈ R, wt ε s cur r ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), wt ε s cur r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => wt_nonneg hε s cur r
      _ = Wsum D A0 A1 ε s 0 X cur := by rw [Finset.sum_singleton, wt_nil]; rfl
  | succ N ih =>
    intro X cur R hR
    rw [← Finset.sum_fiberwise R List.head? (fun r => wt ε s cur r), Fintype.sum_option]
    have h1 : ∑ r ∈ R with r.head? = none, wt ε s cur r ≤ 1 := by
      have hsub : (R.filter fun r => r.head? = none) ⊆ {[]} := fun r hr => by
        rw [Finset.mem_filter] at hr
        rw [Finset.mem_singleton]
        exact List.head?_eq_none_iff.1 hr.2
      calc _ ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), wt ε s cur r :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => wt_nonneg hε s cur r
        _ = 1 := by rw [Finset.sum_singleton, wt_nil]
    have h2 : ∀ m : G.Move, ∑ r ∈ R with r.head? = some m, wt ε s cur r ≤
        if allowed D A0 A1 X cur m then
          ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
            Wsum D A0 A1 ε s N (nextSt m) (nextBlk cur m) else 0 := by
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
        calc ∑ r ∈ R with r.head? = some m, wt ε s cur r
            = ∑ r ∈ R with r.head? = some m,
                ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
                  wt ε s (nextBlk cur m) r.tail := by
              refine Finset.sum_congr rfl fun r hr => ?_
              conv_lhs => rw [hform r hr]
              rw [wt_cons]
          _ = ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
                ∑ t ∈ (R.filter (fun r => r.head? = some m)).image List.tail, wt ε s (nextBlk cur m) t := by
              rw [Finset.sum_image hinj, Finset.mul_sum]
          _ ≤ _ := by
              refine mul_le_mul_of_nonneg_left (ih _ _ _ fun t ht => ?_)
                (mul_nonneg hε (Real.exp_pos _).le)
              obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
              have hrR := (Finset.mem_filter.1 hr).1
              obtain ⟨hg, hlen⟩ := hR r hrR
              rw [hform r hr] at hg hlen
              refine ⟨hg.2, ?_⟩
              simp only [List.length_cons] at hlen
              omega
      · have hempty : R.filter (fun r => r.head? = some m) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
          have hrR := (Finset.mem_filter.1 hr).1
          have hg := (hR r hrR).1
          rw [hform r hr] at hg
          exact hal hg.1
        rw [hempty, Finset.sum_empty]
    calc (∑ r ∈ R with r.head? = none, wt ε s cur r) + ∑ m, ∑ r ∈ R with r.head? = some m, wt ε s cur r
        ≤ 1 + ∑ m : G.Move, (if allowed D A0 A1 X cur m then
            ε * Real.exp (s * (((nextBlk cur m).2.val : ℝ) - (cur.2.val : ℝ))) *
              Wsum D A0 A1 ε s N (nextSt m) (nextBlk cur m) else 0) :=
          add_le_add h1 (Finset.sum_le_sum fun m _ => h2 m)
      _ = Wsum D A0 A1 ε s (N + 1) X cur := rfl
theorem sum_ite_bound {Q : G.Block → Prop} {_hQ : DecidablePred Q} (P : G.Block → Prop) [DecidablePred P]
    (hQP : ∀ b, Q b → P b) {g w : G.Block → ℝ} (g' : G.Block → ℝ) (hgg : ∀ b, g b = g' b) {v : ℝ}
    (hg : ∀ b, 0 ≤ g' b) (hv : 0 ≤ v) (hw : ∀ b, Q b → w b ≤ v) :
    ∑ b, (if Q b then g b * w b else 0) ≤ v * ∑ b ∈ univ.filter P, g' b := by
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hq : Q b
  · have hp := hQP b hq
    simp only [hq, hp, ↓reduceIte]
    rw [mul_comm v, hgg b]
    exact mul_le_mul_of_nonneg_left (hw b hq) (hg b)
  · simp only [hq, ↓reduceIte]
    split_ifs
    · exact mul_nonneg hv (hg b)
    · exact le_rfl

/-- The value of the transfer bound in each state. -/
def GState.val (α β γ : ℝ) : GState → ℝ
  | .A => α
  | .B => β
  | .C => γ

/-- **Transfer bound.** If the one-move sums of steps, links and leaves are at most `u0`, `u1`, `l0` from every
block and `α, β, γ ≥ 0` satisfy the three fixed-point inequalities, then `Wsum ≤ α, β, γ` in the states
`A, B, C`. -/
theorem Wsum_le {D A0 A1 : ℕ} {ε s u0 u1 l0 α β γ : ℝ} (hε : 0 ≤ ε)
    (hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
      ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ u0)
    (hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1),
      ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ u1)
    (hl0 : ∀ cur : G.Block, ∑ _b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0), ε ≤ l0)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hu00 : 0 ≤ u0) (hu10 : 0 ≤ u1) (hl00 : 0 ≤ l0)
    (hα : 1 + u0 * α + u1 * β ≤ α) (hβ : 1 + u0 * α + l0 * γ ≤ β) (hγ : 1 + u1 * β ≤ γ) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block), Wsum D A0 A1 ε s N X cur ≤ X.val α β γ := by
  have h1α : 1 ≤ α := by nlinarith
  have h1β : 1 ≤ β := by nlinarith
  have h1γ : 1 ≤ γ := by nlinarith
  induction N with
  | zero => intro X cur; cases X <;> simp only [Wsum, GState.val] <;> assumption
  | succ N ih =>
    intro X cur
    have hg : ∀ b : G.Block, 0 ≤ ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) :=
      fun b => mul_nonneg hε (Real.exp_pos _).le
    have hWA : ∀ b, Wsum D A0 A1 ε s N .A b ≤ α := fun b => ih .A b
    have hWB : ∀ b, Wsum D A0 A1 ε s N .B b ≤ β := fun b => ih .B b
    have hWC : ∀ b, Wsum D A0 A1 ε s N .C b ≤ γ := fun b => ih .C b
    have hu0' := mul_le_mul_of_nonneg_left (hu0 cur) hα0
    have hu1' := mul_le_mul_of_nonneg_left (hu1 cur) hβ0
    have hl0' := mul_le_mul_of_nonneg_left (hl0 cur) hγ0
    show 1 + ∑ m : G.Move, _ ≤ _
    rw [sum_move]
    cases X with
    | A =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun b => ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))) (fun b => rfl) hg hα0
          (fun b _ => hWA b))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1) (fun b h => h)
          (fun b => ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))) (fun b => rfl) hg hβ0
          (fun b _ => hWB b)))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))) ?_
      show _ ≤ α
      linarith
    | B =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun b => ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))) (fun b => rfl) hg hα0
          (fun b _ => hWA b))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0) (fun b h => h)
          (fun _ => ε) (fun b => by simp [nextBlk]) (fun _ => hε) hγ0 (fun _ _ => hWC cur)))) ?_
      show _ ≤ β
      linarith
    | C =>
      refine le_trans (add_le_add le_rfl (add_le_add (add_le_add
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)))
        (sum_ite_bound (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1) (fun b h => h)
          (fun b => ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))) (fun b => rfl) hg hβ0
          (fun b _ => hWB b)))
        (le_of_eq (Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h))))) ?_
      show _ ≤ γ
      linarith

/-- The offsets `v ∈ ℤ²` with `D ≤ |v|∞ ≤ A`. -/
def offBox (D A : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(A : ℤ)) A ×ˢ Finset.Icc (-(A : ℤ)) A).filter (fun v => D ≤ max v.1.natAbs v.2.natAbs)

/-- The tilted offset sum `Σ_{v ∈ offBox D A} e^{s v_y}`. -/
noncomputable def Tbox (D A : ℕ) (s : ℝ) : ℝ := ∑ v ∈ offBox D A, Real.exp (s * (v.2 : ℝ))

theorem ndist_eq_natAbs (a b : ℕ) : ndist a b = ((b : ℤ) - a).natAbs := by
  unfold ndist
  omega

/-- **One-move sums.** The tilted sum over the blocks at offset `D ≤ |v|∞ ≤ A` from `cur` is at most `Tbox D A s`
(the offsets of distinct blocks are distinct). -/
theorem sum_offsets_le (D A : ℕ) (s : ℝ) (cur : G.Block) :
    ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A),
      Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ Tbox D A s := by
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
  calc ∑ b ∈ univ.filter (fun b : G.Block => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A),
        Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ)))
      = ∑ b ∈ univ.filter (fun b : G.Block => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A),
          (fun v : ℤ × ℤ => Real.exp (s * (v.2 : ℝ)))
            ((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        push_cast
        rfl
    _ = ∑ v ∈ (univ.filter (fun b : G.Block => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A)).image
          (fun b : G.Block => ((b.1.val : ℤ) - cur.1.val, (b.2.val : ℤ) - cur.2.val)),
          Real.exp (s * (v.2 : ℝ)) :=
        (Finset.sum_image (f := fun v : ℤ × ℤ => Real.exp (s * (v.2 : ℝ))) hinj).symm
    _ ≤ Tbox D A s := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le

/-- The number of blocks at offset `D ≤ |v|∞ ≤ A` is at most `Tbox D A 0 = |offBox D A|`. -/
theorem card_offsets_le (D A : ℕ) (cur : G.Block) :
    ((univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A)).card : ℝ) ≤ Tbox D A 0 := by
  have h := sum_offsets_le (G := G) D A 0 cur
  simp only [zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- Blocks in the bottom strip: at most `n_x (h + 1)`. -/
theorem card_strip_le (h : ℕ) : (univ.filter (fun b : G.Block => b.2.val ≤ h)).card ≤ G.nx * (h + 1) := by
  have hsub : univ.filter (fun b : G.Block => b.2.val ≤ h) ⊆
      (univ : Finset (Fin G.nx)) ×ˢ (univ.filter (fun y : Fin G.ny => y.val ≤ h)) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
    exact hb
  have hy : (univ.filter (fun y : Fin G.ny => y.val ≤ h)).card ≤ (Finset.range (h + 1)).card :=
    Finset.card_le_card_of_injOn (fun y : Fin G.ny => y.val)
      (fun y hy => by
        have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        exact Finset.mem_coe.2 (Finset.mem_range.2 (show y.val < h + 1 by omega)))
      (fun y _ y' _ hyy => Fin.ext hyy)
  rw [Finset.card_range] at hy
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = G.nx * (univ.filter (fun y : Fin G.ny => y.val ≤ h)).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ G.nx * (h + 1) := Nat.mul_le_mul_left _ hy

end S3Geom

namespace S3Geom

variable (G : S3Geom)

/-- **The T1 count from the transfer bound.** With `u0`, `u1`, `l0` bounding the one-move sums at separation `D`
(steps and leaves up to `A0 = D - 1 + a0`, links up to `A1 = D - 1 + a1`) and `α, β, γ` a fixed point,
`routeCount ≤ n_x (h_s + 1) α e^{-s (n_y - H0)}` with `H0 = 2 h_s + A1 + 1`. -/
theorem routeCount_le (a0 a1 : ℕ) {ε s u0 u1 l0 α β γ : ℝ} (hε : 0 ≤ ε) (hs0 : 0 ≤ s)
    (hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + a0),
      ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ u0)
    (hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + a1),
      ε * Real.exp (s * ((b.2.val : ℝ) - (cur.2.val : ℝ))) ≤ u1)
    (hl0 : ∀ cur : G.Block, ∑ _b ∈ univ.filter
      (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + a0), ε ≤ l0)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hu00 : 0 ≤ u0) (hu10 : 0 ≤ u1) (hl00 : 0 ≤ l0)
    (hα : 1 + u0 * α + u1 * β ≤ α) (hβ : 1 + u0 * α + l0 * γ ≤ β) (hγ : 1 + u1 * β ≤ γ) :
    G.routeCount a0 a1 ε ≤ (G.nx : ℝ) * ((Stage1.hs a1 : ℝ) + 1) * α *
      Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
  have hD1 : 1 ≤ G.D := by show 1 ≤ 4 + 2 * G.R / G.L; exact le_add_right (by norm_num)
  -- a chosen route for each counted-block set
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Finset G.Block → G.Block × List G.Move,
      ∀ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1),
        G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) (ρ B).1 (ρ B).2 ∧
          B = ((ρ B).2.map Move.blk).toFinset := by
    refine ⟨fun B => if h : ∃ b0 ms, G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) b0 ms ∧
        B = (ms.map Move.blk).toFinset then (Classical.choose h, Classical.choose (Classical.choose_spec h))
      else ((⟨0, G.hnx⟩, ⟨0, G.hny⟩), []), fun B hB => ?_⟩
    have h : ∃ b0 ms, G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) b0 ms ∧
        B = (ms.map Move.blk).toFinset := (Finset.mem_filter.1 hB).2
    simp only [dite_eq_left h]
    exact Classical.choose_spec (Classical.choose_spec h)
  -- counted blocks are distinct
  have hnodup : ∀ b0 ms, G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) b0 ms →
      (ms.map Move.blk).Nodup := fun b0 ms hv =>
    List.Pairwise.imp (fun {b b'} h hbb => by rw [hbb, G.blockDist_self] at h; omega) hv.2.2.2.2.2.1
  have hinj : Set.InjOn ρ ((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) :
      Finset (Finset G.Block)) : Set (Finset G.Block)) := fun B hB B' hB' h => by
    rw [(hρ B hB).2, (hρ B' hB').2, h]
  -- the climb
  have hclimb : ∀ b0 ms, G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) b0 ms →
      ε ^ ms.length ≤ wt ε s b0 ms *
        Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
    intro b0 ms hv
    have hb0 : (b0.2.val : ℝ) ≤ (Stage1.hs a1 : ℝ) := by exact_mod_cast hv.1
    have htop : (G.ny : ℝ) ≤ ((endBlock b0 ms).2.val : ℝ) + 1 + (Stage1.hs a1 : ℝ) + ((G.D - 1 + a1 : ℕ) : ℝ) := by
      exact_mod_cast hv.2.2.2.2.2.2
    have hrow : (G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ) ≤
        ((endBlock b0 ms).2.val : ℝ) - (b0.2.val : ℝ) := by
      push_cast at htop ⊢
      linarith
    unfold wt
    rw [mul_assoc, ← Real.exp_add]
    have h0 : 0 ≤ s * (((endBlock b0 ms).2.val : ℝ) - (b0.2.val : ℝ)) +
        -s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ)) := by
      nlinarith
    calc ε ^ ms.length = ε ^ ms.length * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp h0) (pow_nonneg hε _)
  -- grammar words and lengths
  have hgram : ∀ b0 ms, G.ValidRoute G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1) b0 ms →
      GramFrom G.D (G.D - 1 + a0) (G.D - 1 + a1) .A b0 ms ∧ ms.length ≤ Fintype.card G.Block := by
    intro b0 ms hv
    refine ⟨gram_of_moves ms .A b0 hv.2.1 hv.2.2.1 hv.2.2.2.1, ?_⟩
    have := (hnodup b0 ms hv).length_le_card
    rwa [List.length_map] at this
  -- the transfer bound
  have hW : ∀ b0, Wsum G.D (G.D - 1 + a0) (G.D - 1 + a1) ε s (Fintype.card G.Block) .A b0 ≤ α := fun b0 =>
    Wsum_le hε hu0 hu1 hl0 hα0 hβ0 hγ0 hu00 hu10 hl00 hα hβ hγ _ .A b0
  have hE0 : 0 ≤ Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) :=
    (Real.exp_pos _).le
  have hfib : ∀ b0, ∑ r ∈ ((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ).filter
      (fun r => r.1 = b0), wt ε s r.1 r.2 ≤ α := by
    intro b0
    have hinj2 : Set.InjOn Prod.snd ((((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image
        ρ).filter (fun r => r.1 = b0) : Finset (G.Block × List G.Move)) : Set (G.Block × List G.Move)) :=
      fun r hr r' hr' h => by
        have h1 := (Finset.mem_filter.1 hr).2
        have h2 := (Finset.mem_filter.1 hr').2
        exact Prod.ext (h1.trans h2.symm) h
    calc ∑ r ∈ ((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ).filter
          (fun r => r.1 = b0), wt ε s r.1 r.2
        = ∑ r ∈ ((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ).filter
            (fun r => r.1 = b0), wt ε s b0 r.2 := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [(Finset.mem_filter.1 hr).2]
      _ = ∑ ms ∈ (((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ).filter
            (fun r => r.1 = b0)).image Prod.snd, wt ε s b0 ms := (Finset.sum_image hinj2).symm
      _ ≤ Wsum G.D (G.D - 1 + a0) (G.D - 1 + a1) ε s (Fintype.card G.Block) .A b0 := by
          refine sum_wt_le G.D (G.D - 1 + a0) (G.D - 1 + a1) hε s _ .A b0 _ fun ms hms => ?_
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hms
          obtain ⟨hrR, hr1⟩ := Finset.mem_filter.1 hr
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hrR
          have hv := (hρ B hB).1
          rw [hr1] at hv
          exact hgram _ _ hv
      _ ≤ α := hW b0
  calc G.routeCount a0 a1 ε
      = ∑ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1), ε ^ B.card := rfl
    _ = ∑ B ∈ G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1), ε ^ (ρ B).2.length := by
        refine Finset.sum_congr rfl fun B hB => ?_
        obtain ⟨hv, hBe⟩ := hρ B hB
        conv_lhs => rw [hBe]
        rw [List.toFinset_card_of_nodup (hnodup _ _ hv), List.length_map]
    _ = ∑ r ∈ (G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ, ε ^ r.2.length :=
        (Finset.sum_image (f := fun r : G.Block × List G.Move => ε ^ r.2.length) hinj).symm
    _ ≤ ∑ r ∈ (G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ,
          wt ε s r.1 r.2 * Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum fun r hr => ?_
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hr
        exact hclimb _ _ (hρ B hB).1
    _ = (∑ b0 ∈ univ.filter (fun b : G.Block => b.2.val ≤ Stage1.hs a1),
          ∑ r ∈ ((G.routeSets G.D (G.D - 1 + a0) (G.D - 1 + a1) (Stage1.hs a1)).image ρ).filter
            (fun r => r.1 = b0), wt ε s r.1 r.2) *
          Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
        rw [← Finset.sum_mul, Finset.sum_fiberwise_of_maps_to]
        intro r hr
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hr
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hρ B hB).1.1⟩
    _ ≤ (∑ b0 ∈ univ.filter (fun b : G.Block => b.2.val ≤ Stage1.hs a1), α) *
          Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun b0 _ => hfib b0) hE0
    _ = ((univ.filter (fun b : G.Block => b.2.val ≤ Stage1.hs a1)).card : ℝ) * α *
          Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (G.nx : ℝ) * ((Stage1.hs a1 : ℝ) + 1) * α *
          Real.exp (-s * ((G.ny : ℝ) - ((2 * Stage1.hs a1 + (G.D - 1 + a1) + 1 : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hα0) hE0
        have := card_strip_le (G := G) (Stage1.hs a1)
        exact_mod_cast this

end S3Geom

end QECML
