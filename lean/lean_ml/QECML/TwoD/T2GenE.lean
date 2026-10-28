import QECML.TwoD.T2Gen

/-!
# Grammar words with end weights

The routes of a T2 skeleton may not end in every grammar state: a family route and the bottom route never end right
after a link (a link is followed by a leaf or a step). `GWsumE e` weights the end of a word by `e` of its final state;
with `e B = 0` the words ending after a link drop out. The transfer bound becomes `α ≥ e A + u0 α + u1 β`,
`β ≥ e B + u0 α + l0 γ`, `γ ≥ e C + u1 β` (`GWsumE_le`).
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-- The state after a word. -/
def finalSt : GState → G.Block → List G.Move → GState
  | X, _, [] => X
  | _, cur, m :: ms => finalSt (nextSt m) (nextBlk cur m) ms

/-- The weighted sum over the grammar words of length at most `N`, each word weighted by `e` of its final state. -/
noncomputable def GWsumE (D A0 A1 : ℕ) (g : G.Block → G.Move → ℝ) (e : GState → ℝ) : ℕ → GState → G.Block → ℝ
  | 0, X, _ => e X
  | N + 1, X, cur => e X + ∑ m : G.Move, if allowed D A0 A1 X cur m then
      g cur m * GWsumE D A0 A1 g e N (nextSt m) (nextBlk cur m) else 0

/-- **Transfer bound with end weights, combinatorial part.** -/
theorem sum_gwtE_le (D A0 A1 : ℕ) {g : G.Block → G.Move → ℝ} (hg : ∀ cur m, 0 ≤ g cur m) {e : GState → ℝ}
    (he : ∀ X, 0 ≤ e X) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block) (R : Finset (List G.Move)),
      (∀ r ∈ R, GramFrom D A0 A1 X cur r ∧ r.length ≤ N) →
        ∑ r ∈ R, gwt g cur r * e (finalSt X cur r) ≤ GWsumE D A0 A1 g e N X cur := by
  have hnn : ∀ X cur r, 0 ≤ gwt g cur r * e (finalSt X cur r) := fun X cur r =>
    mul_nonneg (gwt_nonneg hg cur r) (he _)
  induction N with
  | zero =>
    intro X cur R hR
    have hsub : R ⊆ {[]} := fun r hr => by
      have h := (hR r hr).2
      rw [Finset.mem_singleton]
      exact List.eq_nil_of_length_eq_zero (by omega)
    calc ∑ r ∈ R, gwt g cur r * e (finalSt X cur r)
        ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), gwt g cur r * e (finalSt X cur r) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hnn X cur r
      _ = GWsumE D A0 A1 g e 0 X cur := by
          rw [Finset.sum_singleton]
          simp [gwt, finalSt, GWsumE]
  | succ N ih =>
    intro X cur R hR
    rw [← Finset.sum_fiberwise R List.head? (fun r => gwt g cur r * e (finalSt X cur r)), Fintype.sum_option]
    have h1 : ∑ r ∈ R with r.head? = none, gwt g cur r * e (finalSt X cur r) ≤ e X := by
      have hsub : (R.filter fun r => r.head? = none) ⊆ {[]} := fun r hr => by
        rw [Finset.mem_filter] at hr
        rw [Finset.mem_singleton]
        exact List.head?_eq_none_iff.1 hr.2
      calc _ ≤ ∑ r ∈ ({[]} : Finset (List G.Move)), gwt g cur r * e (finalSt X cur r) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => hnn X cur r
        _ = e X := by
            rw [Finset.sum_singleton]
            simp [gwt, finalSt]
    have h2 : ∀ m : G.Move, ∑ r ∈ R with r.head? = some m, gwt g cur r * e (finalSt X cur r) ≤
        if allowed D A0 A1 X cur m then g cur m * GWsumE D A0 A1 g e N (nextSt m) (nextBlk cur m) else 0 := by
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
        calc ∑ r ∈ R with r.head? = some m, gwt g cur r * e (finalSt X cur r)
            = ∑ r ∈ R with r.head? = some m,
                g cur m * (gwt g (nextBlk cur m) r.tail * e (finalSt (nextSt m) (nextBlk cur m) r.tail)) := by
              refine Finset.sum_congr rfl fun r hr => ?_
              conv_lhs => rw [hform r hr]
              simp only [gwt, finalSt]
              ring
          _ = g cur m * ∑ t ∈ (R.filter (fun r => r.head? = some m)).image List.tail,
                gwt g (nextBlk cur m) t * e (finalSt (nextSt m) (nextBlk cur m) t) := by
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
    calc (∑ r ∈ R with r.head? = none, gwt g cur r * e (finalSt X cur r)) +
          ∑ m, ∑ r ∈ R with r.head? = some m, gwt g cur r * e (finalSt X cur r)
        ≤ e X + ∑ m : G.Move, (if allowed D A0 A1 X cur m then
            g cur m * GWsumE D A0 A1 g e N (nextSt m) (nextBlk cur m) else 0) :=
          add_le_add h1 (Finset.sum_le_sum fun m _ => h2 m)
      _ = GWsumE D A0 A1 g e (N + 1) X cur := rfl

/-- **Transfer bound with end weights.** -/
theorem GWsumE_le {D A0 A1 : ℕ} {g : G.Block → G.Move → ℝ} {e : GState → ℝ} {u0 u1 l0 α β γ : ℝ}
    (hg : ∀ cur m, 0 ≤ g cur m)
    (hu0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
      g cur (.step b) ≤ u0)
    (hu1 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1),
      g cur (.link b) ≤ u1)
    (hl0 : ∀ cur : G.Block, ∑ b ∈ univ.filter (fun b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0),
      g cur (.leaf b) ≤ l0)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hα : e .A + u0 * α + u1 * β ≤ α) (hβ : e .B + u0 * α + l0 * γ ≤ β) (hγ : e .C + u1 * β ≤ γ)
    (heA : e .A ≤ α) (heB : e .B ≤ β) (heC : e .C ≤ γ) (N : ℕ) :
    ∀ (X : GState) (cur : G.Block), GWsumE D A0 A1 g e N X cur ≤ X.val α β γ := by
  induction N with
  | zero => intro X cur; cases X <;> simp only [GWsumE, GState.val] <;> assumption
  | succ N ih =>
    intro X cur
    have hWA : ∀ b, GWsumE D A0 A1 g e N .A b ≤ α := fun b => ih .A b
    have hWB : ∀ b, GWsumE D A0 A1 g e N .B b ≤ β := fun b => ih .B b
    have hWC : ∀ b, GWsumE D A0 A1 g e N .C b ≤ γ := fun b => ih .C b
    have hu0' := mul_le_mul_of_nonneg_left (hu0 cur) hα0
    have hu1' := mul_le_mul_of_nonneg_left (hu1 cur) hβ0
    have hl0' := mul_le_mul_of_nonneg_left (hl0 cur) hγ0
    show e X + ∑ m : G.Move, _ ≤ _
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

end S3Geom

end QECML
