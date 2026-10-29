import QECD1.Indep3

/-!
# Level-0 clusters, level-1 components, and the offset sets of the skeleton

The skeleton of the 3D lemma lives on a finite set `F` of flagged blocks:
* the clusters are the `a0`-components of `F` (`a0 = 4`);
* the level-1 components are the `a1`-components (`a1 = 20`);
* each cluster carries a selection (`selection_A0`).

This module derives, without dimension-specific arguments, the offset facts the family keys need. Each uses (R0):
the root that the offset reaches is an actual block of `F`.

* `comp_sep`: blocks of `F` in different `a`-components are more than `a` apart.
* `step_mem_S0` (Selection3): steps between selected blocks of a cluster lie in `S0 = {5 ≤ |v|∞ ≤ 8}`.
* `link_mem_S1`: take a selected block `s` covering the exit block `b` of its cluster. The next root `b'` is an actual
  block of another cluster within `a1` of `b`. Then the link offset `b' - s` lies in `S1 = {5 ≤ |v|∞ ≤ 24}`:
  * the lower bound holds because different clusters are `≥ a0 + 1 = 5 = D` apart;
  * the upper bound is `link_le_A1`, with one cover offset.
* `witness_span`: let the witness part's root `e*` be an actual block, and the witness block `w` a block of `F` in
  another level-1 component, covered within `D - 1` by the last selected block `sw` of the walk. Then
  `|sw - e*|∞ ≥ Sw = 17`.
* `landing_dist`: the next family's landing root `r'` lies in another level-1 component than the exit block. So its
  offset from the exit cover is at least `J = 17`.
* `selected_sep`: selected blocks of different clusters are `≥ D` apart. With the separation inside each selection,
  all counted blocks are pairwise `D`-separated. That is what independence (`no_common_edge`) needs.
-/

namespace QECD1

/-- `a`-adjacency inside a set of flagged blocks. -/
def AdjIn (F : Finset V3) (a : ℕ) (x y : V3) : Prop := x ∈ F ∧ y ∈ F ∧ dist3 x y ≤ a

/-- Same `a`-component of `F`. -/
def SameComp (F : Finset V3) (a : ℕ) (x y : V3) : Prop := Relation.ReflTransGen (AdjIn F a) x y

/-- **Components are separated**: blocks of `F` in different `a`-components are more than `a` apart. -/
theorem comp_sep (F : Finset V3) (a : ℕ) {x y : V3} (hx : x ∈ F) (hy : y ∈ F) (hxy : ¬ SameComp F a x y) :
    a + 1 ≤ dist3 x y := by
  by_contra h
  exact hxy (Relation.ReflTransGen.single ⟨hx, hy, by omega⟩)

/-- `a`-components refine `a'`-components for `a ≤ a'`. -/
theorem comp_mono (F : Finset V3) {a a' : ℕ} (h : a ≤ a') {x y : V3} (hxy : SameComp F a x y) :
    SameComp F a' x y := by
  induction hxy with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hbc.2.1, le_trans hbc.2.2 h⟩

theorem sameComp_symm (F : Finset V3) (a : ℕ) {x y : V3} (hxy : SameComp F a x y) : SameComp F a y x := by
  induction hxy with
  | refl => exact .refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, by rw [dist3_comm]; exact hbc.2.2⟩ ih

/-- **Links lie in `S1`.** -/
theorem link_mem_S1 (F : Finset V3) {s b b' : V3} (hs : s ∈ F) (hb' : b' ∈ F)
    (hdiff : ¬ SameComp F Const.a0 s b') (hcov : dist3 b s ≤ Const.D - 1) (hbb' : dist3 b b' ≤ Const.a1) :
    b' - s ∈ S1off := by
  have hlow := comp_sep F Const.a0 hs hb' hdiff
  have hup := link_le_A1 s b b' (by unfold Covers; rw [linf_sub_comm]; exact hcov) hbb'
  rw [S1off_eq_const, Finset.mem_filter, mem_box]
  refine ⟨hup, ?_⟩
  have e : linf (b' - s) = dist3 s b' := by rw [dist3, linf_sub_comm]
  rw [e]
  simp only [Const.a0, Const.D_val] at hlow ⊢
  omega

/-- **Witness span** (Sw = 17), with the root `e` an actual block and the witness block `w` in another level-1
component. -/
theorem witness_span (F : Finset V3) {e sw w : V3} (he : e ∈ F) (hw : w ∈ F)
    (hdiff : ¬ SameComp F Const.a1 e w) (hcov : dist3 w sw ≤ Const.D - 1) : Const.Sw ≤ linf (sw - e) := by
  have hsep := comp_sep F Const.a1 he hw hdiff
  refine witness_ge_Sw e sw w ?_ ?_
  · rw [linf_sub_comm]
    exact hsep
  · unfold Covers
    rw [linf_sub_comm]
    exact hcov

/-- **Landing distance** (J = 17), with the landing root `r'` an actual block in another level-1 component than the
exit block `b`. -/
theorem landing_dist (F : Finset V3) {s b r' : V3} (hb : b ∈ F) (hr : r' ∈ F)
    (hdiff : ¬ SameComp F Const.a1 b r') (hcov : dist3 b s ≤ Const.D - 1) : Const.J ≤ linf (r' - s) := by
  have hsep := comp_sep F Const.a1 hb hr hdiff
  refine landing_ge_J s b r' ?_ ?_
  · unfold Covers
    rw [linf_sub_comm]
    exact hcov
  · rw [linf_sub_comm]
    exact hsep

/-- **Counted blocks of different clusters are `D`-separated** (`a0 + 1 = D`). -/
theorem selected_sep (F : Finset V3) {s s' : V3} (hs : s ∈ F) (hs' : s' ∈ F)
    (hdiff : ¬ SameComp F Const.a0 s s') : Const.D ≤ dist3 s s' := by
  have := comp_sep F Const.a0 hs hs' hdiff
  simp only [Const.a0, Const.D_val] at this ⊢
  omega

/-- `a0 + 1 = D`: the cluster separation equals the independence distance (no slack). -/
theorem a0_succ_eq_D : Const.a0 + 1 = Const.D := by
  rw [Const.D_val]
  rfl

end QECD1
