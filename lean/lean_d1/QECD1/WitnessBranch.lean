import QECD1.SkelRoute

/-!
# The on-route witness branch

This is the 3D, dimension-free version of the 2D `branch_split` / `sel_branch` (TwoD/T2Skel). In the witness
part, the route is a simple path `P` of the selection from the part's root `e*` (an actual odd block, R0) to the end
of the part. The witness block `w` is a block of the part from another level-1 component, and its cover `sw` is a
selected block. Take a simple path `Q` of the selection from `e*` to `sw`, and let `r` be its last vertex on `P`.
Then:
* `r` lies on the route: it is the mark position;
* the rest of `Q` after `r` is a walk of the selection that avoids `P`. It is the witness walk, and its counted blocks
  are disjoint from the route's;
* its steps are `S0` offsets (`diffs_mem_S0`), and the route displacement at `r` plus the walk's displacement is
  `sw - e*`.

By `witness_span`, `|sw - e*|∞ ≥ Sw`, so along some axis `i` the witness condition `Sw ≤ |z_i + Σ w_i|` of `witWt`
holds (`witness_axis`).

* `split_last`: a list meeting `P` splits as `pre ++ r :: suf`, with `r ∈ P` and `suf` disjoint from `P`.
* `diffs`, `diffs_sum`, `diffs_mem_S0`: consecutive differences, their telescoping sum, and their membership in `S0`.
* `witness_branch`: the branch exists for any selected `sw`.
* `witness_axis`: the witness condition along some axis.
-/

namespace QECD1

/-- **Last vertex on `P`.** -/
theorem split_last (P : List V3) : ∀ Q : List V3, (∃ x ∈ Q, x ∈ P) →
    ∃ pre r suf, Q = pre ++ r :: suf ∧ r ∈ P ∧ ∀ y ∈ suf, y ∉ P
  | [], h => by simp at h
  | q :: Q, h => by
    by_cases hQ : ∃ x ∈ Q, x ∈ P
    · obtain ⟨pre, r, suf, hsplit, hr, hsuf⟩ := split_last P Q hQ
      exact ⟨q :: pre, r, suf, by rw [hsplit]; rfl, hr, hsuf⟩
    · refine ⟨[], q, Q, rfl, ?_, fun y hy hyP => hQ ⟨y, hy, hyP⟩⟩
      obtain ⟨x, hx, hxP⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hxP
      · exact absurd ⟨x, hx', hxP⟩ hQ

/-- Consecutive differences of a walk from `cur`. -/
def diffs : V3 → List V3 → List V3
  | _, [] => []
  | cur, b :: bs => (b - cur) :: diffs b bs

theorem diffs_sum : ∀ (cur : V3) (bs : List V3), (diffs cur bs).sum = (cur :: bs).getLast (List.cons_ne_nil _ _) - cur
  | cur, [] => by simp [diffs]
  | cur, b :: bs => by
    simp only [diffs, List.sum_cons]
    rw [diffs_sum b bs, List.getLast_cons (List.cons_ne_nil _ _)]
    abel

theorem diffs_mem_S0 {S : Finset V3} (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q) :
    ∀ (cur : V3) (bs : List V3), List.IsChain (selGraph S Const.A0).Adj (cur :: bs) → ∀ v ∈ diffs cur bs, v ∈ S0
  | _, [], _ => by simp [diffs]
  | cur, b :: bs, hch => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hadj, hrest⟩ := hch
    obtain ⟨hc, hb, hne, hd⟩ := selGraph_adj.1 hadj
    intro v hv
    simp only [diffs, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact sep_step_mem_S0 hsep hc hb hne hd
    · exact diffs_mem_S0 hsep b bs hrest v hv

/-- Reachability in the selection graph is symmetric, so a simple path exists between any two selected blocks
reachable from the root. -/
theorem exists_sel_path_from {K S : Finset V3} {e : V3} {D A : ℕ} (hS : IsSelection3 K S e D A) {s : V3}
    (hs : s ∈ S) :
    ∃ rest : List V3, (e :: rest).Nodup ∧ List.IsChain (selGraph S A).Adj (e :: rest) ∧
      (e :: rest).getLast (List.cons_ne_nil _ _) = s :=
  exists_sel_path hS hs

/-- **The witness branch.** `P = e :: P'` is the route path in the selection, and `sw` any selected block. There is
a vertex `r` of the route and a walk `r :: suf` of the selection to `sw` whose blocks after `r` avoid the route. -/
theorem witness_branch {K S : Finset V3} {e : V3} (hS : IsSelection3 K S e Const.D Const.A0) (P' : List V3)
    {sw : V3} (hsw : sw ∈ S) :
    ∃ r suf, r ∈ e :: P' ∧ (∀ y ∈ suf, y ∉ e :: P') ∧ (r :: suf).Nodup ∧
      List.IsChain (selGraph S Const.A0).Adj (r :: suf) ∧
      (r :: suf).getLast (List.cons_ne_nil _ _) = sw ∧ r ∈ S := by
  obtain ⟨Q, hnd, hch, hlast⟩ := exists_sel_path hS hsw
  obtain ⟨pre, r, suf, hsplit, hr, hsuf⟩ :=
    split_last (e :: P') (e :: Q) ⟨e, List.mem_cons_self, List.mem_cons_self⟩
  refine ⟨r, suf, hr, hsuf, ?_, ?_, ?_, ?_⟩
  · rw [hsplit] at hnd
    exact List.Nodup.of_append_right hnd
  · rw [hsplit] at hch
    exact List.IsChain.right_of_append hch
  · have h1 : (e :: Q).getLast (List.cons_ne_nil _ _) = (pre ++ r :: suf).getLast (by simp) := by
      congr 1
    rw [← hlast, h1, List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)]
  · -- every vertex of the selection path is selected
    have hmem : r ∈ e :: Q := by rw [hsplit]; simp
    have key : ∀ (a : V3) (l : List V3), a ∈ S → List.IsChain (selGraph S Const.A0).Adj (a :: l) → ∀ x ∈ a :: l, x ∈ S := by
      intro a l
      induction l generalizing a with
      | nil => intro ha _ x hx; simp at hx; rw [hx]; exact ha
      | cons y ys ih =>
        intro ha hc x hx
        rw [List.isChain_cons_cons] at hc
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ha
        · exact ih y (selGraph_adj.1 hc.1).2.1 hc.2 x hx'
    exact key e Q hS.2.1 hch r hmem

/-- **The witness condition along some axis.** If `|sw - e|∞ ≥ Sw` (`witness_span`), the route displacement
`r - e` at the mark plus the walk's displacement meets `Sw` along some axis. -/
theorem witness_axis (e r sw : V3) (suf : List V3) (hlast : (r :: suf).getLast (List.cons_ne_nil _ _) = sw)
    (hspan : Const.Sw ≤ linf (sw - e)) :
    ∃ i : Fin 3, Const.Sw ≤ (coord i (r - e) + ((diffs r suf).map (coord i)).sum).natAbs := by
  have hsum : (diffs r suf).sum = sw - r := by rw [diffs_sum, hlast]
  have hcoord : ∀ i : Fin 3, ((diffs r suf).map (coord i)).sum = coord i (diffs r suf).sum := by
    intro i
    generalize diffs r suf = l
    induction l with
    | nil => fin_cases i <;> rfl
    | cons v l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      fin_cases i <;> simp [coord]
  have htot : ∀ i : Fin 3, coord i (r - e) + ((diffs r suf).map (coord i)).sum = coord i (sw - e) := by
    intro i
    rw [hcoord, hsum]
    fin_cases i <;> simp [coord] <;> ring
  simp only [linf, le_max_iff] at hspan
  rcases hspan with h | h | h
  · exact ⟨0, by rw [htot]; simpa [coord] using h⟩
  · exact ⟨1, by rw [htot]; simpa [coord] using h⟩
  · exact ⟨2, by rw [htot]; simpa [coord] using h⟩

end QECD1
