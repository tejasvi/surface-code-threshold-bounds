import QECD1.Excursion3

/-!
# The general family key (2D `fam_skeleton` with the encoding, 3D, dimension-free)

The hypotheses of the 3D deterministic lemma for one family:
* `F` the flagged blocks and `L ⊆ F` the level-1 blocks;
* a cluster chain `e → x` of the family, with landing root `e ∈ L` and exit `x ∈ L`;
* W0 at the level-1 roots;
* W1 for the level-1 component of `e` (`W1Hyp`).

`gen_key3` builds from them a valid family key of some axis. Its weight is the product of the token weights of the
route words around the mark, times `ε^{witLen}` for the witness.
* The route is the chain route of a shortest chain (`fam_segs_data`, `chain_route`).
* In case (A) of `fam_witness3` the witness is on the route, in the cluster of a pair `j`.
  * The mark sits at the last route vertex of the selected path to the cover of the witness block
    (`witness_branch`).
  * The walk's span reaches `Sw` along some axis (`witness_axis`).
* In case (B) the witness is off the route. It has three parts:
  * a selected walk from the route to the cover of the departure block;
  * a link (`link_mem_S1`);
  * the excursion word, which ends in `Asp` (`exc_route3`, `exc_word_asp`).

The leaf convention applies when the witness leaves from the root of a route part that is only
its root. Then the first block of the branch is that part's leaf, and the mark sits after it, at `C(z)`.
`gram_swap_leaf` shows the route word stays valid. An off-route witness leaving from the root itself, with an empty
walk, is marked at `B`, before the part's own leaf.

The route word is split around the mark in two steps:
* `chainToks_split`: the word before the witness cluster ends at `B`;
* `prefix_path_split`: the cluster's path splits at the mark.

Any such split with a valid witness is a valid key (`keyOK_of_split`, RouteWord3).
-/

namespace QECD1

open QECD1.Bld

/-- The number of `ε` factors of a witness: the walk's steps; for an off-route witness also the link and the
excursion's tokens. -/
def witLen : Wit → ℕ
  | .inl w => w.length
  | .inr x => x.1.length + 1 + x.2.2.length

theorem keyWt_eq (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok) :
    keyWt i (r1, wit, r2) = (fam3 i).wtPre 0 r1 * witW i ((fam3 i).stAfter 0 r1) wit *
      (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := rfl

theorem kind_eq_zero {m : ℕ} (h : kind m = 0) : m = 0 := by
  unfold kind at h
  split_ifs at h with h0 h34 <;> omega

/-- A route word that leaves the route grammar at `B` leaves every family automaton at `B`. -/
theorem fam3_stAfter_B (i : Fin 3) {A : List Tok} (hgA : route3.Gram 0 A) (hA : route3.stAfter 0 A = 0) :
    (fam3 i).stAfter 0 A = 0 := by
  obtain ⟨-, hk⟩ := kind_stAfter i A 0 (by norm_num) hgA
  exact kind_eq_zero (hk.trans hA)

theorem fam3_next_leaf (i : Fin 3) {m : ℕ} (hm : m < 52) (v : V3) :
    (fam3 i).next m (Tok.leaf v) = jIdx (coord i v) + 35 := by
  show famNext i m (Tok.leaf v) = _
  simp [famNext, hm, routeNext]

theorem zOf_leaf (i : Fin 3) {v : V3} (hv : v ∈ S0) : zOf (jIdx (coord i v) + 35) = coord i v := by
  have := coord_jIdx i v hv
  unfold zOf
  rw [if_neg (by omega), if_neg (by omega)]
  push_cast
  omega

/-- **The witness weight at a leaf state** `C(z)` is the walk's untilted weight when the witness condition holds. -/
theorem witW_leaf (i : Fin 3) {v : V3} (hv : v ∈ S0) (w : List V3)
    (hcond : Const.Sw ≤ (coord i v + (w.map (coord i)).sum).natAbs) :
    witW i (jIdx (coord i v) + 35) (Sum.inl w) = eps ^ w.length := by
  show (if jIdx (coord i v) + 35 = 34 then eps ^ w.length else witWt i (zOf (jIdx (coord i v) + 35)) w) = _
  rw [if_neg (by omega)]
  unfold witWt
  rw [zOf_leaf i hv, if_pos hcond, mul_one]

/-- **The weight of an off-route witness** is `ε^{witLen}` when the excursion ends in `Asp`. -/
theorem witW_off (i : Fin 3) (m : ℕ) (walk : List V3) (v : V3) (E : List Tok)
    (hE : (exc3 i).wt 0 E = eps ^ E.length) :
    witW i m (Sum.inr (walk, v, E)) = eps ^ witLen (Sum.inr (walk, v, E)) := by
  simp only [witW, offWt, witLen]
  rw [hE]
  ring

/-! ### Splitting the chain route at a cluster -/

theorem chainToks_cons_ne_nil (p : Seg) : ∀ (l : List Seg) (h : l ≠ []),
    chainToks (p :: l) = segToks p ++ Tok.link ((l.head h).root - segEnd p) :: chainToks l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem route3_stAfter_link (q : ℕ) (A : List Tok) (v : V3) (C : List Tok) :
    route3.stAfter q (A ++ Tok.link v :: C) = route3.stAfter 0 C := by
  rw [WA.stAfter_append]
  rfl

/-- **A chain route splits at any of its clusters**; the word before the cluster leaves the route grammar at `B`. -/
theorem chainToks_split : ∀ (pre : List Seg) (s : Seg) (post : List Seg),
    ∃ A C : List Tok, chainToks (pre ++ s :: post) = A ++ segToks s ++ C ∧ route3.stAfter 0 A = 0
  | [], s, [] => ⟨[], [], by simp [chainToks], rfl⟩
  | [], s, s' :: ss => ⟨[], Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss), by simp [chainToks], rfl⟩
  | p :: pre, s, post => by
    obtain ⟨A, C, hAC, hA⟩ := chainToks_split pre s post
    have hne : pre ++ s :: post ≠ [] := by simp
    refine ⟨segToks p ++ Tok.link (((pre ++ s :: post).head hne).root - segEnd p) :: A, C, ?_, ?_⟩
    · rw [List.cons_append, chainToks_cons_ne_nil p _ hne, hAC]
      simp
    · rw [route3_stAfter_link]
      exact hA

theorem pathToks_append : ∀ (cur : V3) (xs : List V3) (y : V3) (ys : List V3),
    pathToks cur (xs ++ y :: ys) = pathToks cur (xs ++ [y]) ++ pathToks y ys
  | _, [], _, _ => rfl
  | cur, x :: xs, y, ys => by
    show Tok.step (x - cur) :: pathToks x (xs ++ y :: ys) =
      Tok.step (x - cur) :: pathToks x (xs ++ [y]) ++ pathToks y ys
    rw [pathToks_append x xs y ys]
    rfl

/-- The path word splits at any vertex `r` into the prefix word (OnRouteKey) and the word after `r`. -/
theorem prefix_path_split {e r : V3} {P' pre post : List V3} (hsplit : e :: P' = pre ++ r :: post) :
    pathToks e P' = prefixToks e pre r ++ pathToks r post := by
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hsplit
    obtain ⟨hre, hP⟩ := hsplit
    subst hre
    subst hP
    rfl
  | cons a pre' =>
    simp only [List.cons_append, List.cons.injEq] at hsplit
    obtain ⟨_, hP'⟩ := hsplit
    rw [hP']
    show pathToks e (pre' ++ r :: post) = pathToks e (pre' ++ [r]) ++ pathToks r post
    exact pathToks_append e pre' r post

/-- The route grammar allows a leaf only at `B`. -/
theorem leaf_mem_rToks {q : ℕ} {u : V3} (h : Tok.leaf u ∈ rToks q) : q = 0 := by
  unfold rToks at h
  split_ifs at h with h0 h1
  · exact h0
  · simp at h
  · simp at h

/-- **Changing the leaf keeps a route word valid** (the leaf convention); the leaf sits at `B`. -/
theorem gram_swap_leaf {A C : List Tok} {u v : V3} (h : route3.Gram 0 (A ++ Tok.leaf u :: C)) (hv : v ∈ S0) :
    route3.Gram 0 (A ++ Tok.leaf v :: C) ∧ route3.stAfter 0 A = 0 := by
  rw [WA.gram_append] at h ⊢
  obtain ⟨hA, hl, hC⟩ := h
  have hq : route3.stAfter 0 A = 0 := leaf_mem_rToks hl
  refine ⟨⟨hA, ?_, hC⟩, hq⟩
  rw [hq]
  exact rToks_leaf v hv

/-! ### The key in one cluster of the route -/

/-- **An on-route key in a cluster of the route** (cases α, α'). The route word is `A ++ segToks s ++ C`, with `A`
ending at `B`. The witness block `w` is a level-1 block of another level-1 component than the cluster's root, which
is an actual block (R0), and its cover `sw` is selected. -/
theorem seg_key_onroute (F L : Finset V3) {s : Seg} {A C : List Tok}
    (hg : route3.Gram 0 (A ++ segToks s ++ C)) (hA : route3.stAfter 0 A = 0) (hsok : SegOK F s)
    {K : Finset V3} (hS : IsSelection3 K s.sel s.root Const.D Const.A0) (hroot : s.root ∈ L) {w sw : V3}
    (hw : w ∈ L) (hdiff : ¬ SameComp L Const.a1 s.root w) (hsw : sw ∈ s.sel)
    (hcov : dist3 w sw ≤ Const.D - 1) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := by
  obtain ⟨r, suf, hrP, _, _, hbch, hblast, _⟩ := witness_branch hS s.rest hsw
  have hspan := witness_span L hroot hw hdiff hcov
  obtain ⟨i, hcond⟩ := witness_axis s.root r sw suf hblast hspan
  have hgA : route3.Gram 0 A := by
    rw [List.append_assoc, WA.gram_append] at hg
    exact hg.1
  have hfA := fam3_stAfter_B i hgA hA
  have h0 : coord i (0 : V3) = 0 := by fin_cases i <;> rfl
  by_cases hrest : s.rest = []
  · -- a root-only part: the first branch block is the leaf, and the mark sits after it
    have hr : r = s.root := by
      rw [hrest] at hrP
      simpa using hrP
    subst hr
    cases suf with
    | nil =>
      exfalso
      simp only [diffs, List.map_nil, List.sum_nil, add_zero, sub_self] at hcond
      rw [h0, Const.Sw_val] at hcond
      simp at hcond
    | cons b1 suf' =>
      rw [List.isChain_cons_cons] at hbch
      obtain ⟨hadj, hbch'⟩ := hbch
      obtain ⟨hrS, hb1S, hne, hd⟩ := selGraph_adj.1 hadj
      have hv : b1 - s.root ∈ S0 := sep_step_mem_S0 hsok.sep hrS hb1S hne hd
      have hword : A ++ segToks s ++ C = A ++ Tok.leaf (s.leaf - s.root) :: C := by
        unfold segToks
        rw [if_pos hrest]
        simp
      rw [hword] at hg
      obtain ⟨hg', -⟩ := gram_swap_leaf hg hv
      refine ⟨i, A ++ [Tok.leaf (b1 - s.root)], Sum.inl (diffs b1 suf'), C, ?_, ?_⟩
      · refine keyOK_of_split i (by simpa using hg') ?_
        exact diffs_mem_S0 hsok.sep b1 suf' hbch'
      · rw [keyWt_eq]
        have hst : (fam3 i).stAfter 0 (A ++ [Tok.leaf (b1 - s.root)]) = jIdx (coord i (b1 - s.root)) + 35 := by
          rw [WA.stAfter_append, hfA]
          exact fam3_next_leaf i (by norm_num) _
        rw [hst, witW_leaf i hv]
        · rfl
        · -- the witness condition, from the branch's span
          simp only [diffs, List.map_cons, List.sum_cons, sub_self] at hcond
          rw [h0, zero_add] at hcond
          exact hcond
  · -- a path part: the mark sits on the path
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hrP
    have hseg : segToks s = pathToks s.root s.rest := by
      unfold segToks
      rw [if_neg hrest]
    have hword : A ++ segToks s ++ C = (A ++ prefixToks s.root pre r) ++ (pathToks r post ++ C) := by
      rw [hseg, prefix_path_split hsplit]
      simp
    rw [hword] at hg
    refine ⟨i, A ++ prefixToks s.root pre r, Sum.inl (diffs r suf), pathToks r post ++ C,
      keyOK_of_split i hg (diffs_mem_S0 hsok.sep r suf hbch), ?_⟩
    rw [keyWt_eq]
    obtain ⟨-, htr⟩ := prefix_props i hsok.sep hsplit hsok.chain
    have hst : (fam3 i).stAfter 0 (A ++ prefixToks s.root pre r) =
        (fam3 i).stAfter 0 (prefixToks s.root pre r) := by
      rw [WA.stAfter_append, hfA]
    rw [hst, witW_eq_of_tracks i htr (diffs r suf) hcond]
    rfl

/-- **An off-route key in a cluster of the route** (case β). The excursion `s1 :: ss` starts within `a1` of the
departure block `x0` of this cluster and lies in other clusters. Its last part spans at least `Sw` from its root. -/
theorem seg_key_offroute (F : Finset V3) {s : Seg} {A C : List Tok}
    (hg : route3.Gram 0 (A ++ segToks s ++ C)) (hA : route3.stAfter 0 A = 0) (hsok : SegOK F s)
    {K : Finset V3} (hS : IsSelection3 K s.sel s.root Const.D Const.A0)
    (hselc : ∀ q ∈ s.sel, SameComp F Const.a0 s.root q) {x0 sx : V3} (hsx : sx ∈ s.sel)
    (hcov : dist3 x0 sx ≤ Const.D - 1) {s1 sl : Seg} {ss : List Seg} (hd1 : dist3 x0 s1.root ≤ Const.a1)
    (hoff1 : ¬ SameComp F Const.a0 s.root s1.root) (hok : ∀ t ∈ s1 :: ss, SegOK F t)
    (hpw : (s1 :: ss).Pairwise (fun s s' => ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q))
    (hch : (s1 :: ss).IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1))
    (hsl : (s1 :: ss).getLast (List.cons_ne_nil _ _) = sl) (hspan : Const.Sw ≤ linf (segEnd sl - sl.root)) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := by
  -- the excursion word
  obtain ⟨hgE, -, -⟩ := chain_route F (s1 :: ss) hok hpw hch s1 rfl
  obtain ⟨i, hEg, hEw⟩ := exc_word_asp F s1 ss hok hgE hsl hspan
  -- the link from the cover of the departure block to the excursion's first root
  have hs1 := hok s1 List.mem_cons_self
  have hlink : s1.root - sx ∈ S1off :=
    link_mem_S1 F (hsok.sel_sub hsx) (hs1.sel_sub hs1.root_mem) (fun h => hoff1 ((hselc sx hsx).trans h)) hcov hd1
  have hwit : ∀ (walk : List V3), (∀ u ∈ walk, u ∈ S0) → ∀ m : ℕ,
      witValid i (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) ∧
      witW i m (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) =
        eps ^ witLen (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) :=
    fun walk hw m => ⟨⟨hw, hlink, hEg⟩, witW_off i m walk _ _ hEw⟩
  -- the walk from the route to the cover
  obtain ⟨r, suf, hrP, _, _, hbch, _, _⟩ := witness_branch hS s.rest hsx
  by_cases hrest : s.rest = []
  · have hr : r = s.root := by
      rw [hrest] at hrP
      simpa using hrP
    subst hr
    have hword : A ++ segToks s ++ C = A ++ Tok.leaf (s.leaf - s.root) :: C := by
      unfold segToks
      rw [if_pos hrest]
      simp
    cases suf with
    | nil =>
      -- the departure cover is the root: the mark sits at `B`, before the part's leaf
      obtain ⟨hv, hm⟩ := hwit [] (by simp) 0
      refine ⟨i, A, Sum.inr ([], s1.root - sx, chainToks (s1 :: ss)), segToks s ++ C, ?_, ?_⟩
      · refine keyOK_of_split i ?_ hv
        rw [← List.append_assoc]
        exact hg
      · rw [keyWt_eq]
        have hgA : route3.Gram 0 A := by
          rw [List.append_assoc, WA.gram_append] at hg
          exact hg.1
        rw [fam3_stAfter_B i hgA hA, hm]
    | cons b1 suf' =>
      -- the first branch block is the leaf, and the mark sits after it
      rw [List.isChain_cons_cons] at hbch
      obtain ⟨hadj, hbch'⟩ := hbch
      obtain ⟨hrS, hb1S, hne, hd⟩ := selGraph_adj.1 hadj
      have hv : b1 - s.root ∈ S0 := sep_step_mem_S0 hsok.sep hrS hb1S hne hd
      rw [hword] at hg
      obtain ⟨hg', -⟩ := gram_swap_leaf hg hv
      obtain ⟨hvw, hm⟩ := hwit (diffs b1 suf') (diffs_mem_S0 hsok.sep b1 suf' hbch')
        ((fam3 i).stAfter 0 (A ++ [Tok.leaf (b1 - s.root)]))
      refine ⟨i, A ++ [Tok.leaf (b1 - s.root)], Sum.inr (diffs b1 suf', s1.root - sx, chainToks (s1 :: ss)), C,
        keyOK_of_split i (by simpa using hg') hvw, ?_⟩
      rw [keyWt_eq, hm]
  · -- a path part: the mark sits on the path
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hrP
    have hseg : segToks s = pathToks s.root s.rest := by
      unfold segToks
      rw [if_neg hrest]
    have hword : A ++ segToks s ++ C = (A ++ prefixToks s.root pre r) ++ (pathToks r post ++ C) := by
      rw [hseg, prefix_path_split hsplit]
      simp
    rw [hword] at hg
    obtain ⟨hvw, hm⟩ := hwit (diffs r suf) (diffs_mem_S0 hsok.sep r suf hbch)
      ((fam3 i).stAfter 0 (A ++ prefixToks s.root pre r))
    refine ⟨i, A ++ prefixToks s.root pre r, Sum.inr (diffs r suf, s1.root - sx, chainToks (s1 :: ss)),
      pathToks r post ++ C, keyOK_of_split i hg hvw, ?_⟩
    rw [keyWt_eq, hm]

/-! ### The general key -/

/-- **The general family key.** For a family with landing root `e ∈ L`, a cluster chain to its exit `x ∈ L`, W0 at
the level-1 roots and W1, some axis has a valid family key. Its weight is the token weights of the route words
around the mark times `ε^{witLen}`. -/
theorem gen_key3 (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} (he : e ∈ L) (hx : x ∈ L)
    (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f)
    (hW0 : ∀ r ∈ L, ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) (hW1 : W1Hyp F L e) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 := by
  obtain ⟨n, f, hf, hdist⟩ := exists_min_fchain3 F L hex
  obtain ⟨seg, hseg, -, hok, hpw, hch⟩ :=
    fam_segs_data F L hf hdist (fun j hj => hW0 _ (chain_roots_mem hf he j hj))
  have hhead : seg 0 ∈ ((List.range (n + 1)).map seg).head? := by
    simp [List.range_succ_eq_map]
  obtain ⟨hgR, -, -⟩ := chain_route F _ hok hpw hch (seg 0) hhead
  -- the route word splits at the cluster of any pair `j`
  have hsplitj : ∀ j ≤ n, ∃ A C : List Tok,
      route3.Gram 0 (A ++ segToks (seg j) ++ C) ∧ route3.stAfter 0 A = 0 := by
    intro j hj
    have hmem : seg j ∈ (List.range (n + 1)).map seg := List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨pre, post, hsp⟩ := List.append_of_mem hmem
    obtain ⟨A, C, hAC, hA⟩ := chainToks_split pre (seg j) post
    refine ⟨A, C, ?_, hA⟩
    rw [← hAC, ← hsp]
    exact hgR
  rcases fam_witness3 F L hf hx hW1 with ⟨j, hj, w, hwL, hwc, hwd⟩ | ⟨-, c, hcL, hoff, ⟨k, hk, hck⟩, hfar⟩
  · -- (A): the witness is on the route
    obtain ⟨hroot, -, -, hsok, hS, hcovS⟩ := hseg j hj
    obtain ⟨A, C, hg, hA⟩ := hsplitj j hj
    obtain ⟨sw, hsw, hwsw⟩ := hcovS w (mem_clusterOf.2 ⟨hLF hwL, hwc⟩)
    have hrootL : (seg j).root ∈ L := hroot ▸ chain_roots_mem hf he j hj
    rw [← hroot] at hS hwd
    exact seg_key_onroute F L hg hA hsok hS hrootL hwL hwd hsw hwsw
  · -- (B): the witness is an excursion
    obtain ⟨jx, x0, esegs, hjx, hx0L, hx0c, hfirst, heok, hepw, hech, heoff, sl, hsl, hspan⟩ :=
      exc_route3 F L hLF hf he hcL hoff hk hck hfar hW0
    obtain ⟨hroot, -, hsub, hsok, hS, hcovS⟩ := hseg jx hjx
    obtain ⟨A, C, hg, hA⟩ := hsplitj jx hjx
    obtain ⟨sx, hsx, hx0sx⟩ := hcovS x0 (mem_clusterOf.2 ⟨hLF hx0L, hx0c⟩)
    cases esegs with
    | nil => simp at hsl
    | cons s1 ss =>
      obtain ⟨hd1, -⟩ := hfirst s1 rfl
      have hselc : ∀ q ∈ (seg jx).sel, SameComp F Const.a0 (seg jx).root q := by
        intro q hq
        rw [hroot]
        exact (mem_clusterOf.1 (hsub hq)).2
      have hoff1 : ¬ SameComp F Const.a0 (seg jx).root s1.root := by
        rw [hroot]
        exact heoff s1 List.mem_cons_self s1.root (heok s1 List.mem_cons_self).root_mem jx hjx
      have hsl' : (s1 :: ss).getLast (List.cons_ne_nil _ _) = sl := by
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hsl
        exact Option.some.inj hsl
      rw [← hroot] at hS
      exact seg_key_offroute F hg hA hsok hS hselc hsx hx0sx hd1 hoff1 heok hepw hech hsl' hspan

end QECD1
