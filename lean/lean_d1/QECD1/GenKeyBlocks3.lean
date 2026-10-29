import QECD1.KeyBlocks3

/-!
# The general family key with its skeleton blocks

`gen_key3_blocks` strengthens `gen_key3`: the key's counted blocks (`keyBlocks`, read from the landing root) are
pairwise `D`-separated flagged blocks. With `keyBlocks_length` (one block per `ε` factor of `keyWt`, plus the root)
this is what the probability side needs:
* the blocks are flagged, so each costs `ε` (H_eps);
* they are `D`-separated, so independent (`no_common_edge`);
* they are read from the key and the root, so the encoding is injective.

The route is split explicitly (`preToks`, `postToks`). The key's blocks are then compared with the route's, the
branch's and the excursion's blocks (`keyBlocks_perm_of_route`, `keyBlocks_leaf`, `witBlocks_off`), and separated by
`skeleton_sep`.
-/

namespace QECD1

open QECD1.Bld

theorem head_mem_split (pre post : List Seg) (s : Seg) : ∃ s0, s0 ∈ (pre ++ s :: post).head? := by
  cases pre with
  | nil => exact ⟨s, rfl⟩
  | cons p _ => exact ⟨p, rfl⟩

/-- Localization of the route blocks when the branch avoids the witness part's own route blocks. -/
theorem route_loc {F : Finset V3} {pre post : List Seg} {s : Seg} (hok : ∀ t ∈ pre ++ s :: post, SegOK F t)
    {suf : List V3} (havoid : ∀ a ∈ s.root :: segBlocks s, a ∉ suf) :
    ∀ a ∈ chainBlocks (pre ++ s :: post), (∃ t ∈ pre ++ post, a ∈ t.sel) ∨ (a ∈ s.sel ∧ a ∉ suf) := by
  have hsok := hok s (List.mem_append_right _ List.mem_cons_self)
  intro a ha
  rw [chainBlocks_append] at ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨t, ht, hat⟩ := chainBlocks_mem_sel pre (fun t ht => hok t (List.mem_append_left _ ht)) a h
    exact Or.inl ⟨t, List.mem_append_left _ ht, hat⟩
  · simp only [chainBlocks, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr ⟨segBlocks_sub hsok a h, havoid a h⟩
    · obtain ⟨t, ht, hat⟩ := chainBlocks_mem_sel post
        (fun t ht => hok t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))) a h
      exact Or.inl ⟨t, List.mem_append_right _ ht, hat⟩

/-- Localization of the route blocks in the leaf convention (the part's own leaf removed). -/
theorem route_loc_leaf {F : Finset V3} {pre post : List Seg} {s : Seg} (hok : ∀ t ∈ pre ++ s :: post, SegOK F t)
    {suf : List V3} (havoid : s.root ∉ suf) :
    ∀ a ∈ chainBlocks pre ++ [s.root] ++ chainBlocks post,
      (∃ t ∈ pre ++ post, a ∈ t.sel) ∨ (a ∈ s.sel ∧ a ∉ suf) := by
  have hsok := hok s (List.mem_append_right _ List.mem_cons_self)
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨t, ht, hat⟩ := chainBlocks_mem_sel pre (fun t ht => hok t (List.mem_append_left _ ht)) a h
      exact Or.inl ⟨t, List.mem_append_left _ ht, hat⟩
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inr ⟨hsok.root_mem, havoid⟩
  · obtain ⟨t, ht, hat⟩ := chainBlocks_mem_sel post
      (fun t ht => hok t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))) a h
    exact Or.inl ⟨t, List.mem_append_right _ ht, hat⟩

/-- In the leaf convention the route's blocks without the part's own leaf are a sublist of the chain's blocks. -/
theorem leaf_route_sublist {pre post : List Seg} {s : Seg} (hrest : s.rest = []) :
    (chainBlocks pre ++ [s.root] ++ chainBlocks post).Sublist (chainBlocks (pre ++ s :: post)) := by
  have hb : segBlocks s = [s.leaf] := by
    unfold segBlocks
    rw [if_pos hrest]
  rw [chainBlocks_append]
  show (chainBlocks pre ++ [s.root] ++ chainBlocks post).Sublist
    (chainBlocks pre ++ ((s.root :: segBlocks s) ++ chainBlocks post))
  rw [hb, List.append_assoc]
  exact List.Sublist.append_left (List.Sublist.cons_cons s.root (List.sublist_cons_self s.leaf _)) _

/-- A chain route ends after a step or a leaf, never at `B`. -/
theorem route3_stAfter_chainToks_pos {F : Finset V3} :
    ∀ (s : Seg) (ss : List Seg), (∀ t ∈ s :: ss, SegOK F t) → 1 ≤ route3.stAfter 0 (chainToks (s :: ss))
  | s, [], hok => (segToks_gram (hok s List.mem_cons_self)).2
  | s, s' :: ss, hok => by
    show 1 ≤ route3.stAfter 0 (segToks s ++ Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss))
    rw [route3_stAfter_link]
    exact route3_stAfter_chainToks_pos s' ss (fun t ht => hok t (List.mem_cons_of_mem _ ht))

theorem route3_stAfter_split_pos {F : Finset V3} {pre post : List Seg} {s : Seg}
    (hok : ∀ t ∈ pre ++ s :: post, SegOK F t) : 1 ≤ route3.stAfter 0 (chainToks (pre ++ s :: post)) := by
  cases pre with
  | nil => exact route3_stAfter_chainToks_pos s post hok
  | cons p pre' => exact route3_stAfter_chainToks_pos p (pre' ++ s :: post) hok

/-- The route grammar's state after a word does not depend on a leaf's offset. -/
theorem route3_stAfter_swap_leaf (A C : List Tok) (u v : V3) :
    route3.stAfter 0 (A ++ Tok.leaf v :: C) = route3.stAfter 0 (A ++ Tok.leaf u :: C) := by
  rw [WA.stAfter_append, WA.stAfter_append]
  rfl

/-- In the leaf convention the route word still ends after a step or a leaf. -/
theorem route3_stAfter_leaf_pos {F : Finset V3} {pre post : List Seg} {s : Seg}
    (hok : ∀ t ∈ pre ++ s :: post, SegOK F t) (hrest : s.rest = []) (b1 : V3) :
    1 ≤ route3.stAfter 0 ((preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) ++ postToks s post) := by
  have h := route3_stAfter_split_pos hok
  have hword : preToks pre s.root ++ segToks s ++ postToks s post =
      preToks pre s.root ++ Tok.leaf (s.leaf - s.root) :: postToks s post := by
    unfold segToks
    rw [if_pos hrest]
    simp
  rw [chainToks_pre_post, hword, route3_stAfter_swap_leaf _ _ (b1 - s.root) (s.leaf - s.root)] at h
  rw [List.append_assoc, List.singleton_append]
  exact h

/-- **The route of a chain ends at the end of its last cluster's path**, which covers the last exit. -/
theorem endOf_chainToks_last : ∀ (s : Seg) (ss : List Seg) (t : Seg), (s :: ss).getLast? = some t →
    endOf s.root (chainToks (s :: ss)) = segEnd t
  | s, [], t, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact segToks_end s
  | s, s' :: ss, t, h => by
    show endOf s.root (segToks s ++ Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss)) = segEnd t
    rw [endOf_append, segToks_end]
    show endOf (segEnd s + (s'.root - segEnd s)) (chainToks (s' :: ss)) = segEnd t
    rw [add_sub_cancel]
    exact endOf_chainToks_last s' ss t (by rw [List.getLast?_cons_cons] at h; exact h)

theorem endOf_split_last {pre post : List Seg} {s t : Seg} (h : (pre ++ s :: post).getLast? = some t) :
    endOf (firstRoot pre s.root) (chainToks (pre ++ s :: post)) = segEnd t := by
  cases pre with
  | nil => exact endOf_chainToks_last s post t h
  | cons p pre' => exact endOf_chainToks_last p (pre' ++ s :: post) t h

/-- A leaf does not move the route. -/
theorem endOf_swap_leaf (cur : V3) (A C : List Tok) (u v : V3) :
    endOf cur (A ++ Tok.leaf v :: C) = endOf cur (A ++ Tok.leaf u :: C) := by
  rw [endOf_append, endOf_append]
  rfl

/-- In the leaf convention the route still ends where the chain route ends. -/
theorem endOf_leaf_route {pre post : List Seg} {s : Seg} (hrest : s.rest = []) (b1 : V3) :
    endOf (firstRoot pre s.root) ((preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) ++ postToks s post) =
      endOf (firstRoot pre s.root) (chainToks (pre ++ s :: post)) := by
  have hword : preToks pre s.root ++ segToks s ++ postToks s post =
      preToks pre s.root ++ Tok.leaf (s.leaf - s.root) :: postToks s post := by
    unfold segToks
    rw [if_pos hrest]
    simp
  rw [chainToks_pre_post, hword, List.append_assoc, List.singleton_append,
    endOf_swap_leaf _ _ _ (s.leaf - s.root) (b1 - s.root)]

/-! ### The key in one cluster, with its blocks -/

/-- **An on-route key in a cluster of the route, with its skeleton blocks** (cases α, α'). -/
theorem seg_key_onroute2 (F L : Finset V3) {pre post : List Seg} {s : Seg}
    (hok : ∀ t ∈ pre ++ s :: post, SegOK F t) (hpw : (pre ++ s :: post).Pairwise (SegApart F))
    (hch : (pre ++ s :: post).IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1))
    {K : Finset V3} (hS : IsSelection3 K s.sel s.root Const.D Const.A0) (hroot : s.root ∈ L) {w sw : V3}
    (hw : w ∈ L) (hdiff : ¬ SameComp L Const.a1 s.root w) (hsw : sw ∈ s.sel)
    (hcov : dist3 w sw ≤ Const.D - 1) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 ∧
      1 ≤ route3.stAfter 0 (r1 ++ r2) ∧
      endOf (firstRoot pre s.root) (r1 ++ r2) = endOf (firstRoot pre s.root) (chainToks (pre ++ s :: post)) ∧
      (keyBlocks (firstRoot pre s.root) (r1, wit, r2)).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      ∀ b ∈ keyBlocks (firstRoot pre s.root) (r1, wit, r2), b ∈ F := by
  have hs : s ∈ pre ++ s :: post := List.mem_append_right _ List.mem_cons_self
  have hsok := hok s hs
  obtain ⟨s0, hs0⟩ := head_mem_split pre post s
  obtain ⟨hgR, -, hsepR⟩ := chain_route F (pre ++ s :: post) hok hpw hch s0 hs0
  have hg : route3.Gram 0 (preToks pre s.root ++ segToks s ++ postToks s post) := by
    rw [← chainToks_pre_post]
    exact hgR
  have hA := route3_stAfter_preToks pre s.root
  obtain ⟨r, suf, hrP, hsufP, hbnd, hbch, hblast, _⟩ := witness_branch hS s.rest hsw
  have hsufS : ∀ b ∈ suf, b ∈ s.sel := chain_mem_sel r suf hbch
  have hsufnd : suf.Nodup := (List.nodup_cons.1 hbnd).2
  have hspan := witness_span L hroot hw hdiff hcov
  obtain ⟨i, hcond⟩ := witness_axis s.root r sw suf hblast hspan
  have hgA : route3.Gram 0 (preToks pre s.root) := by
    have h := hg
    rw [List.append_assoc, WA.gram_append] at h
    exact h.1
  have hfA := fam3_stAfter_B i hgA hA
  have h0 : coord i (0 : V3) = 0 := by fin_cases i <;> rfl
  by_cases hrest : s.rest = []
  · -- a root-only part: the leaf convention
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
      have hrootnot : s.root ∉ b1 :: suf' := fun h => hsufP s.root h List.mem_cons_self
      rw [List.isChain_cons_cons] at hbch
      obtain ⟨hadj, hbch'⟩ := hbch
      obtain ⟨hrS, hb1S, hne, hd⟩ := selGraph_adj.1 hadj
      have hv : b1 - s.root ∈ S0 := sep_step_mem_S0 hsok.sep hrS hb1S hne hd
      have hword : preToks pre s.root ++ segToks s ++ postToks s post =
          preToks pre s.root ++ Tok.leaf (s.leaf - s.root) :: postToks s post := by
        unfold segToks
        rw [if_pos hrest]
        simp
      rw [hword] at hg
      obtain ⟨hg', -⟩ := gram_swap_leaf hg hv
      refine ⟨i, preToks pre s.root ++ [Tok.leaf (b1 - s.root)], Sum.inl (diffs b1 suf'), postToks s post,
        keyOK_of_split i (by simpa using hg') (diffs_mem_S0 hsok.sep b1 suf' hbch'), ?_,
        route3_stAfter_leaf_pos hok hrest b1, endOf_leaf_route hrest b1, ?_⟩
      · rw [keyWt_eq]
        have hst : (fam3 i).stAfter 0 (preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) =
            jIdx (coord i (b1 - s.root)) + 35 := by
          rw [WA.stAfter_append, hfA]
          exact fam3_next_leaf i (by norm_num) _
        rw [hst, witW_leaf i hv]
        · rfl
        · simp only [diffs, List.map_cons, List.sum_cons, sub_self] at hcond
          rw [h0, zero_add] at hcond
          exact hcond
      · -- the blocks: the route without the part's leaf, then the branch
        have hperm := keyBlocks_leaf (pre := pre) (post := post) hrest b1 (Sum.inl (diffs b1 suf'))
        have hwb : witBlocks b1 (Sum.inl (diffs b1 suf')) = suf' := walkBlocks_diffs b1 suf'
        rw [hwb] at hperm
        obtain ⟨hsep, hF⟩ := skeleton_sep F (esegs := []) (X := []) hok hpw (fun t ht => by simp at ht)
          (fun t _ t' ht' => by simp at ht') (hsepR.sublist (leaf_route_sublist hrest))
          (route_loc_leaf hok hrootnot) hsufS hsufnd List.Pairwise.nil (fun c hc => by simp at hc)
        rw [List.append_nil] at hsep hF
        exact ⟨(List.Perm.pairwise_iff (fun h => sep_symm h) hperm).2 hsep, fun b hb => hF b (hperm.mem_iff.1 hb)⟩
  · -- a path part: the mark sits on the path
    obtain ⟨pre', post', hsplit⟩ := List.append_of_mem hrP
    have hseg : segToks s = pathToks s.root s.rest := by
      unfold segToks
      rw [if_neg hrest]
    have h12 : (preToks pre s.root ++ prefixToks s.root pre' r) ++ (pathToks r post' ++ postToks s post) =
        chainToks (pre ++ s :: post) := by
      rw [chainToks_pre_post, hseg, prefix_path_split hsplit]
      simp
    refine ⟨i, preToks pre s.root ++ prefixToks s.root pre' r, Sum.inl (diffs r suf),
      pathToks r post' ++ postToks s post, keyOK_of_split i (h12 ▸ hgR) (diffs_mem_S0 hsok.sep r suf hbch), ?_,
      h12 ▸ route3_stAfter_split_pos hok, by rw [h12], ?_⟩
    · rw [keyWt_eq]
      obtain ⟨-, htr⟩ := prefix_props i hsok.sep hsplit hsok.chain
      have hst : (fam3 i).stAfter 0 (preToks pre s.root ++ prefixToks s.root pre' r) =
          (fam3 i).stAfter 0 (prefixToks s.root pre' r) := by
        rw [WA.stAfter_append, hfA]
      rw [hst, witW_eq_of_tracks i htr (diffs r suf) hcond]
      rfl
    · -- the blocks: the route, then the branch
      have hperm := keyBlocks_perm_of_route (route_blocks_split pre post s) h12 (Sum.inl (diffs r suf))
      have hmp : markPos (firstRoot pre s.root) (preToks pre s.root ++ prefixToks s.root pre' r) = r := by
        rw [markPos_of_not_leaf (noLeaf_append (preToks_noLeaf pre s.root)
          (noLeaf_of_steps (prefixToks_steps s.root r pre'))), endOf_append, endOf_preToks, prefix_end hsplit]
      have hwb : witBlocks r (Sum.inl (diffs r suf)) = suf := walkBlocks_diffs r suf
      rw [hmp, hwb] at hperm
      have hsb : segBlocks s = s.rest := by
        unfold segBlocks
        rw [if_neg hrest]
      have havoid : ∀ a ∈ s.root :: segBlocks s, a ∉ suf := by
        rw [hsb]
        exact fun a ha hsuf => hsufP a hsuf ha
      obtain ⟨hsep, hF⟩ := skeleton_sep F (esegs := []) (X := []) hok hpw (fun t ht => by simp at ht)
        (fun t _ t' ht' => by simp at ht') hsepR (route_loc hok havoid) hsufS hsufnd List.Pairwise.nil
        (fun c hc => by simp at hc)
      rw [List.append_nil] at hsep hF
      exact ⟨(List.Perm.pairwise_iff (fun h => sep_symm h) hperm).2 hsep, fun b hb => hF b (hperm.mem_iff.1 hb)⟩

/-- **An off-route key in a cluster of the route, with its skeleton blocks** (case β). -/
theorem seg_key_offroute2 (F : Finset V3) {pre post : List Seg} {s : Seg}
    (hok : ∀ t ∈ pre ++ s :: post, SegOK F t) (hpw : (pre ++ s :: post).Pairwise (SegApart F))
    (hch : (pre ++ s :: post).IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1))
    {K : Finset V3} (hS : IsSelection3 K s.sel s.root Const.D Const.A0) {x0 sx : V3} (hsx : sx ∈ s.sel)
    (hcov : dist3 x0 sx ≤ Const.D - 1) {s1 sl : Seg} {ss : List Seg} (hd1 : dist3 x0 s1.root ≤ Const.a1)
    (heok : ∀ t ∈ s1 :: ss, SegOK F t) (hepw : (s1 :: ss).Pairwise (SegApart F))
    (hech : (s1 :: ss).IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1))
    (hoff : ∀ t ∈ pre ++ s :: post, ∀ t' ∈ s1 :: ss, SegApart F t t')
    (hsl : (s1 :: ss).getLast (List.cons_ne_nil _ _) = sl) (hspan : Const.Sw ≤ linf (segEnd sl - sl.root)) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 ∧
      1 ≤ route3.stAfter 0 (r1 ++ r2) ∧
      endOf (firstRoot pre s.root) (r1 ++ r2) = endOf (firstRoot pre s.root) (chainToks (pre ++ s :: post)) ∧
      (keyBlocks (firstRoot pre s.root) (r1, wit, r2)).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      ∀ b ∈ keyBlocks (firstRoot pre s.root) (r1, wit, r2), b ∈ F := by
  have hs : s ∈ pre ++ s :: post := List.mem_append_right _ List.mem_cons_self
  have hsok := hok s hs
  obtain ⟨s0, hs0⟩ := head_mem_split pre post s
  obtain ⟨hgR, -, hsepR⟩ := chain_route F (pre ++ s :: post) hok hpw hch s0 hs0
  have hg : route3.Gram 0 (preToks pre s.root ++ segToks s ++ postToks s post) := by
    rw [← chainToks_pre_post]
    exact hgR
  have hA := route3_stAfter_preToks pre s.root
  -- the excursion word
  obtain ⟨hgE, -, hsepE⟩ := chain_route F (s1 :: ss) heok hepw hech s1 rfl
  obtain ⟨i, hEg, hEw⟩ := exc_word_asp F s1 ss heok hgE hsl hspan
  have hs1 := heok s1 List.mem_cons_self
  have hlink : s1.root - sx ∈ S1off :=
    link_mem_S1 F (hsok.sel_sub hsx) (hs1.sel_sub hs1.root_mem)
      (hoff s hs s1 List.mem_cons_self sx hsx s1.root hs1.root_mem) hcov hd1
  have hwit : ∀ (walk : List V3), (∀ u ∈ walk, u ∈ S0) → ∀ m : ℕ,
      witValid i (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) ∧
      witW i m (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) =
        eps ^ witLen (Sum.inr (walk, s1.root - sx, chainToks (s1 :: ss))) :=
    fun walk hw m => ⟨⟨hw, hlink, hEg⟩, witW_off i m walk _ _ hEw⟩
  have hXloc := chainBlocks_mem_sel (s1 :: ss) heok
  -- the walk from the route to the cover of the departure block
  obtain ⟨r, suf, hrP, hsufP, hbnd, hbch, hblast, _⟩ := witness_branch hS s.rest hsx
  have hsufS : ∀ b ∈ suf, b ∈ s.sel := chain_mem_sel r suf hbch
  have hsufnd : suf.Nodup := (List.nodup_cons.1 hbnd).2
  have hgA : route3.Gram 0 (preToks pre s.root) := by
    have h := hg
    rw [List.append_assoc, WA.gram_append] at h
    exact h.1
  by_cases hrest : s.rest = []
  · have hr : r = s.root := by
      rw [hrest] at hrP
      simpa using hrP
    subst hr
    cases suf with
    | nil =>
      -- the departure cover is the root: the mark sits at `B`, before the part's leaf
      obtain ⟨hv, hm⟩ := hwit (diffs s.root []) (by simp [diffs]) 0
      have h12 : preToks pre s.root ++ (segToks s ++ postToks s post) = chainToks (pre ++ s :: post) := by
        rw [chainToks_pre_post, List.append_assoc]
      refine ⟨i, preToks pre s.root, Sum.inr (diffs s.root [], s1.root - sx, chainToks (s1 :: ss)),
        segToks s ++ postToks s post, keyOK_of_split i (h12 ▸ hgR) hv, ?_, h12 ▸ route3_stAfter_split_pos hok, by rw [h12], ?_⟩
      · rw [keyWt_eq, fam3_stAfter_B i hgA hA, hm]
      · have hperm := keyBlocks_perm_of_route (route_blocks_split pre post s) h12
          (Sum.inr (diffs s.root [], s1.root - sx, chainToks (s1 :: ss)))
        have hmp : markPos (firstRoot pre s.root) (preToks pre s.root) = s.root := by
          rw [markPos_of_not_leaf (preToks_noLeaf pre s.root), endOf_preToks]
        rw [hmp, witBlocks_off s.root sx [] hblast s1 ss, ← List.append_assoc] at hperm
        obtain ⟨hsep, hF⟩ := skeleton_sep F (suf := []) hok hpw heok hoff hsepR
          (route_loc hok (fun a _ h => by simp at h)) (fun b hb => by simp at hb) List.nodup_nil hsepE hXloc
        exact ⟨(List.Perm.pairwise_iff (fun h => sep_symm h) hperm).2 hsep, fun b hb => hF b (hperm.mem_iff.1 hb)⟩
    | cons b1 suf' =>
      -- the first branch block is the leaf, and the mark sits after it
      have hrootnot : s.root ∉ b1 :: suf' := fun h => hsufP s.root h List.mem_cons_self
      have hblast' : (b1 :: suf').getLast (List.cons_ne_nil _ _) = sx := by
        rw [← hblast, List.getLast_cons (List.cons_ne_nil _ _)]
      rw [List.isChain_cons_cons] at hbch
      obtain ⟨hadj, hbch'⟩ := hbch
      obtain ⟨hrS, hb1S, hne, hd⟩ := selGraph_adj.1 hadj
      have hv : b1 - s.root ∈ S0 := sep_step_mem_S0 hsok.sep hrS hb1S hne hd
      have hword : preToks pre s.root ++ segToks s ++ postToks s post =
          preToks pre s.root ++ Tok.leaf (s.leaf - s.root) :: postToks s post := by
        unfold segToks
        rw [if_pos hrest]
        simp
      rw [hword] at hg
      obtain ⟨hg', -⟩ := gram_swap_leaf hg hv
      obtain ⟨hvw, hm⟩ := hwit (diffs b1 suf') (diffs_mem_S0 hsok.sep b1 suf' hbch')
        ((fam3 i).stAfter 0 (preToks pre s.root ++ [Tok.leaf (b1 - s.root)]))
      refine ⟨i, preToks pre s.root ++ [Tok.leaf (b1 - s.root)],
        Sum.inr (diffs b1 suf', s1.root - sx, chainToks (s1 :: ss)), postToks s post,
        keyOK_of_split i (by simpa using hg') hvw, by rw [keyWt_eq, hm], route3_stAfter_leaf_pos hok hrest b1, endOf_leaf_route hrest b1, ?_⟩
      have hperm := keyBlocks_leaf (pre := pre) (post := post) hrest b1
        (Sum.inr (diffs b1 suf', s1.root - sx, chainToks (s1 :: ss)))
      rw [witBlocks_off b1 sx suf' hblast' s1 ss] at hperm
      obtain ⟨hsep, hF⟩ := skeleton_sep F hok hpw heok hoff (hsepR.sublist (leaf_route_sublist hrest))
        (route_loc_leaf hok hrootnot) hsufS hsufnd hsepE hXloc
      have e : (chainBlocks pre ++ [s.root] ++ chainBlocks post) ++ (b1 :: (suf' ++ chainBlocks (s1 :: ss))) =
          (chainBlocks pre ++ [s.root] ++ chainBlocks post) ++ (b1 :: suf') ++ chainBlocks (s1 :: ss) := by
        simp
      rw [e] at hperm
      exact ⟨(List.Perm.pairwise_iff (fun h => sep_symm h) hperm).2 hsep, fun b hb => hF b (hperm.mem_iff.1 hb)⟩
  · -- a path part: the mark sits on the path
    obtain ⟨pre', post', hsplit⟩ := List.append_of_mem hrP
    have hseg : segToks s = pathToks s.root s.rest := by
      unfold segToks
      rw [if_neg hrest]
    have h12 : (preToks pre s.root ++ prefixToks s.root pre' r) ++ (pathToks r post' ++ postToks s post) =
        chainToks (pre ++ s :: post) := by
      rw [chainToks_pre_post, hseg, prefix_path_split hsplit]
      simp
    obtain ⟨hvw, hm⟩ := hwit (diffs r suf) (diffs_mem_S0 hsok.sep r suf hbch)
      ((fam3 i).stAfter 0 (preToks pre s.root ++ prefixToks s.root pre' r))
    refine ⟨i, preToks pre s.root ++ prefixToks s.root pre' r,
      Sum.inr (diffs r suf, s1.root - sx, chainToks (s1 :: ss)), pathToks r post' ++ postToks s post,
      keyOK_of_split i (h12 ▸ hgR) hvw, by rw [keyWt_eq, hm], h12 ▸ route3_stAfter_split_pos hok, by rw [h12], ?_⟩
    have hperm := keyBlocks_perm_of_route (route_blocks_split pre post s) h12
      (Sum.inr (diffs r suf, s1.root - sx, chainToks (s1 :: ss)))
    have hmp : markPos (firstRoot pre s.root) (preToks pre s.root ++ prefixToks s.root pre' r) = r := by
      rw [markPos_of_not_leaf (noLeaf_append (preToks_noLeaf pre s.root)
        (noLeaf_of_steps (prefixToks_steps s.root r pre'))), endOf_append, endOf_preToks, prefix_end hsplit]
    rw [hmp, witBlocks_off r sx suf hblast s1 ss, ← List.append_assoc] at hperm
    have hsb : segBlocks s = s.rest := by
      unfold segBlocks
      rw [if_neg hrest]
    have havoid : ∀ a ∈ s.root :: segBlocks s, a ∉ suf := by
      rw [hsb]
      exact fun a ha hsuf => hsufP a hsuf ha
    obtain ⟨hsep, hF⟩ := skeleton_sep F hok hpw heok hoff hsepR (route_loc hok havoid) hsufS hsufnd hsepE hXloc
    exact ⟨(List.Perm.pairwise_iff (fun h => sep_symm h) hperm).2 hsep, fun b hb => hF b (hperm.mem_iff.1 hb)⟩

/-! ### The general key with its blocks -/

/-- **The general family key with its skeleton blocks.** Under the hypotheses of `gen_key3`, some axis has a valid
family key with the weight of `gen_key3` whose counted blocks, read from the landing root `e`, are pairwise
`D`-separated flagged blocks. -/
theorem gen_key3_blocks (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} (he : e ∈ L) (hx : x ∈ L)
    (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f)
    (hW0 : ∀ r ∈ L, ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) (hW1 : W1Hyp F L e) :
    ∃ (i : Fin 3) (r1 : List Tok) (wit : Wit) (r2 : List Tok), KeyOK i (r1, wit, r2) ∧
      keyWt i (r1, wit, r2) =
        (fam3 i).wtPre 0 r1 * eps ^ witLen wit * (fam3 i).wt ((fam3 i).stAfter 0 r1 + 52) r2 ∧
      1 ≤ route3.stAfter 0 (r1 ++ r2) ∧ dist3 x (endOf e (r1 ++ r2)) ≤ Const.D - 1 ∧
      (keyBlocks e (r1, wit, r2)).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      ∀ b ∈ keyBlocks e (r1, wit, r2), b ∈ F := by
  obtain ⟨n, f, hf, hdist⟩ := exists_min_fchain3 F L hex
  obtain ⟨seg, hseg, hhead, hok, hpw, hch⟩ :=
    fam_segs_data F L hf hdist (fun j hj => hW0 _ (chain_roots_mem hf he j hj))
  -- the route segments lie in the clusters of the chain's roots
  have hsegs : ∀ t ∈ (List.range (n + 1)).map seg, ∃ j ≤ n, t.sel ⊆ clusterOf F (f j).1 := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    have hj' : j ≤ n := by
      have := List.mem_range.1 hj
      omega
    exact ⟨j, hj', (hseg j hj').2.2.1⟩
  have hsplitj : ∀ j ≤ n, ∃ pre post, (List.range (n + 1)).map seg = pre ++ seg j :: post := by
    intro j hj
    exact List.append_of_mem (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩)
  -- the chain route ends at the cover of the exit `x`
  have hlast : ((List.range (n + 1)).map seg).getLast? = some (seg n) := by simp [List.range_succ]
  have hxcov : ∀ pre post s, (List.range (n + 1)).map seg = pre ++ s :: post →
      dist3 x (endOf (firstRoot pre s.root) (chainToks (pre ++ s :: post))) ≤ Const.D - 1 := by
    intro pre post s hsp
    rw [endOf_split_last (t := seg n) (hsp ▸ hlast)]
    obtain ⟨-, hexit, -, hsn, -⟩ := hseg n le_rfl
    have hc := hsn.exit_cov
    rw [hexit, hf.2.2.2] at hc
    exact hc
  rcases fam_witness3 F L hf hx hW1 with ⟨j, hj, w, hwL, hwc, hwd⟩ | ⟨-, c, hcL, hoff, ⟨k, hk, hck⟩, hfar⟩
  · -- (A): the witness is on the route
    obtain ⟨hroot, -, -, -, hS, hcovS⟩ := hseg j hj
    obtain ⟨pre, post, hsp⟩ := hsplitj j hj
    obtain ⟨sw, hsw, hwsw⟩ := hcovS w (mem_clusterOf.2 ⟨hLF hwL, hwc⟩)
    have hrootL : (seg j).root ∈ L := hroot ▸ chain_roots_mem hf he j hj
    rw [← hroot] at hS hwd
    rw [hsp] at hok hpw hch hhead
    have hfr := firstRoot_eq hhead
    obtain ⟨i, r1, wit, r2, h1, h2, h3, hE, h4, h5⟩ := seg_key_onroute2 F L hok hpw hch hS hrootL hwL hwd hsw hwsw
    have hc := hxcov pre post (seg j) hsp
    rw [← hE, hfr] at hc
    rw [hfr] at h4 h5
    exact ⟨i, r1, wit, r2, h1, h2, h3, hc, h4, h5⟩
  · -- (B): the witness is an excursion
    obtain ⟨jx, x0, esegs, hjx, hx0L, hx0c, hfirst, heok, hepw, hech, heoff, sl, hsl, hspan⟩ :=
      exc_route3 F L hLF hf he hcL hoff hk hck hfar hW0
    obtain ⟨hroot, -, -, -, hS, hcovS⟩ := hseg jx hjx
    obtain ⟨pre, post, hsp⟩ := hsplitj jx hjx
    obtain ⟨sx, hsx, hx0sx⟩ := hcovS x0 (mem_clusterOf.2 ⟨hLF hx0L, hx0c⟩)
    -- the excursion is apart from every route segment
    have hoffs : ∀ t ∈ (List.range (n + 1)).map seg, ∀ t' ∈ esegs, SegApart F t t' := by
      intro t ht t' ht' p hp q hq hpq
      obtain ⟨j', hj', hsub⟩ := hsegs t ht
      exact heoff t' ht' q hq j' hj' ((mem_clusterOf.1 (hsub hp)).2.trans hpq)
    cases esegs with
    | nil => simp at hsl
    | cons s1 ss =>
      obtain ⟨hd1, -⟩ := hfirst s1 rfl
      have hsl' : (s1 :: ss).getLast (List.cons_ne_nil _ _) = sl := by
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hsl
        exact Option.some.inj hsl
      rw [← hroot] at hS
      rw [hsp] at hok hpw hch hhead hoffs
      have hfr := firstRoot_eq hhead
      obtain ⟨i, r1, wit, r2, h1, h2, h3, hE, h4, h5⟩ :=
        seg_key_offroute2 F hok hpw hch hS hsx hx0sx hd1 heok hepw hech hoffs hsl' hspan
      have hc := hxcov pre post (seg jx) hsp
      rw [← hE, hfr] at hc
      rw [hfr] at h4 h5
      exact ⟨i, r1, wit, r2, h1, h2, h3, hc, h4, h5⟩

end QECD1
