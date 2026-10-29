import QECD1.GenKey3

/-!
# The counted blocks of a family key (the skeleton)

`keyBlocks e k` reads the counted blocks of a key `k = (r1, wit, r2)` from the landing root `e`, in four parts:
* the root `e`;
* the route blocks before the mark (`blocksOf e r1`);
* the witness blocks from the mark position (`witBlocks`): the walk's blocks; for an off-route witness also the link
  target and the excursion's blocks;
* the route blocks after the mark (`blocksOf (endOf e r1) r2`).

The mark position (`markPos`) is the route's position after `r1`, except after a leaf. There it is the leaf block,
by the leaf convention: the witness leaves from the root of a root-only part through its first branch block, which
is the leaf.

* `keyBlocks_length`: a valid key has `1 + |r1| + witLen + |r2|` blocks. That is one per `ε` factor of `keyWt`,
  plus the root.
* `preToks`, `postToks`, `chainToks_pre_post`: the explicit split of a chain route at a cluster.
  * The word before the cluster ends at `B` (`route3_stAfter_preToks`) and at the cluster's root (`endOf_preToks`).
  * Its blocks are the earlier clusters' blocks (`blocks_preToks`, `blocks_postToks`, `chainBlocks_eq`).
-/

namespace QECD1

open QECD1.Bld

/-- The blocks of a walk from `cur`. -/
def walkBlocks : V3 → List V3 → List V3
  | _, [] => []
  | cur, v :: w => (cur + v) :: walkBlocks (cur + v) w

/-- The witness's start: the route's position after `r1`, or the leaf block when `r1` ends with a leaf. -/
def markPos (e : V3) (r1 : List Tok) : V3 :=
  match r1.getLast? with
  | some (Tok.leaf v) => endOf e r1 + v
  | _ => endOf e r1

/-- The blocks of a witness from the mark position `p`. -/
def witBlocks (p : V3) : Wit → List V3
  | .inl w => walkBlocks p w
  | .inr x => walkBlocks p x.1 ++ blocksOf (p + x.1.sum) (Tok.link x.2.1 :: x.2.2)

/-- **The counted blocks of a key** from the landing root `e`. -/
def keyBlocks (e : V3) (k : Key) : List V3 :=
  e :: blocksOf e k.1 ++ witBlocks (markPos e k.1) k.2.1 ++ blocksOf (endOf e k.1) k.2.2

theorem walkBlocks_length : ∀ (cur : V3) (w : List V3), (walkBlocks cur w).length = w.length
  | _, [] => rfl
  | cur, v :: w => by
    simp only [walkBlocks, List.length_cons]
    rw [walkBlocks_length (cur + v) w]

theorem walkBlocks_diffs : ∀ (cur : V3) (bs : List V3), walkBlocks cur (diffs cur bs) = bs
  | _, [] => rfl
  | cur, b :: bs => by
    simp only [diffs, walkBlocks, add_sub_cancel]
    rw [walkBlocks_diffs b bs]

theorem blocksOf_length : ∀ (cur : V3) (ws : List Tok), Tok.mark ∉ ws → (blocksOf cur ws).length = ws.length
  | _, [], _ => rfl
  | cur, .step v :: ws, h => by
    simp only [blocksOf, List.length_cons]
    rw [blocksOf_length _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
  | cur, .link v :: ws, h => by
    simp only [blocksOf, List.length_cons]
    rw [blocksOf_length _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
  | cur, .leaf v :: ws, h => by
    simp only [blocksOf, List.length_cons]
    rw [blocksOf_length _ ws (fun hm => h (List.mem_cons_of_mem _ hm))]
  | _, .mark :: _, h => absurd List.mem_cons_self h

/-- Words of the marked copy contain no mark. -/
theorem mark_notMem_marked (i : Fin 3) :
    ∀ (ws : List Tok) (n : ℕ), 52 ≤ n → (fam3 i).Gram n ws → Tok.mark ∉ ws
  | [], _, _, _ => List.not_mem_nil
  | t :: ws, n, hn, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ famToks n at ht
    unfold famToks at ht
    rw [if_neg (by omega)] at ht
    have hne : t ≠ Tok.mark := fun h => mark_notMem (n - 52) (h ▸ ht)
    have hnext : (fam3 i).next n t = routeNext i (n - 52) t + 52 := by
      show famNext i n t = _
      unfold famNext
      rw [if_neg (by omega)]
    intro hm
    rcases List.mem_cons.1 hm with h | h
    · exact hne h.symm
    · rw [hnext] at hrest
      exact mark_notMem_marked i ws _ (by omega) hrest h

/-- Excursion words contain no mark. -/
theorem mark_notMem_exc3 (i : Fin 3) : ∀ (ws : List Tok) (n : ℕ), (exc3 i).Gram n ws → Tok.mark ∉ ws
  | [], _, _ => List.not_mem_nil
  | t :: ws, n, hg => by
    obtain ⟨ht, hrest⟩ := hg
    change t ∈ routeToks n at ht
    intro hm
    rcases List.mem_cons.1 hm with h | h
    · exact mark_notMem n (h ▸ ht)
    · exact mark_notMem_exc3 i ws _ hrest h

/-- **A valid key has `1 + |r1| + witLen + |r2|` counted blocks.** -/
theorem keyBlocks_length (i : Fin 3) (e : V3) {k : Key} (hk : KeyOK i k) :
    (keyBlocks e k).length = 1 + k.1.length + witLen k.2.1 + k.2.2.length := by
  obtain ⟨r1, wit, r2⟩ := k
  obtain ⟨_, h1, hw, h2⟩ := hk
  have hm2 := mark_notMem_marked i r2 _ (by omega) h2
  unfold keyBlocks
  simp only [List.length_append, List.length_cons]
  rw [blocksOf_length e r1 h1, blocksOf_length _ r2 hm2]
  cases wit with
  | inl w =>
    simp only [witBlocks, witLen, walkBlocks_length]
    ring
  | inr x =>
    obtain ⟨-, -, hE⟩ := hw
    simp only [witBlocks, witLen, List.length_append, walkBlocks_length, blocksOf, List.length_cons]
    rw [blocksOf_length _ x.2.2 (mark_notMem_exc3 i x.2.2 0 hE)]
    ring

/-! ### The explicit split of a chain route at a cluster -/

theorem endOf_append : ∀ (cur : V3) (a b : List Tok), endOf cur (a ++ b) = endOf (endOf cur a) b
  | _, [], _ => rfl
  | cur, .step v :: a, b => endOf_append (cur + v) a b
  | cur, .link v :: a, b => endOf_append (cur + v) a b
  | cur, .leaf _ :: a, b => endOf_append cur a b
  | cur, .mark :: a, b => endOf_append cur a b

/-- The first root of `pre ++ [s]`, given the root `r` of `s`. -/
def firstRoot : List Seg → V3 → V3
  | [], r => r
  | p :: _, _ => p.root

/-- The route word before the cluster with root `r` in `pre ++ s :: post`: each earlier cluster's word and link. -/
def preToks : List Seg → V3 → List Tok
  | [], _ => []
  | p :: pre, r => segToks p ++ Tok.link (firstRoot pre r - segEnd p) :: preToks pre r

/-- The route word after the cluster `s` in a chain: the link to the next root and the rest of the chain. -/
def postToks (s : Seg) : List Seg → List Tok
  | [] => []
  | s' :: ss => Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss)

theorem chainToks_cons_post (s : Seg) : ∀ post : List Seg, chainToks (s :: post) = segToks s ++ postToks s post
  | [] => by simp [chainToks, postToks]
  | _ :: _ => rfl

/-- **The explicit split of a chain route** at any of its clusters. -/
theorem chainToks_pre_post : ∀ (pre : List Seg) (s : Seg) (post : List Seg),
    chainToks (pre ++ s :: post) = preToks pre s.root ++ segToks s ++ postToks s post
  | [], s, post => by simp [preToks, chainToks_cons_post]
  | p :: pre, s, post => by
    have hne : pre ++ s :: post ≠ [] := by simp
    rw [List.cons_append, chainToks_cons_ne_nil p _ hne, chainToks_pre_post pre s post]
    have hfr : ((pre ++ s :: post).head hne).root = firstRoot pre s.root := by
      cases pre <;> rfl
    rw [hfr]
    simp [preToks]

theorem route3_stAfter_preToks : ∀ (pre : List Seg) (r : V3), route3.stAfter 0 (preToks pre r) = 0
  | [], _ => rfl
  | p :: pre, r => by
    show route3.stAfter 0 (segToks p ++ Tok.link (firstRoot pre r - segEnd p) :: preToks pre r) = 0
    rw [route3_stAfter_link]
    exact route3_stAfter_preToks pre r

theorem endOf_preToks : ∀ (pre : List Seg) (r : V3), endOf (firstRoot pre r) (preToks pre r) = r
  | [], _ => rfl
  | p :: pre, r => by
    show endOf p.root (segToks p ++ Tok.link (firstRoot pre r - segEnd p) :: preToks pre r) = r
    rw [endOf_append, segToks_end]
    show endOf (segEnd p + (firstRoot pre r - segEnd p)) (preToks pre r) = r
    rw [add_sub_cancel]
    exact endOf_preToks pre r

/-- **The blocks of a chain route**, without any validity assumption. -/
theorem chainBlocks_eq : ∀ (s : Seg) (ss : List Seg),
    s.root :: blocksOf s.root (chainToks (s :: ss)) = chainBlocks (s :: ss)
  | s, [] => by
    show s.root :: blocksOf s.root (segToks s) = (s.root :: segBlocks s) ++ []
    rw [segToks_blocks, List.append_nil]
  | s, s' :: ss => by
    show s.root :: blocksOf s.root (segToks s ++ Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss)) =
      (s.root :: segBlocks s) ++ chainBlocks (s' :: ss)
    rw [blocksOf_append, segToks_blocks, segToks_end, ← chainBlocks_eq s' ss]
    simp only [blocksOf, add_sub_cancel]
    rfl

theorem chainBlocks_append : ∀ (l1 l2 : List Seg), chainBlocks (l1 ++ l2) = chainBlocks l1 ++ chainBlocks l2
  | [], _ => rfl
  | t :: l, l2 => by
    show (t.root :: segBlocks t) ++ chainBlocks (l ++ l2) =
      ((t.root :: segBlocks t) ++ chainBlocks l) ++ chainBlocks l2
    rw [chainBlocks_append l l2, List.append_assoc]

theorem blocks_preToks : ∀ (pre : List Seg) (r : V3),
    firstRoot pre r :: blocksOf (firstRoot pre r) (preToks pre r) = chainBlocks pre ++ [r]
  | [], _ => rfl
  | p :: pre, r => by
    show p.root :: blocksOf p.root (segToks p ++ Tok.link (firstRoot pre r - segEnd p) :: preToks pre r) =
      ((p.root :: segBlocks p) ++ chainBlocks pre) ++ [r]
    rw [blocksOf_append, segToks_blocks, segToks_end]
    simp only [blocksOf, add_sub_cancel]
    rw [blocks_preToks pre r]
    simp

theorem blocks_postToks (s : Seg) : ∀ post : List Seg, blocksOf (segEnd s) (postToks s post) = chainBlocks post
  | [] => rfl
  | s' :: ss => by
    show (segEnd s + (s'.root - segEnd s)) :: blocksOf (segEnd s + (s'.root - segEnd s)) (chainToks (s' :: ss)) =
      chainBlocks (s' :: ss)
    rw [add_sub_cancel]
    exact chainBlocks_eq s' ss

/-- The blocks of the chain route from its first root. -/
theorem route_blocks_split (pre post : List Seg) (s : Seg) :
    firstRoot pre s.root :: blocksOf (firstRoot pre s.root) (chainToks (pre ++ s :: post)) =
      chainBlocks (pre ++ s :: post) := by
  cases pre with
  | nil => exact chainBlocks_eq s post
  | cons p pre' => exact chainBlocks_eq p (pre' ++ s :: post)

theorem firstRoot_eq {pre post : List Seg} {s : Seg} {e : V3}
    (h : (pre ++ s :: post).head?.map Seg.root = some e) : firstRoot pre s.root = e := by
  cases pre with
  | nil => simpa [firstRoot] using h
  | cons p pre' => simpa [firstRoot] using h

/-! ### The mark position -/

theorem markPos_of_not_leaf {e : V3} {r1 : List Tok} (h : ∀ v, r1.getLast? ≠ some (Tok.leaf v)) :
    markPos e r1 = endOf e r1 := by
  unfold markPos
  split
  · rename_i v hv
    exact absurd hv (h v)
  · rfl

theorem markPos_leaf (e : V3) (A : List Tok) (v : V3) : markPos e (A ++ [Tok.leaf v]) = endOf e A + v := by
  simp [markPos, endOf_append, endOf]

theorem noLeaf_append {A B : List Tok} (hA : ∀ v, A.getLast? ≠ some (Tok.leaf v))
    (hB : ∀ v, B.getLast? ≠ some (Tok.leaf v)) (v : V3) : (A ++ B).getLast? ≠ some (Tok.leaf v) := by
  rw [List.getLast?_append]
  cases hb : B.getLast? with
  | none => simpa using hA v
  | some t => simpa [hb] using hB v

theorem noLeaf_of_steps {ws : List Tok} (h : ∀ t ∈ ws, ∃ u, t = Tok.step u) (v : V3) :
    ws.getLast? ≠ some (Tok.leaf v) := by
  intro hl
  obtain ⟨u, hu⟩ := h _ (List.mem_of_getLast? hl)
  cases hu

theorem pathToks_steps : ∀ (cur : V3) (bs : List V3), ∀ t ∈ pathToks cur bs, ∃ u, t = Tok.step u
  | _, [], t, ht => by simp [pathToks] at ht
  | cur, b :: bs, t, ht => by
    simp only [pathToks, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨_, rfl⟩
    · exact pathToks_steps b bs t ht

theorem prefixToks_steps (e r : V3) (pre : List V3) : ∀ t ∈ prefixToks e pre r, ∃ u, t = Tok.step u := by
  cases pre with
  | nil => simp [prefixToks]
  | cons a pre' => exact pathToks_steps e (pre' ++ [r])

theorem preToks_noLeaf : ∀ (pre : List Seg) (r v : V3), (preToks pre r).getLast? ≠ some (Tok.leaf v)
  | [], _, _ => by simp [preToks]
  | p :: pre, r, v => by
    have e : preToks (p :: pre) r = (segToks p ++ [Tok.link (firstRoot pre r - segEnd p)]) ++ preToks pre r := by
      simp [preToks]
    rw [e]
    refine noLeaf_append (fun u => ?_) (fun u => preToks_noLeaf pre r u) v
    simp

theorem prefix_end {e r : V3} {P' pre post : List V3} (hsplit : e :: P' = pre ++ r :: post) :
    endOf e (prefixToks e pre r) = r := by
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hsplit
    rw [hsplit.1]
    rfl
  | cons a pre' =>
    show endOf e (pathToks e (pre' ++ [r])) = r
    rw [pathToks_end]
    simp

/-! ### The blocks of a key read along a split route -/

/-- When `r1 ++ r2` is the chain route, the key's blocks are the route's blocks and the witness blocks. -/
theorem keyBlocks_perm_of_route {segs : List Seg} {e : V3}
    (he : e :: blocksOf e (chainToks segs) = chainBlocks segs) {r1 r2 : List Tok} (h12 : r1 ++ r2 = chainToks segs)
    (wit : Wit) : (keyBlocks e (r1, wit, r2)).Perm (chainBlocks segs ++ witBlocks (markPos e r1) wit) := by
  have hb : (e :: blocksOf e r1) ++ blocksOf (endOf e r1) r2 = chainBlocks segs := by
    rw [← he, ← h12, blocksOf_append]
    rfl
  show (((e :: blocksOf e r1) ++ witBlocks (markPos e r1) wit) ++ blocksOf (endOf e r1) r2).Perm _
  rw [← hb, List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

/-- In the leaf convention, the key's blocks are the route's blocks without the part's own leaf, the branch's first
block, and the witness blocks from it. -/
theorem keyBlocks_leaf {pre post : List Seg} {s : Seg} (hrest : s.rest = []) (b1 : V3) (wit : Wit) :
    (keyBlocks (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)], wit, postToks s post)).Perm
      ((chainBlocks pre ++ [s.root] ++ chainBlocks post) ++ (b1 :: witBlocks b1 wit)) := by
  have hend : segEnd s = s.root := by
    unfold segEnd
    simp [hrest]
  have h1 : firstRoot pre s.root :: blocksOf (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) =
      chainBlocks pre ++ [s.root] ++ [b1] := by
    rw [blocksOf_append, endOf_preToks, ← List.cons_append, blocks_preToks]
    simp [blocksOf]
  have h2 : endOf (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) = s.root := by
    rw [endOf_append, endOf_preToks]
    rfl
  have h3 : markPos (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)]) = b1 := by
    rw [markPos_leaf, endOf_preToks, add_sub_cancel]
  show (((firstRoot pre s.root :: blocksOf (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)])) ++
    witBlocks (markPos (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)])) wit) ++
    blocksOf (endOf (firstRoot pre s.root) (preToks pre s.root ++ [Tok.leaf (b1 - s.root)])) (postToks s post)).Perm _
  have h4 : blocksOf s.root (postToks s post) = chainBlocks post := by
    rw [← hend]
    exact blocks_postToks s post
  rw [h1, h2, h3, h4]
  have e1 : ((chainBlocks pre ++ [s.root] ++ [b1]) ++ witBlocks b1 wit) ++ chainBlocks post =
      (chainBlocks pre ++ [s.root]) ++ ((b1 :: witBlocks b1 wit) ++ chainBlocks post) := by simp
  have e2 : (chainBlocks pre ++ [s.root] ++ chainBlocks post) ++ (b1 :: witBlocks b1 wit) =
      (chainBlocks pre ++ [s.root]) ++ (chainBlocks post ++ (b1 :: witBlocks b1 wit)) := by simp
  rw [e1, e2]
  exact List.Perm.append_left _ List.perm_append_comm

/-- The witness blocks of an off-route witness: the walk's blocks, then the excursion's blocks from its first root. -/
theorem witBlocks_off (r sx : V3) (suf : List V3) (hlast : (r :: suf).getLast (List.cons_ne_nil _ _) = sx)
    (s1 : Seg) (ss : List Seg) :
    witBlocks r (Sum.inr (diffs r suf, s1.root - sx, chainToks (s1 :: ss))) = suf ++ chainBlocks (s1 :: ss) := by
  simp only [witBlocks]
  rw [walkBlocks_diffs, diffs_sum, hlast, add_sub_cancel]
  show suf ++ (sx + (s1.root - sx)) :: blocksOf (sx + (s1.root - sx)) (chainToks (s1 :: ss)) = _
  rw [add_sub_cancel, chainBlocks_eq]

/-! ### Separation of the skeleton -/

/-- Two segments in different clusters. -/
def SegApart (F : Finset V3) (s s' : Seg) : Prop := ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q

theorem segApart_symm {F : Finset V3} {s s' : Seg} (h : SegApart F s s') : SegApart F s' s :=
  fun p hp q hq hpq => h q hq p hp (sameComp_symm F _ hpq)

theorem apart_sep {F : Finset V3} {s s' : Seg} (hs : SegOK F s) (hs' : SegOK F s') (h : SegApart F s s')
    {a b : V3} (ha : a ∈ s.sel) (hb : b ∈ s'.sel) : Const.D ≤ dist3 a b :=
  selected_sep F (hs.sel_sub ha) (hs'.sel_sub hb) (h a ha b hb)

theorem sep_symm : Symmetric (fun a b : V3 => Const.D ≤ dist3 a b) := by
  intro a b h
  show Const.D ≤ dist3 b a
  rw [dist3_comm]
  exact h

/-- The blocks after the head of a selection path are selected. -/
theorem chain_mem_sel {S : Finset V3} {A : ℕ} :
    ∀ (a : V3) (l : List V3), List.IsChain (selGraph S A).Adj (a :: l) → ∀ x ∈ l, x ∈ S
  | _, [], _, x, hx => by simp at hx
  | a, y :: ys, hc, x, hx => by
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact (selGraph_adj.1 hc.1).2.1
    · exact chain_mem_sel y ys hc.2 x hx'

/-- The blocks of a chain lie in the selections of its segments. -/
theorem chainBlocks_mem_sel {F : Finset V3} : ∀ (ts : List Seg), (∀ t ∈ ts, SegOK F t) →
    ∀ b ∈ chainBlocks ts, ∃ t ∈ ts, b ∈ t.sel
  | [], _, b, hb => by simp [chainBlocks] at hb
  | t :: ts, hts, b, hb => by
    simp only [chainBlocks, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ⟨t, List.mem_cons_self, segBlocks_sub (hts t List.mem_cons_self) b hb⟩
    · obtain ⟨u, hu, hbu⟩ := chainBlocks_mem_sel ts (fun u hu => hts u (List.mem_cons_of_mem _ hu)) b hb
      exact ⟨u, List.mem_cons_of_mem _ hu, hbu⟩

/-- In a chain `pre ++ s :: post` of pairwise apart segments, each segment of `pre ++ post` is apart from `s`. -/
theorem apart_of_split {F : Finset V3} {pre post : List Seg} {s : Seg}
    (hpw : (pre ++ s :: post).Pairwise (SegApart F)) : ∀ t ∈ pre ++ post, SegApart F t s := by
  intro t ht
  rw [List.pairwise_append] at hpw
  rcases List.mem_append.1 ht with h | h
  · exact hpw.2.2 t h s List.mem_cons_self
  · exact segApart_symm (List.rel_of_pairwise_cons hpw.2.1 h)

/-- **Separation of a skeleton**: the route blocks `R`, the witness branch `suf` in the selection of the witness part
`s`, and the excursion blocks `X` are pairwise `D`-separated flagged blocks. -/
theorem skeleton_sep (F : Finset V3) {pre post esegs : List Seg} {s : Seg} {R suf X : List V3}
    (hok : ∀ t ∈ pre ++ s :: post, SegOK F t) (hpw : (pre ++ s :: post).Pairwise (SegApart F))
    (heok : ∀ t ∈ esegs, SegOK F t) (hoff : ∀ t ∈ pre ++ s :: post, ∀ t' ∈ esegs, SegApart F t t')
    (hR : R.Pairwise (fun a b => Const.D ≤ dist3 a b))
    (hRloc : ∀ a ∈ R, (∃ t ∈ pre ++ post, a ∈ t.sel) ∨ (a ∈ s.sel ∧ a ∉ suf))
    (hsuf : ∀ b ∈ suf, b ∈ s.sel) (hsufnd : suf.Nodup)
    (hX : X.Pairwise (fun a b => Const.D ≤ dist3 a b)) (hXloc : ∀ c ∈ X, ∃ t' ∈ esegs, c ∈ t'.sel) :
    (R ++ suf ++ X).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧ ∀ b ∈ R ++ suf ++ X, b ∈ F := by
  have hs : s ∈ pre ++ s :: post := List.mem_append_right _ List.mem_cons_self
  have hsok := hok s hs
  have hpp : ∀ t ∈ pre ++ post, t ∈ pre ++ s :: post := by
    intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  -- every block of `R ++ suf` lies in the selection of a route segment
  have hloc : ∀ a ∈ R ++ suf, ∃ t ∈ pre ++ s :: post, a ∈ t.sel := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · rcases hRloc a h with ⟨t, ht, hat⟩ | ⟨has, _⟩
      · exact ⟨t, hpp t ht, hat⟩
      · exact ⟨s, hs, has⟩
    · exact ⟨s, hs, hsuf a h⟩
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hR, hsufnd.imp_of_mem fun ha hb hne => hsok.sep _ (hsuf _ ha) _ (hsuf _ hb) hne, ?_⟩, hX, ?_⟩
    · intro a ha b hb
      rcases hRloc a ha with ⟨t, ht, hat⟩ | ⟨has, hanot⟩
      · exact apart_sep (hok t (hpp t ht)) hsok (apart_of_split hpw t ht) hat (hsuf b hb)
      · exact hsok.sep a has b (hsuf b hb) (fun h => hanot (h ▸ hb))
    · intro a ha c hc
      obtain ⟨t, ht, hat⟩ := hloc a ha
      obtain ⟨t', ht', hct⟩ := hXloc c hc
      exact apart_sep (hok t ht) (heok t' ht') (hoff t ht t' ht') hat hct
  · intro b hb
    rcases List.mem_append.1 hb with h | h
    · obtain ⟨t, ht, hbt⟩ := hloc b h
      exact (hok t ht).sel_sub hbt
    · obtain ⟨t', ht', hbt⟩ := hXloc b h
      exact (heok t' ht').sel_sub hbt

end QECD1
