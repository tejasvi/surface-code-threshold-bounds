import QECD1.Level1
import QECD1.Top

/-!
# Skeleton routes: from a chain of clusters to a valid route word

This is the dimension-free core of the 2D `route_of_chain` / `fam_route` (TwoD/T2Skel) and of the T1 route
existence (TwoD/RouteExist), in 3D. The steps are as follows.
* In each cluster, a selection is rooted at the entry block (`exists_selection3`).
* A simple path through the selection (the support of a bypassed walk) runs from the root to the selected block
  covering the exit. Its steps are `S0` offsets (`step_mem_S0`).
* When that path is the root alone, a leaf is used. It is a selected block next to the root, which exists when the
  cluster has a block at distance `≥ D` from the root (that block's cover is not the root; this is what W0 provides).
* Consecutive clusters are joined by a link from the end of one path to the next root. That offset lies in `S1`
  (`link_mem_S1`).

The resulting words are valid words of the route grammar `rToks`/`rNext` (B: steps and leaves; A: steps and links;
C: links; no link from B, so the leaf convention holds). The same grammar is that of the family automata, and their
counted blocks are pairwise `D`-separated.

This module proves the in-cluster part:
* `selGraph`, `sel_reachable`, `exists_sel_path`: a simple path in the selection from the root to any selected block;
* `pathToks`, `pathToks_gram`, `pathToks_blocks`, `pathToks_end`: the step word of a path, valid from `B` or `A`;
  its counted blocks are the path minus the root, and it ends at the path's last block;
* `exists_leaf`: the leaf block, a selected block `≠` root within `A0` of it, from a block `≥ D` from the root;
* `leaf_gram`: the leaf word, valid from `B`.

The chain over clusters is stated as `ChainRoute` and proved in `chain_route`, using `link_mem_S1` and
`selected_sep`.
-/

namespace QECD1

/-- Selected blocks within `A` of each other. -/
def selRel (S : Finset V3) (A : ℕ) (x y : V3) : Prop := x ∈ S ∧ y ∈ S ∧ dist3 x y ≤ A

/-- The selection graph: distinct selected blocks within `A` of each other. -/
def selGraph (S : Finset V3) (A : ℕ) : SimpleGraph V3 := SimpleGraph.fromRel (selRel S A)

theorem selGraph_adj {S : Finset V3} {A : ℕ} {x y : V3} :
    (selGraph S A).Adj x y ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ dist3 x y ≤ A := by
  unfold selGraph selRel
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, ⟨hx, hy, hd⟩ | ⟨hy, hx, hd⟩⟩
    · exact ⟨hx, hy, hne, hd⟩
    · exact ⟨hx, hy, hne, by rw [dist3_comm]; exact hd⟩
  · rintro ⟨hx, hy, hne, hd⟩
    exact ⟨hne, Or.inl ⟨hx, hy, hd⟩⟩

theorem sel_reachable {S : Finset V3} {A : ℕ} {r s : V3}
    (h : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ dist3 x y ≤ A) r s) : (selGraph S A).Reachable r s := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    by_cases hb : b = c
    · rw [← hb]
      exact ih
    · exact ih.trans (SimpleGraph.Adj.reachable (selGraph_adj.2 ⟨hbc.1, hbc.2.1, hb, hbc.2.2⟩))

/-- **A simple path in the selection** from the root `r` to any selected block `s`. -/
theorem exists_sel_path {K S : Finset V3} {r : V3} {D A : ℕ} (hS : IsSelection3 K S r D A) {s : V3}
    (hs : s ∈ S) :
    ∃ rest : List V3, (r :: rest).Nodup ∧ List.IsChain (selGraph S A).Adj (r :: rest) ∧
      (r :: rest).getLast (List.cons_ne_nil _ _) = s := by
  classical
  obtain ⟨p⟩ := sel_reachable (hS.2.2.2 s hs)
  set q := p.bypass
  have hnd := (SimpleGraph.Walk.bypass_isPath p).support_nodup
  have hch := SimpleGraph.Walk.isChain_adj_support q
  have hhead := SimpleGraph.Walk.head_support q
  have hlast := SimpleGraph.Walk.getLast_support q
  cases hsup : q.support with
  | nil => exact absurd hsup (SimpleGraph.Walk.support_ne_nil q)
  | cons a rest =>
    have ha : a = r := by
      have := hhead
      simp only [hsup, List.head_cons] at this
      exact this
    subst ha
    refine ⟨rest, ?_, ?_, ?_⟩
    · rw [← hsup]; exact hnd
    · rw [← hsup]; exact hch
    · have := hlast
      simp only [hsup] at this
      exact this

/-- The step word of a path from `cur`. -/
def pathToks : V3 → List V3 → List Tok
  | _, [] => []
  | cur, b :: bs => Tok.step (b - cur) :: pathToks b bs

/-- The counted blocks of a token word from `cur` (step and link targets, leaf blocks). -/
def blocksOf : V3 → List Tok → List V3
  | _, [] => []
  | cur, .step v :: ws => (cur + v) :: blocksOf (cur + v) ws
  | cur, .link v :: ws => (cur + v) :: blocksOf (cur + v) ws
  | cur, .leaf v :: ws => (cur + v) :: blocksOf cur ws
  | cur, .mark :: ws => blocksOf cur ws

/-- The position after a token word (a leaf does not move the route). -/
def endOf : V3 → List Tok → V3
  | cur, [] => cur
  | cur, .step v :: ws => endOf (cur + v) ws
  | cur, .link v :: ws => endOf (cur + v) ws
  | cur, .leaf _ :: ws => endOf cur ws
  | cur, .mark :: ws => endOf cur ws

theorem pathToks_blocks : ∀ (cur : V3) (bs : List V3), blocksOf cur (pathToks cur bs) = bs
  | _, [] => rfl
  | cur, b :: bs => by
    simp only [pathToks, blocksOf, add_sub_cancel]
    rw [pathToks_blocks b bs]

theorem pathToks_end : ∀ (cur : V3) (bs : List V3), endOf cur (pathToks cur bs) = (cur :: bs).getLast (List.cons_ne_nil _ _)
  | _, [] => rfl
  | cur, b :: bs => by
    simp only [pathToks, endOf, add_sub_cancel]
    rw [pathToks_end b bs, List.getLast_cons (List.cons_ne_nil _ _)]

theorem rToks_step (q : ℕ) (hq : q ≤ 1) (v : V3) (hv : v ∈ S0) : Tok.step v ∈ rToks q := by
  unfold rToks
  split_ifs with h0 h1
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  · omega

/-- **The step word of a selection path is valid** from `B` (0) or `A` (1). -/
theorem pathToks_gram {K S : Finset V3} {r : V3} (hS : IsSelection3 K S r Const.D Const.A0) :
    ∀ (q : ℕ), q ≤ 1 → ∀ (cur : V3) (bs : List V3), List.IsChain (selGraph S Const.A0).Adj (cur :: bs) →
      route3.Gram q (pathToks cur bs)
  | _, _, _, [], _ => trivial
  | q, hq, cur, b :: bs, hch => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hadj, hrest⟩ := hch
    obtain ⟨hc, hb, hne, hd⟩ := selGraph_adj.1 hadj
    refine ⟨rToks_step q hq _ (step_mem_S0 hS hc hb hne hd), ?_⟩
    exact pathToks_gram hS 1 le_rfl b bs hrest

/-- **The leaf**: if the cluster `K` has a block at distance `≥ D` from the root `r`, some selected block other
than `r` lies within `A0` of `r`. -/
theorem exists_leaf {K S : Finset V3} {r : V3} (hS : IsSelection3 K S r Const.D Const.A0)
    (hcov : ∀ x ∈ K, ∃ s ∈ S, dist3 x s ≤ Const.D - 1) {b : V3} (hb : b ∈ K) (hfar : Const.D ≤ dist3 r b) :
    ∃ l ∈ S, l ≠ r ∧ dist3 r l ≤ Const.A0 := by
  obtain ⟨s, hs, hbs⟩ := hcov b hb
  have hsr : s ≠ r := by
    intro h
    rw [h, dist3_comm] at hbs
    rw [Const.D_val] at hfar hbs
    omega
  obtain ⟨rest, _, hch, hlast⟩ := exists_sel_path hS hs
  cases rest with
  | nil =>
    simp only [List.getLast_singleton] at hlast
    exact absurd hlast.symm hsr
  | cons l rest' =>
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hadj, _⟩ := hch
    obtain ⟨_, hl, hne, hd⟩ := selGraph_adj.1 hadj
    exact ⟨l, hl, hne.symm, hd⟩

theorem rToks_leaf (v : V3) (hv : v ∈ S0) : Tok.leaf v ∈ rToks 0 := by
  unfold rToks
  rw [if_pos rfl]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)

/-- **The leaf word is valid from `B`**, its counted block is the leaf, and the route stays at the root. -/
theorem leaf_gram {K S : Finset V3} {r l : V3} (hS : IsSelection3 K S r Const.D Const.A0) (hl : l ∈ S)
    (hne : l ≠ r) (hd : dist3 r l ≤ Const.A0) :
    route3.Gram 0 [Tok.leaf (l - r)] ∧ blocksOf r [Tok.leaf (l - r)] = [l] ∧ endOf r [Tok.leaf (l - r)] = r := by
  refine ⟨⟨rToks_leaf _ (step_mem_S0 hS hS.2.1 hl hne.symm hd), trivial⟩, ?_, rfl⟩
  simp [blocksOf]

/-! ### The chain over clusters -/

/-- Steps between distinct blocks of a `D`-separated set, within `A0`, are `S0` offsets. -/
theorem sep_step_mem_S0 {S : Finset V3} (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q) {s s' : V3}
    (hs : s ∈ S) (hs' : s' ∈ S) (hne : s ≠ s') (hlink : dist3 s s' ≤ Const.A0) : s' - s ∈ S0 := by
  have h := hsep s hs s' hs' hne
  rw [S0_eq, Finset.mem_filter, mem_box]
  have h1 : linf (s' - s) = dist3 s s' := by rw [dist3, linf_sub_comm]
  rw [h1]
  exact ⟨hlink, h⟩

theorem pathToks_gram' {S : Finset V3} (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q) :
    ∀ (q : ℕ), q ≤ 1 → ∀ (cur : V3) (bs : List V3), List.IsChain (selGraph S Const.A0).Adj (cur :: bs) →
      route3.Gram q (pathToks cur bs)
  | _, _, _, [], _ => trivial
  | q, hq, cur, b :: bs, hch => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hadj, hrest⟩ := hch
    obtain ⟨hc, hb, hne, hd⟩ := selGraph_adj.1 hadj
    exact ⟨rToks_step q hq _ (sep_step_mem_S0 hsep hc hb hne hd), pathToks_gram' hsep 1 le_rfl b bs hrest⟩

theorem pathToks_stAfter : ∀ (q : ℕ) (cur b : V3) (bs : List V3),
    route3.stAfter q (pathToks cur (b :: bs)) = 1
  | q, cur, b, [] => rfl
  | q, cur, b, c :: bs => by
    show route3.stAfter 1 (pathToks b (c :: bs)) = 1
    exact pathToks_stAfter 1 b c bs

theorem rToks_link (q : ℕ) (hq1 : 1 ≤ q) (v : V3) (hv : v ∈ S1off) : Tok.link v ∈ rToks q := by
  unfold rToks
  split_ifs with h0 h1
  · omega
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)
  · exact Finset.mem_image_of_mem _ hv

theorem blocksOf_append : ∀ (cur : V3) (a b : List Tok), blocksOf cur (a ++ b) = blocksOf cur a ++ blocksOf (endOf cur a) b
  | _, [], _ => rfl
  | cur, .step v :: a, b => by
    simp only [List.cons_append, blocksOf, endOf]
    rw [blocksOf_append (cur + v) a b]
  | cur, .link v :: a, b => by
    simp only [List.cons_append, blocksOf, endOf]
    rw [blocksOf_append (cur + v) a b]
  | cur, .leaf v :: a, b => by
    simp only [List.cons_append, blocksOf, endOf]
    rw [blocksOf_append cur a b]
  | cur, .mark :: a, b => by
    simp only [List.cons_append, blocksOf, endOf]
    rw [blocksOf_append cur a b]

/-- One cluster of a route: its root (an actual block, the entry), its selection, the path from the root to the
cover of the exit (without the root), the leaf (used when the path is the root alone), and the exit block. -/
structure Seg where
  root : V3
  sel : Finset V3
  rest : List V3
  leaf : V3
  exit : V3

/-- The word of one cluster. -/
def segToks (s : Seg) : List Tok := if s.rest = [] then [Tok.leaf (s.leaf - s.root)] else pathToks s.root s.rest

/-- The end of the route in a cluster: the last path block, or the root (a leaf does not move the route). -/
def segEnd (s : Seg) : V3 := (s.root :: s.rest).getLast (List.cons_ne_nil _ _)

/-- The counted blocks of a cluster's word. -/
def segBlocks (s : Seg) : List V3 := if s.rest = [] then [s.leaf] else s.rest

/-- Validity of one cluster (`F`: the flagged blocks). -/
structure SegOK (F : Finset V3) (s : Seg) : Prop where
  sel_sub : s.sel ⊆ F
  root_mem : s.root ∈ s.sel
  sep : ∀ p ∈ s.sel, ∀ q ∈ s.sel, p ≠ q → Const.D ≤ dist3 p q
  nodup : (s.root :: s.rest).Nodup
  chain : List.IsChain (selGraph s.sel Const.A0).Adj (s.root :: s.rest)
  leafOK : s.rest = [] → s.leaf ∈ s.sel ∧ s.leaf ≠ s.root ∧ dist3 s.root s.leaf ≤ Const.A0
  exit_mem : s.exit ∈ F
  exit_cov : dist3 s.exit (segEnd s) ≤ Const.D - 1

theorem segToks_end (s : Seg) : endOf s.root (segToks s) = segEnd s := by
  unfold segToks segEnd
  split_ifs with h
  · simp only [endOf]
    simp [h]
  · exact pathToks_end s.root s.rest

theorem segToks_blocks (s : Seg) : blocksOf s.root (segToks s) = segBlocks s := by
  unfold segToks segBlocks
  split_ifs with h
  · simp [blocksOf]
  · exact pathToks_blocks s.root s.rest

theorem segToks_gram {F : Finset V3} {s : Seg} (hs : SegOK F s) :
    route3.Gram 0 (segToks s) ∧ 1 ≤ route3.stAfter 0 (segToks s) := by
  unfold segToks
  split_ifs with h
  · obtain ⟨hl, hne, hd⟩ := hs.leafOK h
    refine ⟨⟨rToks_leaf _ (sep_step_mem_S0 hs.sep hs.root_mem hl hne.symm hd), trivial⟩, ?_⟩
    show 1 ≤ route3.stAfter 2 []
    show 1 ≤ 2
    norm_num
  · refine ⟨pathToks_gram' hs.sep 0 (by norm_num) s.root s.rest hs.chain, ?_⟩
    cases hr : s.rest with
    | nil => exact absurd hr h
    | cons b bs =>
      rw [pathToks_stAfter]

theorem segBlocks_sub {F : Finset V3} {s : Seg} (hs : SegOK F s) : ∀ b ∈ s.root :: segBlocks s, b ∈ s.sel := by
  intro b hb
  unfold segBlocks at hb
  split_ifs at hb with h
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hs.root_mem
    · exact (hs.leafOK h).1
  · have hch := hs.chain
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hs.root_mem
    · cases hr : s.rest with
      | nil => exact absurd hr h
      | cons c cs =>
        rw [hr] at hch hb'
        -- every block after the root is the end of an adjacency step, hence selected
        have key : ∀ (a : V3) (l : List V3), List.IsChain (selGraph s.sel Const.A0).Adj (a :: l) → ∀ x ∈ l, x ∈ s.sel := by
          intro a l
          induction l generalizing a with
          | nil => intro _ x hx; simp at hx
          | cons y ys ih =>
            intro hc x hx
            rw [List.isChain_cons_cons] at hc
            rcases List.mem_cons.1 hx with rfl | hx'
            · exact (selGraph_adj.1 hc.1).2.1
            · exact ih y hc.2 x hx'
        exact key s.root (c :: cs) hch b hb'

theorem segBlocks_nodup {F : Finset V3} {s : Seg} (hs : SegOK F s) : (s.root :: segBlocks s).Nodup := by
  unfold segBlocks
  split_ifs with h
  · rw [List.nodup_cons]
    exact ⟨by simp only [List.mem_singleton]; exact fun e => (hs.leafOK h).2.1 e.symm, List.nodup_singleton _⟩
  · exact hs.nodup

/-- The route word of a chain of clusters: each cluster's word, then a link from its end to the next root. -/
def chainToks : List Seg → List Tok
  | [] => []
  | [s] => segToks s
  | s :: s' :: ss => segToks s ++ Tok.link (s'.root - segEnd s) :: chainToks (s' :: ss)

/-- The counted blocks of a chain, the first root included. -/
def chainBlocks : List Seg → List V3
  | [] => []
  | s :: ss => (s.root :: segBlocks s) ++ chainBlocks ss

/-- **The chain route** (2D `route_of_chain`, dimension-free core). Each cluster is valid (`SegOK`), the
clusters are pairwise different `a0`-components of `F`, and each exit is within `a1` of the next root. Then:
* the route word is a valid word of the route grammar from `B`;
* its counted blocks, with the first root, are the clusters' roots and counted blocks;
* they are pairwise `D`-separated (`no_common_edge` applies).
The step offsets lie in `S0` and the link offsets in `S1`, as the grammar requires. -/
theorem chain_route (F : Finset V3) :
    ∀ (segs : List Seg), (∀ s ∈ segs, SegOK F s) →
      segs.Pairwise (fun s s' => ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q) →
      segs.IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1) →
      ∀ s0 ∈ segs.head?, route3.Gram 0 (chainToks segs) ∧
        s0.root :: blocksOf s0.root (chainToks segs) = chainBlocks segs ∧
        (chainBlocks segs).Pairwise (fun a b => Const.D ≤ dist3 a b)
  | [], _, _, _ => fun s0 h => by simp at h
  | [s], hok, _, _ => by
    intro s0 h
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h
    subst s
    have hs := hok s0 (List.mem_singleton_self _)
    refine ⟨(segToks_gram hs).1, ?_, ?_⟩
    · show s0.root :: blocksOf s0.root (segToks s0) = (s0.root :: segBlocks s0) ++ []
      rw [segToks_blocks, List.append_nil]
    · show ((s0.root :: segBlocks s0) ++ []).Pairwise _
      rw [List.append_nil]
      exact (segBlocks_nodup hs).imp_of_mem fun ha hb hne =>
        hs.sep _ (segBlocks_sub hs _ ha) _ (segBlocks_sub hs _ hb) hne
  | s :: s' :: ss, hok, hpw, hch => by
    intro s0 h
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h
    subst s
    have hs := hok s0 List.mem_cons_self
    have hs' := hok s' (List.mem_cons_of_mem _ List.mem_cons_self)
    have hok' : ∀ t ∈ s' :: ss, SegOK F t := fun t ht => hok t (List.mem_cons_of_mem _ ht)
    rw [List.pairwise_cons] at hpw
    obtain ⟨hpw0, hpw'⟩ := hpw
    rw [List.isChain_cons_cons] at hch
    obtain ⟨hlink, hch'⟩ := hch
    obtain ⟨ig, ib, ip⟩ := chain_route F (s' :: ss) hok' hpw' hch' s' rfl
    -- the link offset is an S1 offset
    have hend : segEnd s0 ∈ s0.sel := segBlocks_sub hs _ (by
      unfold segEnd segBlocks
      split_ifs with hr
      · simp [hr]
      · exact List.getLast_mem _)
    have hS1 : s'.root - segEnd s0 ∈ S1off :=
      link_mem_S1 F (hs.sel_sub hend) (hs'.sel_sub hs'.root_mem)
        (hpw0 s' List.mem_cons_self _ hend _ hs'.root_mem) hs.exit_cov hlink
    refine ⟨?_, ?_, ?_⟩
    · -- grammar
      show route3.Gram 0 (segToks s0 ++ Tok.link (s'.root - segEnd s0) :: chainToks (s' :: ss))
      rw [WA.gram_append]
      obtain ⟨g1, g2⟩ := segToks_gram hs
      refine ⟨g1, rToks_link _ g2 _ hS1, ?_⟩
      exact ig
    · -- counted blocks
      show s0.root :: blocksOf s0.root (segToks s0 ++ Tok.link (s'.root - segEnd s0) :: chainToks (s' :: ss)) =
        (s0.root :: segBlocks s0) ++ chainBlocks (s' :: ss)
      rw [blocksOf_append, segToks_blocks, segToks_end]
      simp only [blocksOf, add_sub_cancel]
      rw [← ib]
      rfl
    · -- separation
      show ((s0.root :: segBlocks s0) ++ chainBlocks (s' :: ss)).Pairwise _
      rw [List.pairwise_append]
      refine ⟨(segBlocks_nodup hs).imp_of_mem fun ha hb hne =>
        hs.sep _ (segBlocks_sub hs _ ha) _ (segBlocks_sub hs _ hb) hne, ip, ?_⟩
      intro a ha b hb
      -- `b` lies in a later cluster
      have hb' : ∃ t ∈ s' :: ss, b ∈ t.sel := by
        have key : ∀ (ts : List Seg), (∀ t ∈ ts, SegOK F t) → ∀ b ∈ chainBlocks ts, ∃ t ∈ ts, b ∈ t.sel := by
          intro ts hts
          induction ts with
          | nil => intro b hb; simp [chainBlocks] at hb
          | cons t ts ih =>
            intro b hb
            simp only [chainBlocks, List.mem_append] at hb
            rcases hb with hb | hb
            · exact ⟨t, List.mem_cons_self, segBlocks_sub (hts t List.mem_cons_self) b hb⟩
            · obtain ⟨u, hu, hbu⟩ := ih (fun u hu => hts u (List.mem_cons_of_mem _ hu)) b hb
              exact ⟨u, List.mem_cons_of_mem _ hu, hbu⟩
        exact key (s' :: ss) hok' b hb
      obtain ⟨t, ht, hbt⟩ := hb'
      have haS := segBlocks_sub hs a ha
      exact selected_sep F (hs.sel_sub haS) ((hok' t ht).sel_sub hbt) (hpw0 t ht a haS b hbt)

end QECD1
