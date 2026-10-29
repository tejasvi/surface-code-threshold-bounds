import QECD1.SkelRoute

/-!
# Cluster chains: from a chain of clusters to the segments of a skeleton route

This ports the 2D `FChain`, `exists_min_fchain` and the segment construction of `fam_route` (TwoD/T2Skel) to 3D,
dimension-free. The setting:
* `F` is the set of flagged blocks; the clusters are its `a0`-components (`SameComp F a0`);
* `L ⊆ F` is the set of level-1 blocks, which the links join.

A chain from the entry `e` to the exit `x` is a sequence of pairs `(entry_i, exit_i)`. The two blocks of each pair
are in one cluster. Each exit is within `a1` of the next entry, both being level-1 blocks.

* `exists_min_fchain3`: a shortest chain has pairwise different clusters, because a repeated cluster could be cut
  out.
* `clusterOf`, `cluster_conn`: a cluster as a finite set, `a0`-connected from any of its blocks.
* `fam_segs`: from a chain with distinct clusters, and W0 for its roots (each root's cluster has a block `≥ D` from
  it), build the segments. Each is a selection rooted at the entry, a simple path to the selected block covering the
  exit, and a leaf. They satisfy `SegOK`, are pairwise different clusters, and are linked within `a1`. So
  `chain_route` applies. `fam_segs_data` also keeps each segment's root, exit, and covering selection of its cluster,
  which the witness branch needs (GenKey3).
* `fam_route3`: the route word of the chain is valid from `B`, its counted blocks are pairwise `D`-separated, and it
  is a family route word of every axis (`chain_route_fam`, in RouteFam).
-/

namespace QECD1

/-- An entry/exit pair in one cluster. -/
def PairOK3 (F : Finset V3) (p : V3 × V3) : Prop := p.1 ∈ F ∧ p.2 ∈ F ∧ SameComp F Const.a0 p.1 p.2

/-- A level-1 link from an exit to the next entry. -/
def LinkOK3 (L : Finset V3) (x e : V3) : Prop := x ∈ L ∧ e ∈ L ∧ dist3 x e ≤ Const.a1

/-- A cluster chain with fixed ends: pairs `f 0, …, f n`, entry `e`, exit `x`. -/
def FChain3 (F L : Finset V3) (e x : V3) (n : ℕ) (f : ℕ → V3 × V3) : Prop :=
  (∀ i ≤ n, PairOK3 F (f i)) ∧ (∀ i < n, LinkOK3 L (f i).2 (f (i + 1)).1) ∧ (f 0).1 = e ∧ (f n).2 = x

/-- **A shortest chain with fixed ends has pairwise different clusters.** -/
theorem exists_min_fchain3 (F L : Finset V3) {e x : V3} (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f) :
    ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f ∧
      ∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1 := by
  classical
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → V3 × V3, FChain3 F L e x m g) → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨hP, hL, h0, hn⟩ := hf
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, ?_⟩
  intro i j hij hjn hcl
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → V3 × V3, (∀ k < i, g k = f k) ∧
      g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
    ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
      fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
  have hg : FChain3 F L e x (n - (j - i)) g := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        exact hP k (by omega)
      · rw [h, hg2]
        obtain ⟨hei, _, _⟩ := hP i (by omega)
        obtain ⟨_, hxj, hclj⟩ := hP j hjn
        exact ⟨hei, hxj, hcl.trans hclj⟩
      · rw [hg3 k h]
        exact hP _ (by omega)
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        rcases (show k + 1 < i ∨ k + 1 = i by omega) with h' | h'
        · rw [hg1 (k + 1) h']
          exact hL k (by omega)
        · rw [h', hg2]
          have := hL k (by omega)
          rw [h'] at this
          exact this
      · rw [h, hg2, hg3 (i + 1) (by omega), show i + 1 + (j - i) = j + 1 by omega]
        exact hL j (by omega)
      · rw [hg3 k h, hg3 (k + 1) (by omega), show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hL _ (by omega)
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [hg2]
        exact h0
      · rw [hg1 0 h]
        exact h0
    · rcases eq_or_lt_of_le (show i ≤ n - (j - i) by omega) with h | h
      · rw [← h, hg2, show j = n by omega]
        exact hn
      · rw [hg3 _ h, show n - (j - i) + (j - i) = n by omega]
        exact hn
  have := hmin _ ⟨g, hg⟩
  omega

/-- The cluster of `r` as a finite set. -/
noncomputable def clusterOf (F : Finset V3) (r : V3) : Finset V3 :=
  by classical exact F.filter fun y => SameComp F Const.a0 r y

theorem mem_clusterOf {F : Finset V3} {r y : V3} : y ∈ clusterOf F r ↔ y ∈ F ∧ SameComp F Const.a0 r y := by
  classical
  unfold clusterOf
  rw [Finset.mem_filter]

/-- **A cluster is `a0`-connected from any of its blocks.** -/
theorem cluster_conn {F : Finset V3} {r : V3} (hr : r ∈ F) :
    ∀ y ∈ clusterOf F r, Relation.ReflTransGen
      (fun a b => a ∈ clusterOf F r ∧ b ∈ clusterOf F r ∧ dist3 a b ≤ Const.a0) r y := by
  intro y hy
  have hry := (mem_clusterOf.1 hy).2
  -- every block along the a0-walk is in the cluster
  have key : ∀ z, SameComp F Const.a0 r z → Relation.ReflTransGen
      (fun a b => a ∈ clusterOf F r ∧ b ∈ clusterOf F r ∧ dist3 a b ≤ Const.a0) r z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | @tail b c hrb hbc ih =>
      have hb : b ∈ clusterOf F r := mem_clusterOf.2 ⟨hbc.1, hrb⟩
      have hc : c ∈ clusterOf F r := mem_clusterOf.2 ⟨hbc.2.1, hrb.tail hbc⟩
      exact ih.tail ⟨hb, hc, hbc.2.2⟩
  exact key y hry

theorem self_mem_clusterOf {F : Finset V3} {r : V3} (hr : r ∈ F) : r ∈ clusterOf F r :=
  mem_clusterOf.2 ⟨hr, .refl⟩

/-- The segment data of one cluster, with its properties (conditional on `i ≤ n`): the selection lies in the
cluster, the segment is valid, and the selection is a selection of the cluster rooted at the entry that covers the
cluster within `D - 1`. -/
theorem seg_data (F L : Finset V3) (n : ℕ) (f : ℕ → V3 × V3) (hP : ∀ i ≤ n, PairOK3 F (f i))
    (hW0 : ∀ i ≤ n, ∃ b, SameComp F Const.a0 (f i).1 b ∧ Const.D ≤ dist3 (f i).1 b) (i : ℕ) :
    ∃ (S : Finset V3) (rest : List V3) (leaf : V3), i ≤ n →
      S ⊆ clusterOf F (f i).1 ∧ SegOK F ⟨(f i).1, S, rest, leaf, (f i).2⟩ ∧
        IsSelection3 (clusterOf F (f i).1) S (f i).1 Const.D Const.A0 ∧
        ∀ y ∈ clusterOf F (f i).1, ∃ b ∈ S, dist3 y b ≤ Const.D - 1 := by
  by_cases hi : i ≤ n
  · obtain ⟨hr, hx, hrx⟩ := hP i hi
    obtain ⟨S, hS, hcov⟩ := selection_A0 (self_mem_clusterOf hr) (cluster_conn hr)
    have hxK : (f i).2 ∈ clusterOf F (f i).1 := mem_clusterOf.2 ⟨hx, hrx⟩
    obtain ⟨s, hs, hxs⟩ := hcov _ hxK
    obtain ⟨rest, hnd, hch, hlast⟩ := exists_sel_path hS hs
    obtain ⟨b, hrb, hfar⟩ := hW0 i hi
    have hbF : b ∈ F := by
      rcases Relation.ReflTransGen.cases_tail hrb with h | ⟨c, _, hcb⟩
      · rw [h]; exact hr
      · exact hcb.2.1
    have hbK : b ∈ clusterOf F (f i).1 := mem_clusterOf.2 ⟨hbF, hrb⟩
    obtain ⟨l, hl, hlne, hld⟩ := exists_leaf hS hcov hbK hfar
    refine ⟨S, rest, l, fun _ => ⟨hS.1, ?_, hS, hcov⟩⟩
    have hSF : S ⊆ F := fun y hy => (mem_clusterOf.1 (hS.1 hy)).1
    refine ⟨hSF, hS.2.1, hS.2.2.1, hnd, hch, fun _ => ⟨hl, hlne, hld⟩, hx, ?_⟩
    show dist3 (f i).2 (segEnd ⟨(f i).1, S, rest, l, (f i).2⟩) ≤ Const.D - 1
    unfold segEnd
    simp only
    rw [hlast]
    exact hxs
  · exact ⟨∅, [], (0 : V3), fun h => absurd h hi⟩

/-- **The segments of a chain with distinct clusters, with their data.** Segment `i` has root `(f i).1` and exit
`(f i).2`; its selection is a selection of the cluster of the root that covers the cluster. The list of segments is
valid, has pairwise different clusters, and is linked within `a1`. -/
theorem fam_segs_data (F L : Finset V3) {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hdist : ∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1)
    (hW0 : ∀ i ≤ n, ∃ b, SameComp F Const.a0 (f i).1 b ∧ Const.D ≤ dist3 (f i).1 b) :
    ∃ seg : ℕ → Seg, (∀ i ≤ n, (seg i).root = (f i).1 ∧ (seg i).exit = (f i).2 ∧
        (seg i).sel ⊆ clusterOf F (f i).1 ∧ SegOK F (seg i) ∧
        IsSelection3 (clusterOf F (f i).1) (seg i).sel (f i).1 Const.D Const.A0 ∧
        ∀ y ∈ clusterOf F (f i).1, ∃ b ∈ (seg i).sel, dist3 y b ≤ Const.D - 1) ∧
      ((List.range (n + 1)).map seg).head?.map Seg.root = some e ∧
      (∀ s ∈ (List.range (n + 1)).map seg, SegOK F s) ∧
      ((List.range (n + 1)).map seg).Pairwise
        (fun s s' => ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q) ∧
      ((List.range (n + 1)).map seg).IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1) := by
  obtain ⟨hP, hL, h0, _⟩ := hf
  choose S rest leaf hdat using seg_data F L n f hP hW0
  set seg : ℕ → Seg := fun i => ⟨(f i).1, S i, rest i, leaf i, (f i).2⟩
  refine ⟨seg, fun i hi => ⟨rfl, rfl, (hdat i hi).1, (hdat i hi).2.1, (hdat i hi).2.2.1, (hdat i hi).2.2.2⟩,
    ?_, ?_, ?_, ?_⟩
  · simp [seg, List.range_succ_eq_map, h0]
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
    exact (hdat i (by have := List.mem_range.1 hi; omega)).2.1
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij p hp q hq hpq => ?_
    have hin := List.mem_range.1 hi
    have hjn := List.mem_range.1 hj
    have hpK := (mem_clusterOf.1 ((hdat i (by omega)).1 hp)).2
    have hqK := (mem_clusterOf.1 ((hdat j (by omega)).1 hq)).2
    exact hdist i j hij (by omega) ((hpK.trans hpq).trans (sameComp_symm F _ hqK))
  · rw [List.isChain_map, List.isChain_range_succ]
    intro m hm
    exact (hL m hm).2.2

/-- **The segments of a chain with distinct clusters.** -/
theorem fam_segs (F L : Finset V3) {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hdist : ∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1)
    (hW0 : ∀ i ≤ n, ∃ b, SameComp F Const.a0 (f i).1 b ∧ Const.D ≤ dist3 (f i).1 b) :
    ∃ segs : List Seg, segs.head?.map Seg.root = some e ∧ (∀ s ∈ segs, SegOK F s) ∧
      segs.Pairwise (fun s s' => ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q) ∧
      segs.IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1) := by
  obtain ⟨seg, -, h1, h2, h3, h4⟩ := fam_segs_data F L hf hdist hW0
  exact ⟨_, h1, h2, h3, h4⟩

end QECD1
