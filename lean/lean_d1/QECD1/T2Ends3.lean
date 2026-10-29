import QECD1.T2Strips3

/-!
# The end routes of a T2 path (3D)

The 3D analogue of the 2D `TwoD/T2Ends`. On the T2 path, `F_0` is the bottom-strip family at its start (if it
does not start at `b₁`) and `F_{m+1}` the top-strip family at its end (if it does not end at `b₂`). Without T1, `F_0`
has no block in the top strip and `F_{m+1}` none in the bottom strip.

* `exists_min_gchain3`: a shortest cluster chain between two block properties has distinct clusters, no start block
  after its first cluster and no end block before its last cluster.
* `w0_dec3`: (W0) for a level-1 block whose cluster has no declared block (P1 for the cluster, `p1_code3`).
* `lev_not_declared3`: a level-1 block is not declared (its level-0 component does not reach).
* `bot_route3`: a route in `F_0` from its last bottom-strip block `b0` (not counted) to the selected block covering a
  given block `x0` of `F_0`; a word of the route grammar from `A`, whose counted blocks lie strictly between the
  strips and are pairwise `D`-separated.
* `top_route3`: a route in `F_{m+1}` from a level-1 root `e` (not in the bottom strip), a word from `A` stopped before
  the first block in the top strip, so its end is within `A1 + h_s + 1` rows of the top; the route is empty if `e`
  itself lies in the top strip.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

/-! ### Lists -/

/-- Last element with a property: `a :: l = pre ++ b :: suf` with `P b` and no element of `suf` satisfying `P`. -/
theorem exists_last_split3 {α : Type} (P : α → Prop) (a : α) (l : List α) (ha : P a) :
    ∃ pre b suf, a :: l = pre ++ b :: suf ∧ P b ∧ ∀ x ∈ suf, ¬ P x := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], a, [], rfl, ha, fun x hx => absurd hx (by simp)⟩
  | append_singleton l c ih =>
    by_cases hc : P c
    · exact ⟨a :: l, c, [], by simp, hc, fun x hx => absurd hx (by simp)⟩
    · obtain ⟨pre, b, suf, he, hb, hsuf⟩ := ih
      refine ⟨pre, b, suf ++ [c], ?_, hb, fun x hx => ?_⟩
      · rw [← List.cons_append, he, List.append_assoc, List.cons_append]
      · rcases List.mem_append.1 hx with hx | hx
        · exact hsuf x hx
        · rw [List.mem_singleton.1 hx]
          exact hc

/-- First element with a property: `l = l1 ++ l2` with no element of `l1` satisfying `P` and `P` at the head of
`l2`. -/
theorem exists_first_split3 {α : Type} (P : α → Prop) (l : List α) :
    ∃ l1 l2, l = l1 ++ l2 ∧ (∀ x ∈ l1, ¬ P x) ∧ ∀ y ∈ l2.head?, P y := by
  induction l with
  | nil => exact ⟨[], [], rfl, fun x hx => absurd hx (by simp), fun y hy => absurd hy (by simp)⟩
  | cons a l ih =>
    by_cases ha : P a
    · refine ⟨[], a :: l, rfl, fun x hx => absurd hx (by simp), fun y hy => ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hy]
      exact ha
    · obtain ⟨l1, l2, he, h1, h2⟩ := ih
      refine ⟨a :: l1, l2, by rw [he, List.cons_append], fun x hx => ?_, h2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact h1 x hx

/-- The end of a chain word is the end of its last cluster. -/
theorem endOf_chainToks : ∀ (s : Seg) (ss : List Seg),
    endOf s.root (chainToks (s :: ss)) = segEnd ((s :: ss).getLast (List.cons_ne_nil _ _))
  | s, [] => segToks_end s
  | s, s' :: ss => by
    simp only [chainToks]
    rw [endOf_append, segToks_end]
    simp only [endOf, add_sub_cancel]
    rw [endOf_chainToks s' ss, List.getLast_cons (List.cons_ne_nil _ _)]

/-! ### Shortest chains between block properties -/

/-- A cluster chain whose first entry satisfies `Pst` and whose last exit satisfies `Pen`. -/
def GChain3 (F L : Finset V3) (Pst Pen : V3 → Prop) (n : ℕ) (f : ℕ → V3 × V3) : Prop :=
  (∀ i ≤ n, PairOK3 F (f i)) ∧ (∀ i < n, LinkOK3 L (f i).2 (f (i + 1)).1) ∧ Pst (f 0).1 ∧ Pen (f n).2

/-- **A shortest chain between block properties** has distinct clusters, no `Pst`-block after its first cluster, and
no `Pen`-block before its last cluster. -/
theorem exists_min_gchain3 {F L : Finset V3} {Pst Pen : V3 → Prop}
    (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), GChain3 F L Pst Pen n f) :
    ∃ (n : ℕ) (f : ℕ → V3 × V3), GChain3 F L Pst Pen n f ∧
      (∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ c ∈ clusterOf F (f i).1, ¬ Pst c) ∧
      (∀ i, i < n → ∀ c ∈ clusterOf F (f i).1, ¬ Pen c) := by
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → V3 × V3, GChain3 F L Pst Pen m g) → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨hP, hL, h0, hn⟩ := hf
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, ?_, ?_, ?_⟩
  · intro i j hij hjn hcl
    obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → V3 × V3, (∀ k < i, g k = f k) ∧
        g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
      ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
        fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
    have hg : GChain3 F L Pst Pen (n - (j - i)) g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases lt_trichotomy k i with hk' | hk' | hk'
        · rw [hg1 k hk']
          exact hP k (by omega)
        · rw [hk', hg2]
          obtain ⟨hei, _, _⟩ := hP i (by omega)
          obtain ⟨_, hxj, hclj⟩ := hP j hjn
          exact ⟨hei, hxj, hcl.trans hclj⟩
        · rw [hg3 k hk']
          exact hP _ (by omega)
      · rcases lt_trichotomy k i with hk' | hk' | hk'
        · rw [hg1 k hk']
          rcases (show k + 1 < i ∨ k + 1 = i by omega) with h' | h'
          · rw [hg1 (k + 1) h']
            exact hL k (by omega)
          · rw [h', hg2]
            have := hL k (by omega)
            rw [h'] at this
            exact this
        · rw [hk', hg2, hg3 (i + 1) (by omega), show i + 1 + (j - i) = j + 1 by omega]
          exact hL j (by omega)
        · rw [hg3 k hk', hg3 (k + 1) (by omega), show k + 1 + (j - i) = k + (j - i) + 1 by omega]
          exact hL _ (by omega)
      · rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          rw [hg2]
          exact h0
        · rw [hg1 0 hi]
          exact h0
      · rcases eq_or_lt_of_le (show i ≤ n - (j - i) by omega) with hi | hi
        · rw [← hi, hg2, show j = n by omega]
          exact hn
        · rw [hg3 _ hi, show n - (j - i) + (j - i) = n by omega]
          exact hn
    have := hmin _ ⟨g, hg⟩
    omega
  · intro i hi1 hin c hc hpc
    obtain ⟨hcF, hic⟩ := mem_clusterOf.1 hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → V3 × V3, g 0 = (c, (f i).2) ∧ ∀ k, 0 < k → g k = f (i + k) :=
      ⟨fun k => if k = 0 then (c, (f i).2) else f (i + k), by simp, fun k hk => by simp [show k ≠ 0 by omega]⟩
    have hg : GChain3 F L Pst Pen (n - i) g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with hk' | hk'
        · rw [hk', hg1]
          obtain ⟨_, hxi, hcli⟩ := hP i hin
          exact ⟨hcF, hxi, (sameComp_symm F _ hic).trans hcli⟩
        · rw [hg2 k hk']
          exact hP _ (by omega)
      · rcases Nat.eq_zero_or_pos k with hk' | hk'
        · subst hk'
          rw [hg1, Nat.zero_add, hg2 1 Nat.one_pos]
          exact hL i (by omega)
        · rw [hg2 k hk', hg2 (k + 1) (by omega), show i + (k + 1) = i + k + 1 by omega]
          exact hL _ (by omega)
      · rw [hg1]
        exact hpc
      · rcases Nat.eq_zero_or_pos (n - i) with hni | hni
        · rw [hni, hg1, show i = n by omega]
          exact hn
        · rw [hg2 _ hni, show i + (n - i) = n by omega]
          exact hn
    have := hmin _ ⟨g, hg⟩
    omega
  · intro i hin c hc hpc
    obtain ⟨hcF, hic⟩ := mem_clusterOf.1 hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → V3 × V3, (∀ k < i, g k = f k) ∧ g i = ((f i).1, c) :=
      ⟨fun k => if k < i then f k else ((f i).1, c), fun k hk => by simp [hk], by simp⟩
    have hg : GChain3 F L Pst Pen i g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases eq_or_lt_of_le hk with hk' | hk'
        · rw [hk', hg2]
          exact ⟨(hP i hin.le).1, hcF, hic⟩
        · rw [hg1 k hk']
          exact hP k (by omega)
      · rw [hg1 k hk]
        rcases (show k + 1 = i ∨ k + 1 < i by omega) with h' | h'
        · rw [h', hg2]
          have := hL k (by omega)
          rw [h'] at this
          exact this
        · rw [hg1 (k + 1) h']
          exact hL k (by omega)
      · rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          rw [hg2]
          exact h0
        · rw [hg1 0 hi]
          exact h0
      · rw [hg2]
        exact hpc
    have := hmin _ ⟨g, hg⟩
    omega

/-- **The path in one cluster**: a selection of the cluster of `r` rooted at `r` (covering the cluster within `D - 1`)
and a simple selection path from `r` to the selected block covering a given block `x` of the cluster. -/
theorem cluster_path3 {F : Finset V3} {r x : V3} (hr : r ∈ F) (hx : x ∈ clusterOf F r) :
    ∃ (S : Finset V3) (rest : List V3), IsSelection3 (clusterOf F r) S r Const.D Const.A0 ∧
      (∀ y ∈ clusterOf F r, ∃ b ∈ S, dist3 y b ≤ Const.D - 1) ∧ (r :: rest).Nodup ∧
      List.IsChain (selGraph S Const.A0).Adj (r :: rest) ∧
      dist3 x ((r :: rest).getLast (List.cons_ne_nil _ _)) ≤ Const.D - 1 := by
  obtain ⟨S, hS, hcov⟩ := selection_A0 (self_mem_clusterOf hr) (cluster_conn hr)
  obtain ⟨s, hs, hxs⟩ := hcov _ hx
  obtain ⟨rest, hnd, hch, hlast⟩ := exists_sel_path hS hs
  exact ⟨S, rest, hS, hcov, hnd, hch, by rw [hlast]; exact hxs⟩

/-- The blocks of the clusters of a chain lie in the family of its first entry. -/
theorem gchain_family3 {F L : Finset V3} (hLF : L ⊆ F) {n : ℕ} {f : ℕ → V3 × V3}
    (hP : ∀ i ≤ n, PairOK3 F (f i)) (hL : ∀ i < n, LinkOK3 L (f i).2 (f (i + 1)).1) :
    ∀ i ≤ n, ∀ c ∈ clusterOf F (f i).1, InFamily3 F L (f 0).1 c := by
  intro i
  induction i with
  | zero =>
    intro _ c hc
    obtain ⟨hcF, hrc⟩ := mem_clusterOf.1 hc
    exact Relation.ReflTransGen.single ⟨(hP 0 (Nat.zero_le _)).1, hcF, Or.inl hrc⟩
  | succ i ih =>
    intro hi c hc
    have hx : InFamily3 F L (f 0).1 (f i).2 := by
      obtain ⟨_, hxF, hrx⟩ := hP i (by omega)
      exact ih (by omega) _ (mem_clusterOf.2 ⟨hxF, hrx⟩)
    obtain ⟨hxL, heL, hd⟩ := hL i (by omega)
    have he : InFamily3 F L (f 0).1 (f (i + 1)).1 :=
      hx.tail ⟨hLF hxL, hLF heL, Or.inr ⟨hxL, heL, Relation.ReflTransGen.single ⟨hxL, heL, hd⟩⟩⟩
    obtain ⟨hcF, hrc⟩ := mem_clusterOf.1 hc
    exact he.tail ⟨(hP (i + 1) hi).1, hcF, Or.inl hrc⟩

/-- The blocks of a selection path lie in the selection. -/
theorem path_mem_sel {S : Finset V3} {A : ℕ} : ∀ (r : V3) (l : List V3), r ∈ S →
    List.IsChain (selGraph S A).Adj (r :: l) → ∀ b ∈ r :: l, b ∈ S
  | r, [], hr, _ => fun b hb => by rw [List.mem_singleton.1 hb]; exact hr
  | r, x :: l, hr, hch => by
    rw [List.isChain_cons_cons] at hch
    have hx := (selGraph_adj.1 hch.1).2.1
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hr
    · exact path_mem_sel x l hx hch.2 b hb

/-- Distinct blocks of a `D`-separated set are pairwise `D`-separated. -/
theorem sel_pairwise {S : Finset V3} {l : List V3} (hnd : l.Nodup) (hmem : ∀ b ∈ l, b ∈ S)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Const.D ≤ dist3 p q) : l.Pairwise (fun a b => Const.D ≤ dist3 a b) :=
  List.Pairwise.imp_of_mem (fun ha hb hab => hsep _ (hmem _ ha) _ (hmem _ hb) hab) hnd

theorem segEnd_mem_sel {F : Finset V3} {s : Seg} (hs : SegOK F s) : segEnd s ∈ s.sel :=
  path_mem_sel s.root s.rest hs.root_mem hs.chain _ (List.getLast_mem _)

theorem mem_chainBlocks : ∀ (segs : List Seg) (b : V3), b ∈ chainBlocks segs →
    ∃ s ∈ segs, b ∈ s.root :: segBlocks s
  | [], b, hb => by simp [chainBlocks] at hb
  | s :: ss, b, hb => by
    simp only [chainBlocks, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ⟨s, List.mem_cons_self, hb⟩
    · obtain ⟨s', hs', hb'⟩ := mem_chainBlocks ss b hb
      exact ⟨s', List.mem_cons_of_mem _ hs', hb'⟩

/-- A chain word ends after a cluster word, in state `A` or `C`. -/
theorem stAfter_chainToks {F : Finset V3} : ∀ (s : Seg) (ss : List Seg), (∀ t ∈ s :: ss, SegOK F t) →
    1 ≤ route3.stAfter 0 (chainToks (s :: ss))
  | s, [], hok => (segToks_gram (hok s List.mem_cons_self)).2
  | s, s' :: ss, hok => by
    simp only [chainToks]
    rw [WA.stAfter_append]
    exact stAfter_chainToks s' ss (fun t ht => hok t (List.mem_cons_of_mem _ ht))

/-- **The route of a cluster chain** with distinct clusters and (W0) at every root: a word of the route grammar from
`B`, ending in state `A` or `C`, whose blocks with the first root are pairwise `D`-separated and lie in the chain's
clusters, ending in the last cluster within `D - 1` of the last exit. -/
theorem fchain_route3 {F L : Finset V3} {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hdist : ∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1)
    (hW0 : ∀ i ≤ n, ∃ b, SameComp F Const.a0 (f i).1 b ∧ Const.D ≤ dist3 (f i).1 b) :
    ∃ ws : List Tok, route3.Gram 0 ws ∧ 1 ≤ route3.stAfter 0 ws ∧
      (e :: blocksOf e ws).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ e :: blocksOf e ws, ∃ i ≤ n, b ∈ clusterOf F (f i).1) ∧
      endOf e ws ∈ clusterOf F (f n).1 ∧ dist3 x (endOf e ws) ≤ Const.D - 1 := by
  obtain ⟨seg, hseg, -, hok, hpw, hch⟩ := fam_segs_data F L hf hdist hW0
  have he0 : (seg 0).root = e := (hseg 0 (Nat.zero_le _)).1.trans hf.2.2.1
  set ss : List Seg := (List.range n).map (fun i => seg (i + 1)) with hss
  have hsegs : (List.range (n + 1)).map seg = seg 0 :: ss := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  rw [hsegs] at hok hpw hch
  obtain ⟨hgram, hblk, hpw'⟩ := chain_route F (seg 0 :: ss) hok hpw hch (seg 0) (by simp)
  rw [he0] at hblk
  have hmemseg : ∀ s ∈ seg 0 :: ss, ∃ i ≤ n, s = seg i := by
    intro s hs
    rw [← hsegs] at hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
    exact ⟨i, by have := List.mem_range.1 hi; omega, rfl⟩
  have hlast : (seg 0 :: ss).getLast (List.cons_ne_nil _ _) = seg n := by
    have h1 : (seg 0 :: ss).getLast (List.cons_ne_nil _ _) =
        ((List.range (n + 1)).map seg).getLast (by simp) := by
      congr 1
      exact hsegs.symm
    rw [h1, List.getLast_map, List.getLast_range]
    rfl
  have hend : endOf e (chainToks (seg 0 :: ss)) = segEnd (seg n) := by
    rw [← he0, endOf_chainToks, hlast]
  have hokn := (hseg n le_rfl).2.2.2.1
  refine ⟨chainToks (seg 0 :: ss), hgram, stAfter_chainToks (seg 0) ss hok, by rw [hblk]; exact hpw', ?_, ?_, ?_⟩
  · intro b hb
    rw [hblk] at hb
    obtain ⟨s, hs, hbs⟩ := mem_chainBlocks _ b hb
    obtain ⟨i, hi, rfl⟩ := hmemseg s hs
    exact ⟨i, hi, (hseg i hi).2.2.1 (segBlocks_sub (hok _ hs) b hbs)⟩
  · rw [hend]
    exact (hseg n le_rfl).2.2.1 (segEnd_mem_sel hokn)
  · rw [hend]
    have := hokn.exit_cov
    rw [(hseg n le_rfl).2.1, hf.2.2.2] at this
    exact this

theorem getLast_split3 {α : Type} {a b : α} {l pre suf : List α} (hs : a :: l = pre ++ b :: suf) :
    (a :: l).getLast (List.cons_ne_nil _ _) = (b :: suf).getLast (List.cons_ne_nil _ _) := by
  have key : ∀ (M : List α) (hM : M = pre ++ b :: suf) (h1 : M ≠ []),
      M.getLast h1 = (b :: suf).getLast (List.cons_ne_nil _ _) := by
    intro M hM h1
    subst hM
    exact List.getLast_append_of_ne_nil h1 (List.cons_ne_nil _ _)
  exact key (a :: l) hs _

theorem blocksOf_link (cur v : V3) (ws : List Tok) :
    blocksOf cur (Tok.link v :: ws) = (cur + v) :: blocksOf (cur + v) ws := rfl

theorem endOf_link (cur v : V3) (ws : List Tok) : endOf cur (Tok.link v :: ws) = endOf (cur + v) ws := rfl

theorem stAfter_pathToks_one (cur : V3) (bs : List V3) : route3.stAfter 1 (pathToks cur bs) = 1 := by
  cases bs with
  | nil => rfl
  | cons b bs => exact pathToks_stAfter 1 cur b bs

/-- Blocks of different clusters are `D`-separated. -/
theorem sep_of_clusters {F : Finset V3} {r r' c d : V3} (hc : c ∈ clusterOf F r) (hd : d ∈ clusterOf F r')
    (hrr : ¬ SameComp F Const.a0 r r') : Const.D ≤ dist3 c d := by
  obtain ⟨hcF, hrc⟩ := mem_clusterOf.1 hc
  obtain ⟨hdF, hrd⟩ := mem_clusterOf.1 hd
  have hcd : ¬ SameComp F Const.a0 c d := fun hcd => hrr ((hrc.trans hcd).trans (sameComp_symm F _ hrd))
  have := comp_sep F Const.a0 hcF hdF hcd
  rw [← a0_succ_eq_D]
  exact this

/-- **A link between clusters** is an `S1` offset: from a block `s` of one cluster covering `x` within `D - 1` to a
block `e'` of another cluster within `a1` of `x`. -/
theorem link_of_clusters {F : Finset V3} {r r' s x e' : V3} (hs : s ∈ clusterOf F r) (he' : e' ∈ clusterOf F r')
    (hrr : ¬ SameComp F Const.a0 r r') (hcov : dist3 x s ≤ Const.D - 1) (hxe : dist3 x e' ≤ Const.a1) :
    e' - s ∈ S1off := by
  obtain ⟨hsF, hrs⟩ := mem_clusterOf.1 hs
  obtain ⟨heF, hre⟩ := mem_clusterOf.1 he'
  have hdiff : ¬ SameComp F Const.a0 s e' := fun hse =>
    hrr ((hrs.trans hse).trans (sameComp_symm F _ hre))
  exact link_mem_S1 F hsF heF hdiff hcov hxe

theorem gram_link (q : ℕ) (hq : 1 ≤ q) (v : V3) (hv : v ∈ S1off) (ws : List Tok) (hws : route3.Gram 0 ws) :
    route3.Gram q (Tok.link v :: ws) :=
  ⟨rToks_link q hq v hv, hws⟩

/-- **A prefix of steps, a link, and a chain word**: a word from `A`. Its blocks are the steps' blocks, the next
root and the chain word's blocks; it ends where the chain word ends. -/
theorem steps_link_chain (cur e : V3) (bs : List V3) (ws : List Tok)
    (hst : route3.Gram 1 (pathToks cur bs))
    (hlink : e - (cur :: bs).getLast (List.cons_ne_nil _ _) ∈ S1off) (hws : route3.Gram 0 ws) :
    route3.Gram 1 (pathToks cur bs ++ Tok.link (e - (cur :: bs).getLast (List.cons_ne_nil _ _)) :: ws) ∧
      blocksOf cur (pathToks cur bs ++ Tok.link (e - (cur :: bs).getLast (List.cons_ne_nil _ _)) :: ws) =
        bs ++ (e :: blocksOf e ws) ∧
      endOf cur (pathToks cur bs ++ Tok.link (e - (cur :: bs).getLast (List.cons_ne_nil _ _)) :: ws) =
        endOf e ws := by
  refine ⟨(route3.gram_append 1 _ _).2 ⟨hst, ?_⟩, ?_, ?_⟩
  · rw [stAfter_pathToks_one]
    exact gram_link 1 le_rfl _ hlink ws hws
  · rw [blocksOf_append, pathToks_blocks, pathToks_end, blocksOf_link, add_sub_cancel]
  · rw [endOf_append, pathToks_end, endOf_link, add_sub_cancel]

/-- The rows of two blocks differ by at most their distance. -/
theorem row_le_dist3 (a b : V3) : b.2.2 ≤ a.2.2 + dist3 a b := by
  have hd : (a - b).2.2.natAbs ≤ dist3 a b := by
    unfold dist3 linf
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Prod.snd_sub, Prod.snd_sub] at hd
  omega

theorem getLast_eq_of_eq {α : Type} {M M' : List α} (hM : M = M') (h1 : M ≠ []) (h2 : M' ≠ []) :
    M.getLast h1 = M'.getLast h2 := by
  subst hM
  rfl

/-- **The final cut**: steps along a selection path from `r`, stopped before the first block in the top strip. If
the path ends within `A1 + h_s + 1` rows of the top, so does the stop point. -/
theorem final_cut3 {S : Finset V3} {ny : ℕ} (r : V3) (rest : List V3)
    (hch : List.IsChain (selGraph S Const.A0).Adj (r :: rest))
    (hend : (ny : ℤ) ≤ ((r :: rest).getLast (List.cons_ne_nil _ _)).2.2 + 1 + hs3 + Const.A1) :
    ∃ l1 l2 : List V3, rest = l1 ++ l2 ∧ List.IsChain (selGraph S Const.A0).Adj (r :: l1) ∧
      (∀ b ∈ l1, b.2.2 + 1 + hs3 < ny) ∧
      (ny : ℤ) ≤ ((r :: l1).getLast (List.cons_ne_nil _ _)).2.2 + 1 + hs3 + Const.A1 := by
  obtain ⟨l1, l2, hsplit, h1, h2⟩ := exists_first_split3 (fun b : V3 => (ny : ℤ) ≤ b.2.2 + 1 + hs3) rest
  subst hsplit
  have hch' : List.IsChain (selGraph S Const.A0).Adj ((r :: l1) ++ l2) := hch
  rw [List.isChain_append] at hch'
  refine ⟨l1, l2, rfl, hch'.1, fun b hb => not_le.1 (h1 b hb), ?_⟩
  cases l2 with
  | nil =>
    rw [getLast_eq_of_eq (by rw [List.append_nil] : r :: (l1 ++ []) = r :: l1) _ (List.cons_ne_nil _ _)] at hend
    exact hend
  | cons y l2 =>
    have hy : (ny : ℤ) ≤ y.2.2 + 1 + hs3 := h2 y (by simp)
    have ht : (r :: l1).getLast? = some ((r :: l1).getLast (List.cons_ne_nil _ _)) :=
      List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)
    have hadj := hch'.2.2 _ ht y (by simp)
    have hd := (selGraph_adj.1 hadj).2.2.2
    have hrow := row_le_dist3 ((r :: l1).getLast (List.cons_ne_nil _ _)) y
    have hA : Const.A0 ≤ Const.A1 := by decide
    omega

namespace Stage13

variable (S : Stage13 T w h)

/-- **(W0) for an interior level-1 block** of the decoder: a level-1 block whose cluster contains no declared block
has a block of its cluster at distance `≥ D` (P1 for the cluster, A2, A3). -/
theorem w0_dec3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {r : V3}
    (hr : r ∈ S.levSet (reach3 T w h r0) E) (hnd : ∀ b ∈ clusterOf (S.badSet ny E) r, ¬ declared3 ny b) :
    ∃ b, SameComp (S.badSet ny E) Const.a0 r b ∧ Const.D ≤ dist3 r b := by
  have hFl := S.flSet_sub ny E
  have hA2 := S.flSet_hA2 E
  have hA3 := a3_code3 (S.Fcfg E) (S.badSet ny E) (S.badSet_hlong ny E)
  have hrFl : r ∈ S.flSet E := level1Set3_sub _ _ _ hr
  refine w0_of_parity (S.badSet ny E) (S.flSet E) hFl (blockPar3 (S.Fcfg E)) (hpar_of_A2 _ _ hA2) hrFl
    (level1Set3_odd hr) ?_
  exact p1_code3 (S.Fcfg E) _ (compUnion3 (S.Fcfg E) (clusterOf (S.badSet ny E) r)) (compUnion3_closed _ _)
    (interior_of_declared (S.Fcfg E) (S.badSet ny E) ny hh r (S.badSet_hdeclF ny E) hA3 hnd)
    (compUnion3_contains _ _) (compUnion3_odd _ _ _ hFl r hA2 hA3)

/-- **A level-1 block is not declared**: its level-0 component is unresolved, so it does not reach, while a block
of a declared row is within `r0` of a rough side. -/
theorem lev_not_declared3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {r : V3}
    (hr : r ∈ S.levSet (reach3 T w h r0) E) : ¬ declared3 ny r := by
  have hres := (mem_level1Set3.1 hr).2
  have hrFl : r ∈ S.flSet E := (mem_level1Set3.1 hr).1
  obtain ⟨c0, hc0, hrc⟩ : ∃ c0 : PVert3 T w h, True ∧ blockOf3 c0 = r := by
    obtain ⟨-, c0, hc0, -⟩ := Finset.mem_filter.1 hrFl
    exact ⟨c0, trivial, hc0⟩
  have hrK : r ∈ clusterOf (S.flSet E) r := self_mem_clusterOf hrFl
  intro hdecl
  apply hres
  right
  left
  have hr0 : r0 = 2 := by decide
  rcases hdecl with hlow | hhigh
  · refine ⟨(c0.1, c0.2.1, 0), ⟨r, hrK, ?_⟩, Or.inl rfl⟩
    rw [← hrc]
    simp only [dist3, linf, blockOf3, blockOf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, Fin.val_zero,
      Nat.cast_zero, Int.zero_ediv]
    rw [← hrc] at hlow
    simp only [blockOf3, blockOf, PVert3.toV3] at hlow
    rw [hr0]
    omega
  · refine ⟨(c0.1, c0.2.1, Fin.last h), ⟨r, hrK, ?_⟩, Or.inr rfl⟩
    rw [← hrc]
    rw [← hrc] at hhigh
    simp only [blockOf3, blockOf, PVert3.toV3] at hhigh
    simp only [dist3, linf, blockOf3, blockOf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, Fin.val_last]
    have hc := c0.2.2.isLt
    rw [hr0]
    omega

/-- **The bottom end route**: in a family with a block in the bottom strip and none in the top strip, a route from
the last bottom-strip block `b0` of a selection path (not counted) to the selected block covering a given block `x0`
of the family. It is a word from `A`; its counted blocks lie in the family strictly above the bottom strip and are
pairwise `D`-separated. -/
theorem bot_route3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E))
    (hbot : ∃ c ∈ Fm, c.2.2 ≤ hs3) (hntop : ∀ c ∈ Fm, c.2.2 + 1 + hs3 < ny) {x0 : V3} (hx0 : x0 ∈ Fm) :
    ∃ (b0 : V3) (ms : List Tok), b0 ∈ Fm ∧ b0.2.2 ≤ hs3 ∧ route3.Gram 1 ms ∧
      (∀ b ∈ blocksOf b0 ms, b ∈ Fm ∧ (hs3 : ℤ) < b.2.2) ∧
      (blocksOf b0 ms).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      endOf b0 ms ∈ Fm ∧ dist3 x0 (endOf b0 ms) ≤ Const.D - 1 := by
  have hLF : S.levSet (reach3 T w h r0) E ⊆ S.badSet ny E := S.levSet_sub _ ny E
  obtain ⟨c1, hc1, hr1⟩ := hbot
  obtain ⟨c0, -, hc0⟩ := mem_families3.1 hFm
  have hFmF : Fm ⊆ S.badSet ny E := by
    rw [← hc0]
    exact famF_sub _ _ _
  have hinfam : InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) c1 x0 := by
    have hx0' := hx0
    rw [← famF_eq_of_mem_families3 hFm hc1] at hx0'
    exact (mem_famF.1 hx0').2
  obtain ⟨n0, f0, hf0⟩ := exists_fchain3 _ _ hLF (hFmF hc1) hinfam
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, hnost, -⟩ :=
    exists_min_gchain3 (F := S.badSet ny E) (L := S.levSet (reach3 T w h r0) E)
      (Pst := fun c => c ∈ Fm ∧ c.2.2 ≤ hs3) (Pen := fun c => c = x0)
      ⟨n0, f0, hf0.1, hf0.2.1, ⟨by rw [hf0.2.2.1]; exact hc1, by rw [hf0.2.2.1]; exact hr1⟩, hf0.2.2.2⟩
  obtain ⟨h0F, h0r⟩ : (f 0).1 ∈ Fm ∧ (f 0).1.2.2 ≤ hs3 := h0
  have hn' : (f n).2 = x0 := hn
  -- every cluster of the chain lies in the family
  have hfam : ∀ i ≤ n, ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, c ∈ Fm := by
    intro i hi c hc
    have hinf := gchain_family3 hLF hP hL i hi c hc
    rw [← famF_eq_of_mem_families3 hFm h0F]
    exact mem_famF.2 ⟨(mem_clusterOf.1 hc).1, hinf⟩
  -- the clusters after the first lie strictly above the bottom strip
  have habove : ∀ i, 1 ≤ i → i ≤ n → ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, (hs3 : ℤ) < c.2.2 := by
    intro i hi1 hin c hc
    by_contra hle
    exact hnost i hi1 hin c hc ⟨hfam i hin c hc, not_lt.1 hle⟩
  -- the first cluster: a selection path from its entry to the cover of its exit, cut at its last bottom-strip block
  obtain ⟨hr0F, hx0F, hr0x⟩ := hP 0 (Nat.zero_le _)
  obtain ⟨Sel, rest0, hS0, -, hnd0, hch0, hxs0⟩ := cluster_path3 hr0F (mem_clusterOf.2 ⟨hx0F, hr0x⟩)
  have hmem0 : ∀ b ∈ (f 0).1 :: rest0, b ∈ Sel := path_mem_sel _ _ hS0.2.1 hch0
  have hK0 : ∀ b ∈ (f 0).1 :: rest0, b ∈ clusterOf (S.badSet ny E) (f 0).1 := fun b hb => hS0.1 (hmem0 b hb)
  obtain ⟨pre, b, suf, hsplit, hb, hsuf⟩ := exists_last_split3 (fun c : V3 => c.2.2 ≤ hs3) (f 0).1 rest0 h0r
  have hbmem : b ∈ (f 0).1 :: rest0 := by rw [hsplit]; simp
  have hsufmem : ∀ c ∈ suf, c ∈ (f 0).1 :: rest0 := fun c hc => by rw [hsplit]; simp [hc]
  have hchb : List.IsChain (selGraph Sel Const.A0).Adj (b :: suf) := by
    rw [hsplit] at hch0
    exact hch0.right_of_append
  have hndb : (b :: suf).Nodup := by
    rw [hsplit] at hnd0
    exact (List.nodup_append.1 hnd0).2.1
  have hlastb := getLast_split3 hsplit
  have hgram1 : route3.Gram 1 (pathToks b suf) := pathToks_gram hS0 1 le_rfl b suf hchb
  have hsufpw : suf.Pairwise (fun a b => Const.D ≤ dist3 a b) :=
    sel_pairwise (List.nodup_cons.1 hndb).2 (fun c hc => hmem0 c (hsufmem c hc)) hS0.2.2.1
  have hsufok : ∀ c ∈ suf, c ∈ Fm ∧ (hs3 : ℤ) < c.2.2 := fun c hc =>
    ⟨hfam 0 (Nat.zero_le _) c (hK0 c (hsufmem c hc)), not_le.1 (hsuf c hc)⟩
  have hsK : (b :: suf).getLast (List.cons_ne_nil _ _) ∈ clusterOf (S.badSet ny E) (f 0).1 := by
    rw [← hlastb]
    exact hK0 _ (List.getLast_mem _)
  have hbFm : b ∈ Fm := hfam 0 (Nat.zero_le _) b (hK0 b hbmem)
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: steps from `b` to the cover of `x0`
    subst hn0
    refine ⟨b, pathToks b suf, hbFm, hb, hgram1, ?_, ?_, ?_, ?_⟩
    · rw [pathToks_blocks]
      exact hsufok
    · rw [pathToks_blocks]
      exact hsufpw
    · rw [pathToks_end]
      exact hfam 0 le_rfl _ hsK
    · rw [pathToks_end, ← hlastb, ← hn']
      exact hxs0
  · -- several clusters: steps in the first cluster, a link, and the route of the later clusters
    have hgch : FChain3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (f 1).1 x0 (n - 1)
        (fun i => f (i + 1)) :=
      ⟨fun i hi => hP (i + 1) (by omega), fun i hi => hL (i + 1) (by omega), rfl,
        by show (f (n - 1 + 1)).2 = x0; rw [show n - 1 + 1 = n by omega]; exact hn'⟩
    have hgdist : ∀ i j, i < j → j ≤ n - 1 →
        ¬ SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 (f (j + 1)).1 :=
      fun i j hij hj => hdist (i + 1) (j + 1) (by omega) (by omega)
    have hgW0 : ∀ i ≤ n - 1, ∃ c, SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 c ∧
        Const.D ≤ dist3 (f (i + 1)).1 c := by
      intro i hi
      refine S.w0_dec3 hh (hL i (by omega)).2.1 fun c hc => not_declared_of_inter ⟨?_, ?_⟩
      · exact habove (i + 1) (by omega) (by omega) c hc
      · exact hntop c (hfam (i + 1) (by omega) c hc)
    obtain ⟨ws, hwsg, -, hwspw, hwsK, hwsend, hwsx⟩ := fchain_route3 hgch hgdist hgW0
    have hdiff : ¬ SameComp (S.badSet ny E) Const.a0 ((b :: suf).getLast (List.cons_ne_nil _ _)) (f 1).1 := by
      intro hcon
      exact hdist 0 1 (by omega) hn0 ((mem_clusterOf.1 hsK).2.trans hcon)
    have hlink : (f 1).1 - (b :: suf).getLast (List.cons_ne_nil _ _) ∈ S1off :=
      link_mem_S1 _ (mem_clusterOf.1 hsK).1 (hP 1 hn0).1 hdiff (by rw [← hlastb]; exact hxs0) (hL 0 hn0).2.2
    obtain ⟨hg, hblk, hend⟩ := steps_link_chain b (f 1).1 suf ws hgram1 hlink hwsg
    refine ⟨b, _, hbFm, hb, hg, ?_, ?_, ?_, ?_⟩
    · rw [hblk]
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hsufok c hc
      · obtain ⟨i, hi, hci⟩ := hwsK c hc
        exact ⟨hfam (i + 1) (by omega) c hci, habove (i + 1) (by omega) (by omega) c hci⟩
    · rw [hblk, List.pairwise_append]
      refine ⟨hsufpw, hwspw, fun c hc d hd => ?_⟩
      obtain ⟨i, hi, hdi⟩ := hwsK d hd
      exact sep_of_clusters (hK0 c (hsufmem c hc)) hdi (hdist 0 (i + 1) (by omega) (by omega))
    · rw [hend]
      exact hfam (n - 1 + 1) (by omega) _ hwsend
    · rw [hend]
      exact hwsx

set_option maxRecDepth 8000 in
/-- **The top end route**: in a family with a block in the top strip and none in the bottom strip, a route from a
level-1 root `e` of the family. It is a word from `A`, stopped before the first block in the top strip, so it ends
within `A1 + h_s + 1` rows of the top; its counted blocks lie in the family strictly below the top strip and, with
`e`, are pairwise `D`-separated. The route is empty if `e` lies in the top strip. -/
theorem top_route3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E))
    (htop : ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3) (hnbot : ∀ c ∈ Fm, (hs3 : ℤ) < c.2.2) {e : V3}
    (he : e ∈ Fm) :
    ∃ ms : List Tok, route3.Gram 1 ms ∧
      (∀ b ∈ blocksOf e ms, b ∈ Fm ∧ b.2.2 + 1 + hs3 < ny) ∧
      (e :: blocksOf e ms).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (ny : ℤ) ≤ (endOf e ms).2.2 + 1 + hs3 + Const.A1 := by
  by_cases hetop : (ny : ℤ) ≤ e.2.2 + 1 + hs3
  · refine ⟨[], trivial, fun b hb => absurd hb (by simp [blocksOf]), List.pairwise_singleton _ _, ?_⟩
    show (ny : ℤ) ≤ e.2.2 + 1 + hs3 + Const.A1
    omega
  have hLF : S.levSet (reach3 T w h r0) E ⊆ S.badSet ny E := S.levSet_sub _ ny E
  have hA0 : Const.D - 1 + Const.a1 = Const.A1 := by decide
  have hDA : Const.D - 1 ≤ Const.A1 := by decide
  obtain ⟨c2, hc2, hr2⟩ := htop
  obtain ⟨c0, -, hc0⟩ := mem_families3.1 hFm
  have hFmF : Fm ⊆ S.badSet ny E := by
    rw [← hc0]
    exact famF_sub _ _ _
  have hinfam : InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) e c2 := by
    have hc2' := hc2
    rw [← famF_eq_of_mem_families3 hFm he] at hc2'
    exact (mem_famF.1 hc2').2
  obtain ⟨n0, f0, hf0⟩ := exists_fchain3 _ _ hLF (hFmF he) hinfam
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, -, hnoen⟩ :=
    exists_min_gchain3 (F := S.badSet ny E) (L := S.levSet (reach3 T w h r0) E)
      (Pst := fun c => c = e) (Pen := fun c => (ny : ℤ) ≤ c.2.2 + 1 + hs3)
      ⟨n0, f0, hf0.1, hf0.2.1, hf0.2.2.1,
        by show (ny : ℤ) ≤ (f0 n0).2.2.2 + 1 + hs3; rw [hf0.2.2.2]; exact hr2⟩
  have h0' : (f 0).1 = e := h0
  have hn' : (ny : ℤ) ≤ (f n).2.2.2 + 1 + hs3 := hn
  have hfam : ∀ i ≤ n, ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, c ∈ Fm := by
    intro i hi c hc
    have hinf := gchain_family3 hLF hP hL i hi c hc
    rw [h0'] at hinf
    rw [← famF_eq_of_mem_families3 hFm he]
    exact mem_famF.2 ⟨(mem_clusterOf.1 hc).1, hinf⟩
  have hbelow : ∀ i, i < n → ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, c.2.2 + 1 + hs3 < ny :=
    fun i hin c hc => not_le.1 (hnoen i hin c hc)
  have hcl : ∀ i ≤ n, (f i).1 ∈ clusterOf (S.badSet ny E) (f i).1 := fun i hi =>
    self_mem_clusterOf (hP i hi).1
  -- the path of a cluster from its entry to the cover of its exit
  have hpath : ∀ i ≤ n, ∃ (Sel : Finset V3) (rest : List V3),
      IsSelection3 (clusterOf (S.badSet ny E) (f i).1) Sel (f i).1 Const.D Const.A0 ∧ ((f i).1 :: rest).Nodup ∧
      List.IsChain (selGraph Sel Const.A0).Adj ((f i).1 :: rest) ∧
      dist3 (f i).2 (((f i).1 :: rest).getLast (List.cons_ne_nil _ _)) ≤ Const.D - 1 := by
    intro i hi
    obtain ⟨hrF, hxF, hrx⟩ := hP i hi
    obtain ⟨Sel, rest, hS, -, hnd, hch, hxs⟩ := cluster_path3 hrF (mem_clusterOf.2 ⟨hxF, hrx⟩)
    exact ⟨Sel, rest, hS, hnd, hch, hxs⟩
  -- the last cluster: its path, cut before the top strip
  obtain ⟨Seln, restn, hSn, hndn, hchn, hxsn⟩ := hpath n le_rfl
  have hendn : (ny : ℤ) ≤ (((f n).1 :: restn).getLast (List.cons_ne_nil _ _)).2.2 + 1 + hs3 + Const.A1 := by
    have h1 := row_le_dist3 (((f n).1 :: restn).getLast (List.cons_ne_nil _ _)) (f n).2
    rw [dist3_comm] at h1
    omega
  obtain ⟨l1, l2, hsplitn, hchl1, hbl1, hhl1⟩ := final_cut3 (f n).1 restn hchn hendn
  have hmemn : ∀ b ∈ (f n).1 :: restn, b ∈ Seln := path_mem_sel _ _ hSn.2.1 hchn
  have hl1sub : ∀ b ∈ (f n).1 :: l1, b ∈ (f n).1 :: restn := by
    intro b hb
    rw [hsplitn]
    rcases List.mem_cons.1 hb with rfl | hb
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hb)
  have hl1nd : ((f n).1 :: l1).Nodup := by
    rw [hsplitn, ← List.cons_append] at hndn
    exact (List.nodup_append.1 hndn).1
  have hl1pw : ((f n).1 :: l1).Pairwise (fun a b => Const.D ≤ dist3 a b) :=
    sel_pairwise hl1nd (fun b hb => hmemn b (hl1sub b hb)) hSn.2.2.1
  have hl1K : ∀ b ∈ (f n).1 :: l1, b ∈ clusterOf (S.badSet ny E) (f n).1 := fun b hb =>
    hSn.1 (hmemn b (hl1sub b hb))
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: steps from `e`, cut before the top strip
    subst hn0
    rw [h0'] at hchl1 hhl1 hl1pw hl1K
    refine ⟨pathToks e l1, pathToks_gram hSn 1 le_rfl _ l1 hchl1, ?_, ?_, ?_⟩
    · rw [pathToks_blocks]
      intro b hb
      exact ⟨hfam 0 le_rfl b (by rw [h0']; exact hl1K b (List.mem_cons_of_mem _ hb)), hbl1 b hb⟩
    · rw [pathToks_blocks]
      exact hl1pw
    · rw [pathToks_end]
      exact hhl1
  -- several clusters: the prefix through the clusters before the last
  have hpre : ∃ wp : List Tok, route3.Gram 1 wp ∧ 1 ≤ route3.stAfter 1 wp ∧
      (∀ b ∈ blocksOf e wp, ∃ i, i < n ∧ b ∈ clusterOf (S.badSet ny E) (f i).1) ∧
      (e :: blocksOf e wp).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      endOf e wp ∈ clusterOf (S.badSet ny E) (f (n - 1)).1 ∧
      dist3 (f (n - 1)).2 (endOf e wp) ≤ Const.D - 1 := by
    obtain ⟨Sel0, rest0, hS0, hnd0, hch0, hxs0⟩ := hpath 0 (Nat.zero_le _)
    rw [h0'] at hS0 hnd0 hch0 hxs0
    have hmem0 : ∀ b ∈ e :: rest0, b ∈ Sel0 := path_mem_sel _ _ hS0.2.1 hch0
    have hK0 : ∀ b ∈ e :: rest0, b ∈ clusterOf (S.badSet ny E) (f 0).1 := by
      intro b hb
      rw [h0']
      exact hS0.1 (hmem0 b hb)
    have hpw0 : (e :: rest0).Pairwise (fun a b => Const.D ≤ dist3 a b) := sel_pairwise hnd0 hmem0 hS0.2.2.1
    have hg0 : route3.Gram 1 (pathToks e rest0) := pathToks_gram hS0 1 le_rfl e rest0 hch0
    have hs0K := hK0 _ (List.getLast_mem (List.cons_ne_nil e rest0))
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · -- two clusters: the prefix is the path of the first
      have hn1' : n = 1 := by omega
      subst hn1'
      refine ⟨pathToks e rest0, hg0, by rw [stAfter_pathToks_one], ?_, ?_, ?_, ?_⟩
      · rw [pathToks_blocks]
        intro b hb
        exact ⟨0, Nat.one_pos, hK0 b (List.mem_cons_of_mem _ hb)⟩
      · rw [pathToks_blocks]
        exact hpw0
      · rw [pathToks_end]
        exact hs0K
      · rw [pathToks_end]
        exact hxs0
    · -- three or more clusters: the path of the first, a link, and the route of the middle clusters
      have hgch : FChain3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (f 1).1 (f (n - 1)).2 (n - 2)
          (fun i => f (i + 1)) :=
        ⟨fun i hi => hP (i + 1) (by omega), fun i hi => hL (i + 1) (by omega), rfl,
          by show (f (n - 2 + 1)).2 = (f (n - 1)).2; rw [show n - 2 + 1 = n - 1 by omega]⟩
      have hgdist : ∀ i j, i < j → j ≤ n - 2 →
          ¬ SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 (f (j + 1)).1 :=
        fun i j hij hj => hdist (i + 1) (j + 1) (by omega) (by omega)
      have hgW0 : ∀ i ≤ n - 2, ∃ c, SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 c ∧
          Const.D ≤ dist3 (f (i + 1)).1 c := by
        intro i hi
        refine S.w0_dec3 hh (hL i (by omega)).2.1 fun c hc => not_declared_of_inter ⟨?_, ?_⟩
        · exact hnbot c (hfam (i + 1) (by omega) c hc)
        · exact hbelow (i + 1) (by omega) c hc
      obtain ⟨ws, hwsg, hwsst, hwspw, hwsK, hwsend, hwsx⟩ := fchain_route3 hgch hgdist hgW0
      have hl01 : dist3 (f 0).2 (f 1).1 ≤ Const.a1 := (hL 0 (by omega)).2.2
      have hcl1 : (f 1).1 ∈ clusterOf (S.badSet ny E) (f 1).1 := hcl 1 (by omega)
      have hd01 : ¬ SameComp (S.badSet ny E) Const.a0 (f 0).1 (f 1).1 := hdist 0 1 (by omega) (by omega)
      have hlink := link_of_clusters hs0K hcl1 hd01 hxs0 hl01
      obtain ⟨hg, hblk, hend⟩ := steps_link_chain e (f 1).1 rest0 ws hg0 hlink hwsg
      refine ⟨pathToks e rest0 ++ Tok.link ((f 1).1 - (e :: rest0).getLast (List.cons_ne_nil _ _)) :: ws, hg,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [WA.stAfter_append, stAfter_pathToks_one]
        exact hwsst
      · rw [hblk]
        intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact ⟨0, by omega, hK0 b (List.mem_cons_of_mem _ hb)⟩
        · obtain ⟨i, hi, hbi⟩ := hwsK b hb
          exact ⟨i + 1, by omega, hbi⟩
      · rw [hblk, ← List.cons_append, List.pairwise_append]
        refine ⟨hpw0, hwspw, fun c hc d hd => ?_⟩
        obtain ⟨i, hi, hdi⟩ := hwsK d hd
        exact sep_of_clusters (hK0 c hc) hdi (hdist 0 (i + 1) (by omega) (by omega))
      · rw [hend]
        have := hwsend
        rw [show n - 2 + 1 = n - 1 by omega] at this
        exact this
      · rw [hend]
        exact hwsx
  obtain ⟨wp, hwpg, hwpst, hwpK, hwppw, hwpend, hwpx⟩ := hpre
  have hwpok : ∀ b ∈ blocksOf e wp, b ∈ Fm ∧ b.2.2 + 1 + hs3 < ny := by
    intro b hb
    obtain ⟨i, hi, hbi⟩ := hwpK b hb
    exact ⟨hfam i hi.le b hbi, hbelow i hi b hbi⟩
  have hlinkn : dist3 (f (n - 1)).2 (f n).1 ≤ Const.a1 := by
    have := (hL (n - 1) (by omega)).2.2
    rw [show n - 1 + 1 = n by omega] at this
    exact this
  by_cases hrtop : (ny : ℤ) ≤ (f n).1.2.2 + 1 + hs3
  · -- the root of the last cluster is in the top strip: the prefix is the route
    refine ⟨wp, hwpg, hwpok, hwppw, ?_⟩
    have h1 := row_le_dist3 (endOf e wp) (f n).1
    have h2 := dist3_triangle (endOf e wp) (f (n - 1)).2 (f n).1
    rw [dist3_comm] at hwpx
    omega
  · -- a link into the last cluster, then its path cut before the top strip
    have hdiffn : ¬ SameComp (S.badSet ny E) Const.a0 (endOf e wp) (f n).1 := by
      intro hcon
      exact hdist (n - 1) n (by omega) le_rfl ((mem_clusterOf.1 hwpend).2.trans hcon)
    have hlink : (f n).1 - endOf e wp ∈ S1off :=
      link_mem_S1 _ (mem_clusterOf.1 hwpend).1 (hP n le_rfl).1 hdiffn hwpx hlinkn
    have hgl : route3.Gram 0 (pathToks (f n).1 l1) := pathToks_gram hSn 0 (Nat.zero_le _) _ l1 hchl1
    refine ⟨wp ++ Tok.link ((f n).1 - endOf e wp) :: pathToks (f n).1 l1, ?_, ?_, ?_, ?_⟩
    · rw [WA.gram_append]
      exact ⟨hwpg, gram_link _ hwpst _ hlink _ hgl⟩
    · rw [blocksOf_append, blocksOf_link, add_sub_cancel, pathToks_blocks]
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hwpok b hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨hfam n le_rfl _ (hcl n le_rfl), not_le.1 hrtop⟩
        · exact ⟨hfam n le_rfl b (hl1K b (List.mem_cons_of_mem _ hb)), hbl1 b hb⟩
    · rw [blocksOf_append, blocksOf_link, add_sub_cancel, pathToks_blocks, ← List.cons_append,
        List.pairwise_append]
      refine ⟨hwppw, hl1pw, fun c hc d hd => ?_⟩
      have hdK := hl1K d hd
      rcases List.mem_cons.1 hc with rfl | hc
      · rw [← h0'] at *
        exact sep_of_clusters (hcl 0 (Nat.zero_le _)) hdK (hdist 0 n hn0 le_rfl)
      · obtain ⟨i, hi, hci⟩ := hwpK c hc
        exact sep_of_clusters hci hdK (hdist i n hi le_rfl)
    · rw [endOf_append, endOf_link, add_sub_cancel, pathToks_end]
      exact hhl1

end Stage13

end QECD1
