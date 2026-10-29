import QECD1.ClusterChain
import QECD1.RouteFam

/-!
# The route of a family (2D `fam_route`, 3D, dimension-free)

Let `F` be the flagged blocks and `L ⊆ F` the level-1 blocks. Take any cluster chain from the entry `e` to the exit
`x`. Assume W0 for the possible roots, i.e. for `e` and for the level-1 blocks: each such root has a block of its
cluster at distance `≥ D`.

Then a route word exists with these properties:
* it starts at `e`, an actual block (R0);
* it is valid in the route grammar from `B`;
* its counted blocks are flagged and pairwise `D`-separated;
* it is a mark-free allowed route word of the family automaton of every axis, i.e. the `r1` of a family key.

The steps and leaves are `S0` offsets and the links `S1` offsets. Their single cover offset is `link_mem_S1`.
-/

namespace QECD1

/-- **The route of a family.** -/
theorem fam_route3 (F L : Finset V3) {e x : V3} (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f)
    (hW0 : ∀ r, (r = e ∨ r ∈ L) → ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) :
    ∃ segs : List Seg, segs.head?.map Seg.root = some e ∧
      route3.Gram 0 (chainToks segs) ∧ (chainBlocks segs).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ chainBlocks segs, b ∈ F) ∧
      ∀ i : Fin 3, (fam3 i).Gram 0 (chainToks segs) ∧ Tok.mark ∉ chainToks segs := by
  obtain ⟨n, f, hf, hdist⟩ := exists_min_fchain3 F L hex
  have hW0' : ∀ i ≤ n, ∃ b, SameComp F Const.a0 (f i).1 b ∧ Const.D ≤ dist3 (f i).1 b := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact hW0 _ (Or.inl hf.2.2.1)
    · have := (hf.2.1 (i - 1) (by omega)).2.1
      rw [show i - 1 + 1 = i by omega] at this
      exact hW0 _ (Or.inr this)
  obtain ⟨segs, hhead, hok, hpw, hch⟩ := fam_segs F L hf hdist hW0'
  cases hs : segs with
  | nil => rw [hs] at hhead; simp at hhead
  | cons s0 rest =>
    rw [hs] at hhead hok hpw hch
    obtain ⟨hg, -, hsep⟩ := chain_route F (s0 :: rest) hok hpw hch s0 rfl
    refine ⟨s0 :: rest, hhead, hg, hsep, ?_, fun i => chain_route_fam i _ hg⟩
    -- the counted blocks are flagged
    have key : ∀ (ts : List Seg), (∀ t ∈ ts, SegOK F t) → ∀ b ∈ chainBlocks ts, b ∈ F := by
      intro ts hts
      induction ts with
      | nil => intro b hb; simp [chainBlocks] at hb
      | cons t ts ih =>
        intro b hb
        simp only [chainBlocks, List.mem_append] at hb
        rcases hb with hb | hb
        · have ht := hts t List.mem_cons_self
          exact ht.sel_sub (segBlocks_sub ht b hb)
        · exact ih (fun u hu => hts u (List.mem_cons_of_mem _ hu)) b hb
    exact key (s0 :: rest) hok

end QECD1
