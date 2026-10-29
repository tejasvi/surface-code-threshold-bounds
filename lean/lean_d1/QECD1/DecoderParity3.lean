import QECD1.LinkChain3

/-!
# W0 and W1 from parity

The decoder interface has to supply W0 (`hW0`) and W1 (`W1Hyp`). In 2D they come from parity (TwoD/Parity,
TwoD/W1). The setting has three nested block sets:
* `F`, the bad blocks; their `a0`-components are the clusters (`clusterOf F`);
* `Fl ⊆ F`, the flagged blocks; their `a0`-components are the level-0 components (`clusterOf Fl`);
* `L ⊆ Fl`, the level-1 blocks, in unresolved level-0 components; their `a1`-components are the level-1 components.

`par b` is the residual parity of block `b` (the residual summed over its checks). It is nonzero only on flagged blocks,
since a block with an odd check is flagged.

The counting core does not depend on the dimension:
* `w0_of_parity`: assume the level-0 component of `c` has odd parity and its cluster has even parity (P1 for interior
  clusters). Then the cluster has a block at distance `≥ a0 + 1 = D` from `c`, in another level-0 component.
* `w1hyp_of_parity`: assume the level-1 component of `e` has odd parity, and the level-1 blocks of the clusters
  meeting it have even total parity (P2, 2D `lev1_parity`). Then `W1Hyp F L e` holds.
* `gen_skel3_parity`: `gen_skel3_family` with W0 and W1 replaced by these parity facts.

Both are one argument (`odd_outside`): a set of even total parity with a part of odd parity has a block of nonzero
parity outside the part.
-/

namespace QECD1

/-- **An even total with an odd part forces a block of nonzero parity outside the part.** -/
theorem odd_outside {S T : Finset V3} (hTS : T ⊆ S) (par : V3 → ZMod 2) (heven : ∑ b ∈ S, par b = 0)
    (hodd : ∑ b ∈ T, par b ≠ 0) : ∃ b ∈ S, b ∉ T ∧ par b ≠ 0 := by
  have h := Finset.sum_sdiff hTS (f := par)
  rw [heven] at h
  have hne : ∑ b ∈ S \ T, par b ≠ 0 := by
    intro h0
    rw [h0, zero_add] at h
    exact hodd h
  obtain ⟨b, hb, hpb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Finset.mem_sdiff] at hb
  exact ⟨b, hb.1, hb.2, hpb⟩

/-- Components grow with the set. -/
theorem sameComp_mono_set {F F' : Finset V3} (h : F ⊆ F') {a : ℕ} {x y : V3} (hxy : SameComp F a x y) :
    SameComp F' a x y := by
  induction hxy with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

/-- **W0 from parity.** -/
theorem w0_of_parity (F Fl : Finset V3) (hFl : Fl ⊆ F) (par : V3 → ZMod 2) (hpar : ∀ b, par b ≠ 0 → b ∈ Fl)
    {c : V3} (hc : c ∈ Fl) (hodd : ∑ b ∈ clusterOf Fl c, par b ≠ 0) (heven : ∑ b ∈ clusterOf F c, par b = 0) :
    ∃ b, SameComp F Const.a0 c b ∧ Const.D ≤ dist3 c b := by
  have hsub : clusterOf Fl c ⊆ clusterOf F c := by
    intro b hb
    obtain ⟨hbFl, hcb⟩ := mem_clusterOf.1 hb
    exact mem_clusterOf.2 ⟨hFl hbFl, sameComp_mono_set hFl hcb⟩
  obtain ⟨b, hbC, hbK, hpb⟩ := odd_outside hsub par heven hodd
  have hbFl := hpar b hpb
  refine ⟨b, (mem_clusterOf.1 hbC).2, ?_⟩
  have hnot : ¬ SameComp Fl Const.a0 c b := fun h => hbK (mem_clusterOf.2 ⟨hbFl, h⟩)
  rw [← a0_succ_eq_D]
  exact comp_sep Fl Const.a0 hc hbFl hnot

open Classical in
/-- **W1 from parity.** -/
theorem w1hyp_of_parity (F L : Finset V3) (par : V3 → ZMod 2) {e : V3}
    (hodd : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), par b ≠ 0)
    (heven : ∑ b ∈ L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b), par b = 0) :
    W1Hyp F L e := by
  have hsub : L.filter (fun b => SameComp L Const.a1 e b) ⊆
      L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, b, hb.1, hb.2, .refl⟩
  obtain ⟨c, hcU, hcK, _⟩ := odd_outside hsub par heven hodd
  rw [Finset.mem_filter] at hcU
  obtain ⟨hcL, k, _, hek, hkc⟩ := hcU
  refine ⟨c, hcL, ⟨k, hek, hkc⟩, fun h => hcK ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hcL, h⟩

open Classical in
/-- **Every family has a good skeleton, from parity facts.** The hypotheses are the decoder facts:
* `hpar`: blocks of nonzero residual parity are flagged;
* `hP0`: the level-0 component of each level-1 block has odd parity (it is unresolved);
* `hP1`: the cluster of each level-1 block has even parity (P1; its cluster is interior);
* `hodd1`: the level-1 component of `e` has odd parity (the family is unresolved);
* `hP2`: the level-1 blocks of the clusters meeting it have even total parity (P2);
* `hfam`: the exit `x ∈ L` is in the family of `e`. -/
theorem gen_skel3_parity (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F) (par : V3 → ZMod 2)
    (hpar : ∀ b, par b ≠ 0 → b ∈ Fl) (hP0 : ∀ r ∈ L, ∑ b ∈ clusterOf Fl r, par b ≠ 0)
    (hP1 : ∀ r ∈ L, ∑ b ∈ clusterOf F r, par b = 0) {e x : V3} (he : e ∈ L) (hx : x ∈ L)
    (hfam : InFamily3 F L e x) (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), par b ≠ 0)
    (hP2 : ∑ b ∈ L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b), par b = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ F) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_family F L (hLFl.trans hFl) he hx hfam
    (fun r hr => w0_of_parity F Fl hFl par hpar (hLFl hr) (hP0 r hr) (hP1 r hr))
    (w1hyp_of_parity F L par hodd1 hP2)

end QECD1
