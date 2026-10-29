import QECD1.ClusterChain

/-!
# The witness dichotomy (2D `fam_witness`, 3D, dimension-free)

`F` is the set of flagged blocks and `L ⊆ F` the set of level-1 blocks. The family is the level-1 component of its
landing root `e`, i.e. the blocks `k` with `SameComp L a1 e k`.

(W1) is a hypothesis here (`W1Hyp`). The decoder supplies it from the parity of the level-1 residual on interior
clusters (P2/W1). It gives a level-1 block `c` that lies in the cluster of a block of the family
but is itself in another level-1 component.

Take any cluster chain `e → x` of the family (`FChain3`, `x ∈ L`). Then one of two cases holds.
* (A) Some pair `j` of the chain has, in its cluster, a level-1 block `w` of another level-1 component than its root
  `(f j).1`. This happens in two ways:
  * the exit `(f j).2` itself is such a block (2D case α);
  * W1's block `c` lies in a route cluster (case α').

  Then `onroute_key` applies in that part, with `w` and its cover.
* (B) All roots and exits lie in the family, and W1's block `c` lies in no route cluster (case β). The witness is then
  an excursion (Excursion3).
-/

namespace QECD1

/-- **(W1) for the level-1 component of `e`**, as a named hypothesis: a level-1 block `c` in the cluster of some
block `k` of the component, itself in another level-1 component. -/
def W1Hyp (F L : Finset V3) (e : V3) : Prop :=
  ∃ c ∈ L, (∃ k, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k c) ∧ ¬ SameComp L Const.a1 e c

/-- The roots of a chain are level-1 blocks. -/
theorem chain_roots_mem {F L : Finset V3} {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (he : e ∈ L) : ∀ j ≤ n, (f j).1 ∈ L := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [hf.2.2.1]
    exact he
  · have := (hf.2.1 (j - 1) (by omega)).2.1
    rwa [show j - 1 + 1 = j by omega] at this

/-- The exits of a chain ending at a level-1 block are level-1 blocks. -/
theorem chain_exits_mem {F L : Finset V3} {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hx : x ∈ L) : ∀ j ≤ n, (f j).2 ∈ L := by
  intro j hj
  rcases eq_or_lt_of_le hj with h | h
  · rw [h, hf.2.2.2]
    exact hx
  · exact (hf.2.1 j h).1

/-- If every pair's root and exit lie in one level-1 component, all roots and exits lie in the component of `e`. -/
theorem chain_in_comp {F L : Finset V3} {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hα : ∀ j ≤ n, SameComp L Const.a1 (f j).1 (f j).2) :
    ∀ j ≤ n, SameComp L Const.a1 e (f j).1 ∧ SameComp L Const.a1 e (f j).2 := by
  intro j
  induction j with
  | zero =>
    intro h0
    have hr : (f 0).1 = e := hf.2.2.1
    have h1 : SameComp L Const.a1 e (f 0).1 := hr ▸ Relation.ReflTransGen.refl
    exact ⟨h1, h1.trans (hα 0 h0)⟩
  | succ j ih =>
    intro hj
    obtain ⟨hx, he', hd⟩ := hf.2.1 j (by omega)
    have h1 : SameComp L Const.a1 e (f (j + 1)).1 := (ih (by omega)).2.tail ⟨hx, he', hd⟩
    exact ⟨h1, h1.trans (hα (j + 1) hj)⟩

/-- **The witness dichotomy.** -/
theorem fam_witness3 (F L : Finset V3) {e x : V3} {n : ℕ} {f : ℕ → V3 × V3} (hf : FChain3 F L e x n f)
    (hx : x ∈ L) (hW1 : W1Hyp F L e) :
    (∃ j ≤ n, ∃ w ∈ L, SameComp F Const.a0 (f j).1 w ∧ ¬ SameComp L Const.a1 (f j).1 w) ∨
    ((∀ j ≤ n, SameComp L Const.a1 e (f j).1 ∧ SameComp L Const.a1 e (f j).2) ∧
      ∃ c ∈ L, (∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 c) ∧
        (∃ k, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k c) ∧ ¬ SameComp L Const.a1 e c) := by
  by_cases hα : ∃ j ≤ n, ¬ SameComp L Const.a1 (f j).1 (f j).2
  · -- case α: the exit of pair `j` is in another level-1 component than its root
    left
    obtain ⟨j, hj, hK⟩ := hα
    exact ⟨j, hj, (f j).2, chain_exits_mem hf hx j hj, (hf.1 j hj).2.2, hK⟩
  · have hα' : ∀ j ≤ n, SameComp L Const.a1 (f j).1 (f j).2 := by
      intro j hj
      by_contra h
      exact hα ⟨j, hj, h⟩
    have hK := chain_in_comp hf hα'
    obtain ⟨c, hcL, hk, hfar⟩ := hW1
    by_cases hon : ∃ j ≤ n, SameComp F Const.a0 (f j).1 c
    · -- case α': W1's block lies in a route cluster
      left
      obtain ⟨j, hj, hcj⟩ := hon
      exact ⟨j, hj, c, hcL, hcj, fun h => hfar ((hK j hj).1.trans h)⟩
    · -- case β: off the route
      right
      exact ⟨hK, c, hcL, fun j hj h => hon ⟨j, hj, h⟩, hk, hfar⟩

end QECD1
