import QECD1.Encode3

/-!
# Families: from linked blocks to cluster chains (2D `exists_fchain`, `exists_partial_chain`)

In the decoder, `F` is the set of bad blocks, its `a0`-components are the clusters, and `L ⊆ F` is the set of level-1
blocks. Two blocks are linked when they lie in one cluster or in one level-1 component (an `a1`-component of `L`). The
family of a block is its linked closure (2D `Stage1.linked`, `Stage1.family`).

* `exists_fchain3`: every block `x` of the family of a block `e ∈ F` is reached by a cluster chain `e → x`
  (`FChain3`). A cluster step extends the current pair (`fchain3_extend_pair`). A level-1 step is a sequence of links
  within `a1`, each followed by the trivial pair of its target (`fchain3_extend_link`, `fchain3_extend_comp`).
* `gen_skel3_family`: `gen_skel3` with the chain hypothesis replaced by family membership. What the decoder must
  supply is then: `F`, `L ⊆ F`, the exit `x ∈ L` of the family, W0 and W1.
-/

namespace QECD1

/-- Two blocks are linked: in one cluster, or in one level-1 component. -/
def Linked3 (F L : Finset V3) (c c' : V3) : Prop :=
  c ∈ F ∧ c' ∈ F ∧ (SameComp F Const.a0 c c' ∨ (c ∈ L ∧ c' ∈ L ∧ SameComp L Const.a1 c c'))

/-- `x` is in the family of `e`: linked to `e` through a sequence of links. -/
def InFamily3 (F L : Finset V3) (e x : V3) : Prop := Relation.ReflTransGen (Linked3 F L) e x

/-- A cluster step extends the last pair of a chain. -/
theorem fchain3_extend_pair {F L : Finset V3} {e b c : V3} {n : ℕ} {f : ℕ → V3 × V3}
    (hf : FChain3 F L e b n f) (hbc : SameComp F Const.a0 b c) (hc : c ∈ F) :
    ∃ g : ℕ → V3 × V3, FChain3 F L e c n g := by
  obtain ⟨hP, hL, h0, hn⟩ := hf
  refine ⟨fun i => if i = n then ((f n).1, c) else f i, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · by_cases h : i = n
    · subst h
      simp only [ite_true]
      obtain ⟨h1, _, h3⟩ := hP i le_rfl
      rw [hn] at h3
      exact ⟨h1, hc, h3.trans hbc⟩
    · simp only [if_neg h]
      exact hP i hi
  · have hin : i ≠ n := by omega
    simp only [if_neg hin]
    by_cases h : i + 1 = n
    · simp only [if_pos h]
      have := hL i hi
      rw [h] at this
      exact this
    · simp only [if_neg h]
      exact hL i hi
  · by_cases h : 0 = n
    · simp only [if_pos h]
      rw [← h]
      exact h0
    · simp only [if_neg h]
      exact h0
  · simp

/-- A level-1 link within `a1` extends a chain by the trivial pair of its target. -/
theorem fchain3_extend_link {F L : Finset V3} {e b c : V3} {n : ℕ} {f : ℕ → V3 × V3}
    (hf : FChain3 F L e b n f) (hb : b ∈ L) (hc : c ∈ L) (hd : dist3 b c ≤ Const.a1) (hcF : c ∈ F) :
    ∃ g : ℕ → V3 × V3, FChain3 F L e c (n + 1) g := by
  obtain ⟨hP, hL, h0, hn⟩ := hf
  refine ⟨fun i => if i = n + 1 then (c, c) else f i, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · by_cases h : i = n + 1
    · simp only [if_pos h]
      exact ⟨hcF, hcF, .refl⟩
    · simp only [if_neg h]
      exact hP i (by omega)
  · have hin : i ≠ n + 1 := by omega
    simp only [if_neg hin]
    by_cases h : i + 1 = n + 1
    · simp only [if_pos h]
      have hi' : i = n := by omega
      subst hi'
      rw [hn]
      exact ⟨hb, hc, hd⟩
    · simp only [if_neg h]
      exact hL i (by omega)
  · simp only [if_neg (show (0 : ℕ) ≠ n + 1 by omega)]
    exact h0
  · simp

/-- A path in a level-1 component extends a chain. -/
theorem fchain3_extend_comp {F L : Finset V3} (hLF : L ⊆ F) {e b c : V3} {n : ℕ} {f : ℕ → V3 × V3}
    (hf : FChain3 F L e b n f) (hbc : SameComp L Const.a1 b c) :
    ∃ (m : ℕ) (g : ℕ → V3 × V3), FChain3 F L e c m g := by
  induction hbc with
  | refl => exact ⟨n, f, hf⟩
  | @tail c' c'' _ hadj ih =>
    obtain ⟨m, g, hg⟩ := ih
    obtain ⟨h1, h2, h3⟩ := hadj
    obtain ⟨g', hg'⟩ := fchain3_extend_link hg h1 h2 h3 (hLF h2)
    exact ⟨m + 1, g', hg'⟩

/-- **Every block of the family of `e` is reached by a cluster chain from `e`.** -/
theorem exists_fchain3 (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} (he : e ∈ F) (hx : InFamily3 F L e x) :
    ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f := by
  induction hx with
  | refl =>
    exact ⟨0, fun _ => (e, e), ⟨fun _ _ => ⟨he, he, .refl⟩, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩⟩
  | @tail b c _ hlink ih =>
    obtain ⟨n, f, hf⟩ := ih
    obtain ⟨_, hcF, hcl | ⟨hbL, _, hbc⟩⟩ := hlink
    · obtain ⟨g, hg⟩ := fchain3_extend_pair hf hcl hcF
      exact ⟨n, g, hg⟩
    · exact fchain3_extend_comp hLF hf hbc

/-- **Every family has a good skeleton** (`gen_skel3`), for any exit `x ∈ L` of the family of its landing root
`e ∈ L`. -/
theorem gen_skel3_family (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} (he : e ∈ L) (hx : x ∈ L)
    (hfam : InFamily3 F L e x)
    (hW0 : ∀ r ∈ L, ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) (hW1 : W1Hyp F L e) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ F) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3 F L hLF he hx (exists_fchain3 F L hLF (hLF he) hfam) hW0 hW1

end QECD1
