import QECD1.A3Code3

/-!
# The definitional decoder facts, from the resolution rule

The 2D resolution rule (S3/Decoder `resolved`) resolves a component if its residual is even, or its region
touches the y-boundary rows, or its region covers the whole lattice. Here `reach K` stands for the last two
alternatives (`Resolved3`). The level-1 blocks are the flagged blocks in unresolved level-0 components (`level1Set3`,
2D `level1Set`).

From these definitions the four definitional facts of `gen_skel3_decoder3` are theorems:
* `level1Set3_odd` (`hP0`): the level-0 component of a level-1 block is odd;
* `level1Set3_comp` (`hLcomp`): level-1 membership is constant on level-0 components;
* `level1Set3_res` (`hres`): a resolved level-0 component that does not reach is even;
* `unresolved_odd` (`hodd1`): an unresolved level-1 component is odd.

`gen_skel3_decoder3_defs` is the deterministic lemma on the 3D code with `L = level1Set3 Fl (blockPar3 X) reach0`.
Its decoder facts are A2, A3, convention (i), the strips (no declared block, no reach), and the family being
unresolved.
-/

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The resolution rule (2D `resolved`): the residual is even, or the component reaches. -/
def Resolved3 (par : V3 → ZMod 2) (reach : Finset V3 → Prop) (K : Finset V3) : Prop :=
  ∑ b ∈ K, par b = 0 ∨ reach K

/-- The level-1 blocks (2D `level1Set`): the flagged blocks whose level-0 component is unresolved. -/
noncomputable def level1Set3 (Fl : Finset V3) (par : V3 → ZMod 2) (reach : Finset V3 → Prop) : Finset V3 :=
  Fl.filter (fun c => ¬ Resolved3 par reach (clusterOf Fl c))

theorem mem_level1Set3 {Fl : Finset V3} {par : V3 → ZMod 2} {reach : Finset V3 → Prop} {c : V3} :
    c ∈ level1Set3 Fl par reach ↔ c ∈ Fl ∧ ¬ Resolved3 par reach (clusterOf Fl c) := by
  unfold level1Set3
  rw [Finset.mem_filter]

theorem level1Set3_sub (Fl : Finset V3) (par : V3 → ZMod 2) (reach : Finset V3 → Prop) :
    level1Set3 Fl par reach ⊆ Fl :=
  fun _ hc => (mem_level1Set3.1 hc).1

/-- `hP0`: the level-0 component of a level-1 block is odd. -/
theorem level1Set3_odd {Fl : Finset V3} {par : V3 → ZMod 2} {reach : Finset V3 → Prop} {c : V3}
    (hc : c ∈ level1Set3 Fl par reach) : ∑ b ∈ clusterOf Fl c, par b ≠ 0 :=
  fun h => (mem_level1Set3.1 hc).2 (Or.inl h)

/-- `hLcomp`: level-1 membership is constant on level-0 components. -/
theorem level1Set3_comp {Fl : Finset V3} {par : V3 → ZMod 2} {reach : Finset V3 → Prop} {b : V3} (hb : b ∈ Fl)
    (hbL : b ∉ level1Set3 Fl par reach) : ∀ c ∈ clusterOf Fl b, c ∉ level1Set3 Fl par reach := by
  intro c hc hcL
  obtain ⟨_, hbc⟩ := mem_clusterOf.1 hc
  obtain ⟨_, hcres⟩ := mem_level1Set3.1 hcL
  rw [clusterOf_eq hbc] at hcres
  exact hbL (mem_level1Set3.2 ⟨hb, hcres⟩)

/-- `hres`: a resolved level-0 component that does not reach is even. -/
theorem level1Set3_res {Fl : Finset V3} {par : V3 → ZMod 2} {reach : Finset V3 → Prop} {b : V3} (hb : b ∈ Fl)
    (hbL : b ∉ level1Set3 Fl par reach) (hnr : ¬ reach (clusterOf Fl b)) : ∑ c ∈ clusterOf Fl b, par c = 0 := by
  have hres : Resolved3 par reach (clusterOf Fl b) := by
    by_contra h
    exact hbL (mem_level1Set3.2 ⟨hb, h⟩)
  rcases hres with h | h
  · exact h
  · exact absurd h hnr

/-- `hodd1`: an unresolved component is odd. -/
theorem unresolved_odd {par : V3 → ZMod 2} {reach : Finset V3 → Prop} {K : Finset V3}
    (h : ¬ Resolved3 par reach K) : ∑ b ∈ K, par b ≠ 0 :=
  fun hs => h (Or.inl hs)

/-- **The deterministic lemma on the 3D code with the decoder's definitions.** The level-1 blocks are
`L = level1Set3 Fl (blockPar3 X) reach0`. The decoder facts:
* A2 (`hA2`), A3 (`hA3`), convention (i) (`hdeclF`);
* the strips: the family's clusters contain no declared block (`hnodecl`), and the level-0 components in the clusters
  meeting the family's level-1 component do not reach (`hnoreach`);
* the family is unresolved at level 1 (`hunres1`). -/
theorem gen_skel3_decoder3_defs (X : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (hFl : Fl ⊆ F)
    (reach0 reach1 : Finset V3 → Prop) (hL : L = level1Set3 Fl (blockPar3 X) reach0) (ny : ℕ)
    (hh : h + 1 = ny * 35)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl)
    (hA3 : ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v))
    (hdeclF : ∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ F)
    {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hnodecl : ∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b)
    (hnoreach : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) →
      ¬ reach0 (clusterOf Fl b))
    (hunres1 : ¬ Resolved3 (blockPar3 X) reach1 (L.filter (fun b => SameComp L Const.a1 e b))) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length := by
  subst hL
  exact gen_skel3_decoder3 X F Fl _ (level1Set3_sub _ _ _) hFl ny hh hA2 hA3 hdeclF he hx hfam hnodecl
    (fun _ hr _ => level1Set3_odd hr) (unresolved_odd hunres1) (fun _ hb _ hbL => level1Set3_comp hb hbL)
    (fun b hb hk hbL => level1Set3_res hb hbL (hnoreach b hb hk))

end QECD1
