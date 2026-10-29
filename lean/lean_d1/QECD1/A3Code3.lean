import QECD1.P1Code3

/-!
# The data of P1 from A2 and A3, on the 3D code

`gen_skel3_code3` asks, for the cluster of each level-1 block of the family, for a set `U` of checks with four
properties. The natural choice is the union of the `X`-components meeting the cluster (`compUnion3`):
* it is closed under `X`-adjacency (`compUnion3_closed`);
* it contains the cluster's checks (`compUnion3_contains`);
* its odd checks lie in the cluster (`compUnion3_odd`), by A2 (an odd check's block is flagged, hence bad) and A3 (the
  bad blocks met by one `X`-component lie in one cluster).

What is left is the interior condition: no half-edge of `X` touches it (`declared_of_rough` and Lemma A for clusters
away from the rough sides). A2 also gives the block-level `hpar` (`hpar_of_A2`).

`gen_skel3_A2A3` is the deterministic lemma on the 3D code with these decoder facts:
* A2: an odd check lies in a flagged block;
* A3: `X`-connected bad blocks lie in one cluster;
* the interior condition, for the family's clusters;
* the definitional facts `hP0`, `hodd1`, `hLcomp`, `hres`.

The interior condition itself follows from the declared rows (`interior_of_declared`), in four steps:
* a half-edge ends on a rough side (`half_end_rough`);
* rough-side checks lie in declared blocks (`declared_of_rough`);
* declared blocks are bad (convention (i));
* by A3, a component reaching a half-edge would put a declared block into the cluster.

So `gen_skel3_decoder3` needs only A2, A3, convention (i), "the family's clusters contain no declared block", and the
definitional facts.
-/

namespace QECD1

variable {T w h : ℕ}

open Classical

/-- The checks `X`-connected to a check of the block set `C`: the union of the `X`-components meeting `C`. -/
noncomputable def compUnion3 (X : PEdge3 T w h → ZMod 2) (C : Finset V3) : Finset (PVert3 T w h) :=
  Finset.univ.filter (fun v => ∃ u, blockOf3 u ∈ C ∧ Relation.ReflTransGen (Fadj X) u v)

theorem mem_compUnion3 {X : PEdge3 T w h → ZMod 2} {C : Finset V3} {v : PVert3 T w h} :
    v ∈ compUnion3 X C ↔ ∃ u, blockOf3 u ∈ C ∧ Relation.ReflTransGen (Fadj X) u v := by
  unfold compUnion3
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem compUnion3_closed (X : PEdge3 T w h → ZMod 2) (C : Finset V3) :
    ∀ u ∈ compUnion3 X C, ∀ v, Fadj X u v → v ∈ compUnion3 X C := by
  intro u hu v huv
  obtain ⟨u0, hu0, hpath⟩ := mem_compUnion3.1 hu
  exact mem_compUnion3.2 ⟨u0, hu0, hpath.tail huv⟩

theorem compUnion3_contains (X : PEdge3 T w h → ZMod 2) (C : Finset V3) :
    ∀ v : PVert3 T w h, blockOf3 v ∈ C → v ∈ compUnion3 X C :=
  fun v hv => mem_compUnion3.2 ⟨v, hv, .refl⟩

/-- **The odd checks of the component union lie in the cluster** (A2 and A3). -/
theorem compUnion3_odd (X : PEdge3 T w h → ZMod 2) (F Fl : Finset V3) (hFl : Fl ⊆ F) (r : V3)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl)
    (hA3 : ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v)) :
    ∀ v ∈ compUnion3 X (clusterOf F r), psyn3 X v ≠ 0 → blockOf3 v ∈ clusterOf F r := by
  intro v hv hodd
  obtain ⟨u, hu, hpath⟩ := mem_compUnion3.1 hv
  obtain ⟨huF, hru⟩ := mem_clusterOf.1 hu
  have hvF : blockOf3 v ∈ F := hFl (hA2 v hodd)
  exact mem_clusterOf.2 ⟨hvF, hru.trans (hA3 u v hpath huF hvF)⟩

/-- A2 at block level: a block of nonzero residual parity has an odd check, hence is flagged. -/
theorem hpar_of_A2 (X : PEdge3 T w h → ZMod 2) (Fl : Finset V3)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl) : ∀ b, blockPar3 X b ≠ 0 → b ∈ Fl := by
  intro b hb
  obtain ⟨v, hv, hpv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hvb : blockOf3 v = b := (Finset.mem_filter.1 hv).2
  rw [← hvb]
  exact hA2 v hpv

/-- **Every family has a good skeleton, on the 3D code, from A2, A3 and the interior condition.** -/
theorem gen_skel3_A2A3 (X : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl)
    (hA3 : ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v))
    {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hinterior : ∀ r ∈ L, InFamily3 F L e r → ∀ ed, ed.isHalf → X ed = 1 → ∀ v ∈ ed.ends,
      v ∉ compUnion3 X (clusterOf F r))
    (hP0 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, blockPar3 X b ≠ 0)
    (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), blockPar3 X b ≠ 0)
    (hLcomp : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∀ c ∈ clusterOf Fl b, c ∉ L)
    (hres : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∑ c ∈ clusterOf Fl b, blockPar3 X c = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_code3 X F Fl L hLFl hFl (hpar_of_A2 X Fl hA2) he hx hfam hP0
    (fun r hr hf => ⟨compUnion3 X (clusterOf F r), compUnion3_closed X _, hinterior r hr hf,
      compUnion3_contains X _, compUnion3_odd X F Fl hFl r hA2 hA3⟩)
    hodd1 hLcomp hres

/-- The end of a half-edge is on a rough side (`y = 0` or `y = h`). -/
theorem half_end_rough {ed : PEdge3 T w h} (hed : ed.isHalf) {v : PVert3 T w h} (hv : v ∈ ed.ends) :
    (v.2.2 : ℕ) = 0 ∨ (v.2.2 : ℕ) = h := by
  cases ed with
  | hor t x y => exact absurd hed id
  | ver t x y => exact absurd hed id
  | time t x y => exact absurd hed id
  | bot t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hv
    subst hv
    left
    rfl
  | top t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hv
    subst hv
    right
    simp

/-- **The interior condition from the declared rows** (`declared_of_rough` and A3). Suppose the cluster has no declared
block, declared blocks are bad (convention (i)), and `X`-connected bad blocks share a cluster. Then no half-edge of `X`
touches the component union of the cluster. -/
theorem interior_of_declared (X : PEdge3 T w h → ZMod 2) (F : Finset V3) (ny : ℕ) (hh : h + 1 = ny * 35) (r : V3)
    (hdeclF : ∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ F)
    (hA3 : ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v))
    (hnodecl : ∀ b ∈ clusterOf F r, ¬ declared3 ny b) :
    ∀ ed, ed.isHalf → X ed = 1 → ∀ v ∈ ed.ends, v ∉ compUnion3 X (clusterOf F r) := by
  intro ed hed _ v hv hvU
  obtain ⟨u, hu, hpath⟩ := mem_compUnion3.1 hvU
  have hdecl := declared_of_rough ny hh v (half_end_rough hed hv)
  have hvF := hdeclF v hdecl
  obtain ⟨huF, hru⟩ := mem_clusterOf.1 hu
  exact hnodecl (blockOf3 v) (mem_clusterOf.2 ⟨hvF, hru.trans (hA3 u v hpath huF hvF)⟩) hdecl

/-- **The deterministic lemma on the 3D code, from the decoder's facts.** For a family whose clusters contain no
declared block (the families between the strips), the decoder facts are:
* A2 (`hA2`): an odd check lies in a flagged block;
* A3 (`hA3`): `X`-connected bad blocks lie in one cluster;
* convention (i) (`hdeclF`): declared blocks are bad;
* `hnodecl`: the family's clusters contain no declared block;
* the definitional facts `hP0`, `hodd1`, `hLcomp`, `hres` (2D `level1Set`, `resolved`). -/
theorem gen_skel3_decoder3 (X : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F)
    (ny : ℕ) (hh : h + 1 = ny * 35)
    (hA2 : ∀ v : PVert3 T w h, psyn3 X v ≠ 0 → blockOf3 v ∈ Fl)
    (hA3 : ∀ u v : PVert3 T w h, Relation.ReflTransGen (Fadj X) u v → blockOf3 u ∈ F → blockOf3 v ∈ F →
      SameComp F Const.a0 (blockOf3 u) (blockOf3 v))
    (hdeclF : ∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ F)
    {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hnodecl : ∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b)
    (hP0 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, blockPar3 X b ≠ 0)
    (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), blockPar3 X b ≠ 0)
    (hLcomp : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∀ c ∈ clusterOf Fl b, c ∉ L)
    (hres : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∑ c ∈ clusterOf Fl b, blockPar3 X c = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_A2A3 X F Fl L hLFl hFl hA2 hA3 he hx hfam
    (fun r hr hf => interior_of_declared X F ny hh r hdeclF hA3 (hnodecl r hr hf)) hP0 hodd1 hLcomp hres

end QECD1
