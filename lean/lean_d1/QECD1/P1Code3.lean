import QECD1.P2Parity3
import QECD1.Interior3

/-!
# P1 on the 3D code: the residual of an interior cluster is even

Let `X = E + C0` be the error plus the stage-1 correction, so that its syndrome `psyn3 X` is the residual (A2). The
residual parity of a block is the sum of `psyn3 X` over its checks (`blockPar3`).

`p1_code3`: let `C` be a set of blocks and `U` a set of checks with four properties:
* `U` is closed under `X`-adjacency;
* no half-edge of `X` touches `U` (the cluster is interior: `declared_of_rough`);
* `U` contains every check of `C`;
* the odd checks of `U` lie in `C`. This follows from A2 (an odd check's block is flagged, hence bad) and A3 (the bad
  blocks met by one `X`-component lie in one cluster).

Then the residual summed over the blocks of `C` is 0, by `local_handshake`. Take `U` to be the union of the
`X`-components meeting the cluster.

`gen_skel3_code3`: `gen_skel3_parity_family2` on the 3D code, with `par = blockPar3 X`. P1 is replaced by the
four conditions above, for the cluster of each level-1 block of the family.
-/

namespace QECD1

variable {T w h : ℕ}

/-- The residual parity of block `b`: the syndrome of `X` summed over the checks of `b`. -/
noncomputable def blockPar3 (X : PEdge3 T w h → ZMod 2) (b : V3) : ZMod 2 :=
  ∑ v ∈ Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v = b), psyn3 X v

/-- The residual parity summed over a set of blocks is the syndrome summed over their checks. -/
theorem sum_blockPar3 (X : PEdge3 T w h → ZMod 2) (C : Finset V3) :
    ∑ b ∈ C, blockPar3 X b = ∑ v ∈ Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v ∈ C), psyn3 X v := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v ∈ C))
    (t := C) (g := blockOf3) (fun v hv => (Finset.mem_filter.1 hv).2) (psyn3 X)]
  refine Finset.sum_congr rfl fun b hb => ?_
  unfold blockPar3
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    exact ⟨hv ▸ hb, hv⟩
  · exact fun hv => hv.2

/-- **P1 on the 3D code.** -/
theorem p1_code3 (X : PEdge3 T w h → ZMod 2) (C : Finset V3) (U : Finset (PVert3 T w h))
    (hU : ∀ u ∈ U, ∀ v, Fadj X u v → v ∈ U)
    (hrough : ∀ ed, ed.isHalf → X ed = 1 → ∀ v ∈ ed.ends, v ∉ U)
    (hCU : ∀ v : PVert3 T w h, blockOf3 v ∈ C → v ∈ U)
    (hUC : ∀ v ∈ U, psyn3 X v ≠ 0 → blockOf3 v ∈ C) :
    ∑ b ∈ C, blockPar3 X b = 0 := by
  rw [sum_blockPar3]
  have hloc := local_handshake X U hU hrough
  rw [← Finset.sum_filter_add_sum_filter_not U (fun v => blockOf3 v ∈ C)] at hloc
  have h2 : ∑ v ∈ U.filter (fun v => ¬ blockOf3 v ∈ C), psyn3 X v = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    obtain ⟨hvU, hvC⟩ := Finset.mem_filter.1 hv
    by_contra hne
    exact hvC (hUC v hvU hne)
  have h1 : U.filter (fun v => blockOf3 v ∈ C) =
      Finset.univ.filter (fun v : PVert3 T w h => blockOf3 v ∈ C) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hv => hv.2, fun hv => ⟨hCU v hv, hv⟩⟩
  rw [h2, add_zero, h1] at hloc
  exact hloc

open Classical in
/-- **Every family has a good skeleton, on the 3D code.** This is `gen_skel3_parity_family2` with `par = blockPar3 X`.
P1 comes from `p1_code3`, given for the cluster of each level-1 block `r` of the family a set `U` of checks with the
four properties above (closed, interior, containing the cluster's checks, odd checks inside). -/
theorem gen_skel3_code3 (X : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F)
    (hpar : ∀ b, blockPar3 X b ≠ 0 → b ∈ Fl) {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hP0 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, blockPar3 X b ≠ 0)
    (hint : ∀ r ∈ L, InFamily3 F L e r → ∃ U : Finset (PVert3 T w h), (∀ u ∈ U, ∀ v, Fadj X u v → v ∈ U) ∧
      (∀ ed, ed.isHalf → X ed = 1 → ∀ v ∈ ed.ends, v ∉ U) ∧
      (∀ v : PVert3 T w h, blockOf3 v ∈ clusterOf F r → v ∈ U) ∧
      (∀ v ∈ U, psyn3 X v ≠ 0 → blockOf3 v ∈ clusterOf F r))
    (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), blockPar3 X b ≠ 0)
    (hLcomp : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∀ c ∈ clusterOf Fl b, c ∉ L)
    (hres : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∑ c ∈ clusterOf Fl b, blockPar3 X c = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_parity_family2 F Fl L hLFl hFl (blockPar3 X) hpar he hx hfam hP0
    (fun r hr hf => by
      obtain ⟨U, h1, h2, h3, h4⟩ := hint r hr hf
      exact p1_code3 X _ U h1 h2 h3 h4)
    hodd1 hLcomp hres

end QECD1
