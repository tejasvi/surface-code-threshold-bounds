import QECD1.T2Stations3

/-!
# The strips give the family hypotheses (3D)

For an intermediate family of a T2 path (a family with no block in either strip) entered and left at odd checks of
`Ω`, the hypotheses of `FamEvent` hold (`famEvent_of_inter3`):
* its entry and exit blocks are level-1 blocks (`lev_of_om3`) of the family;
* its clusters contain no declared block (`hnodecl`): the declared rows lie in the strips (`not_declared_of_inter`);
* its level-0 components do not reach (`hnoreach`): their regions, of radius `r0 ≤ hs3`, stay strictly between the
  rough sides and do not cover the code (`not_reach_of_inter`);
* its level-1 component is unresolved (`hunres1`): `Ω` is nonzero at its entry check (`unres_of_om3`).

`inter_skel3`: such a family has a good skeleton rooted at its entry block, whose route ends within `D - 1` of its exit
block, and whose counted blocks are pairwise `D`-separated, lie in the family, and are bad and undeclared.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

theorem hs3_val : hs3 = 11 := by decide

/-- A block strictly between the strips is not declared. -/
theorem not_declared_of_inter {ny : ℕ} {c : V3} (hc : (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny) :
    ¬ declared3 ny c := by
  rw [hs3_val] at hc
  unfold declared3
  omega

/-- **The regions of a block set strictly between the strips do not reach** (radius `r ≤ hs3`). -/
theorem not_reach_of_inter {ny : ℕ} (hh : h + 1 = ny * 35) {r : ℕ} (hr : r ≤ hs3) {K : Finset V3}
    (hK : ∀ c ∈ K, (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny) : ¬ reach3 T w h r K := by
  have hbot : ∀ v : PVert3 T w h, v ∈ (region3 K r : Set (PVert3 T w h)) → v.2.2 ≠ 0 := by
    rintro ⟨t, x, y⟩ ⟨c, hc, hd⟩ hy
    simp only at hy
    subst hy
    have h1 := row_bot (T := T) (w := w) (h := h) t x hd
    have h2 := (hK c hc).1
    omega
  have htop : ∀ v : PVert3 T w h, v ∈ (region3 K r : Set (PVert3 T w h)) → v.2.2 ≠ Fin.last h := by
    rintro ⟨t, x, y⟩ ⟨c, hc, hd⟩ hy
    simp only at hy
    subst hy
    have h1 := row_top hh t x hd
    have h2 := (hK c hc).2
    omega
  rintro (⟨v, hv, hy | hy⟩ | hall)
  · exact hbot v hv hy
  · exact htop v hv hy
  · exact hbot (0, 0, 0) (hall _) rfl

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- An odd check of `Ω` lies in a level-1 block. -/
theorem lev_of_om3 {E : PEdge3 T w h → ZMod 2} {v : PVert3 T w h} (hv : S.om3 E v ≠ 0) :
    blockOf3 v ∈ S.levSet (reach3 T w h r0) E := by
  simp only [om3, omega3] at hv
  split_ifs at hv with hc
  · have h1 := hc.1
    rw [lev1Set3_eq] at h1
    exact h1
  · exact absurd rfl hv

/-- An odd check of `Ω` lies in an unresolved level-1 component. -/
theorem unres_of_om3 {E : PEdge3 T w h → ZMod 2} {v : PVert3 T w h} (hv : S.om3 E v ≠ 0) :
    ¬ Resolved3 (blockPar3 (S.Fcfg E)) (reach3 T w h r1)
      ((S.levSet (reach3 T w h r0) E).filter
        (fun b => SameComp (S.levSet (reach3 T w h r0) E) Const.a1 (blockOf3 v) b)) := by
  simp only [om3, omega3] at hv
  split_ifs at hv with hc
  · have h2 := hc.2
    rw [lev1Set3_eq, residD3_eq, parOf_psyn3] at h2
    exact h2
  · exact absurd rfl hv

/-- **The strips give the family event**: an intermediate family entered at the odd check `u` and left at the odd
check `v` of `Ω` satisfies `FamEvent` for its entry and exit blocks. -/
theorem famEvent_of_inter3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E))
    (hint : ∀ c ∈ Fm, (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny)
    {u v : PVert3 T w h} (hu : blockOf3 u ∈ Fm) (hv : blockOf3 v ∈ Fm) (hou : S.om3 E u ≠ 0)
    (hov : S.om3 E v ≠ 0) :
    S.FamEvent (reach3 T w h r0) (reach3 T w h r1) ny (blockOf3 u) (blockOf3 v) E := by
  have heL := S.lev_of_om3 hou
  have hxL := S.lev_of_om3 hov
  have heF : blockOf3 u ∈ S.badSet ny E := S.levSet_sub _ ny E heL
  have hFe : famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) = Fm :=
    famF_eq_of_mem_families3 hFm hu
  have hfam_mem : ∀ b, InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) b →
      b ∈ S.badSet ny E → b ∈ Fm := by
    intro b hb hbF
    rw [← hFe]
    exact mem_famF.2 ⟨hbF, hb⟩
  refine ⟨heL, hxL, ?_, ?_, ?_, S.unres_of_om3 hou⟩
  · have hv' := hv
    rw [← hFe] at hv'
    exact (mem_famF.1 hv').2
  · intro r hr hre b hb
    have hbF := (mem_clusterOf.1 hb).1
    have hrb : InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) b :=
      hre.tail ⟨S.levSet_sub _ ny E hr, hbF, Or.inl (mem_clusterOf.1 hb).2⟩
    exact not_declared_of_inter (hint b (hfam_mem b hrb hbF))
  · intro b hb hex
    obtain ⟨k, hkL, hek, hkb⟩ := hex
    have hbF : b ∈ S.badSet ny E := S.flSet_sub ny E hb
    have hkF : k ∈ S.badSet ny E := S.levSet_sub _ ny E hkL
    have h1 : InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) b :=
      (Relation.ReflTransGen.single ⟨heF, hkF, Or.inr ⟨heL, hkL, hek⟩⟩).tail ⟨hkF, hbF, Or.inl hkb⟩
    refine not_reach_of_inter hh r0_le_hs3 fun c hc => hint c ?_
    have hcF : c ∈ S.badSet ny E := S.flSet_sub ny E (mem_clusterOf.1 hc).1
    have hbc : SameComp (S.badSet ny E) Const.a0 b c :=
      sameComp_mono_set (S.flSet_sub ny E) (mem_clusterOf.1 hc).2
    exact hfam_mem c (h1.tail ⟨hbF, hcF, Or.inl hbc⟩) hcF

/-- **The skeleton of an intermediate family**: rooted at its entry block, with route end within `D - 1` of its exit
block, and counted blocks that are pairwise `D`-separated, lie in the family, and are bad and undeclared. -/
theorem inter_skel3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E))
    (hint : ∀ c ∈ Fm, (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny)
    {u v : PVert3 T w h} (hu : blockOf3 u ∈ Fm) (hv : blockOf3 v ∈ Fm) (hou : S.om3 E u ≠ 0)
    (hov : S.om3 E v ≠ 0) :
    ∃ k : Skel3, k.1 = blockOf3 u ∧ SkelOK k ∧
      dist3 (blockOf3 v) (endOf (blockOf3 u) (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks (blockOf3 u) k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (keyBlocks (blockOf3 u) k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length ∧
      ∀ b ∈ keyBlocks (blockOf3 u) k.2.2, b ∈ Fm ∧ S.bad E b ∧ ¬ declared3 ny b := by
  have hev := S.famEvent_of_inter3 hh hFm hint hu hv hou hov
  obtain ⟨hFl, hL, hA2, hlong, hdeclF, he, hx, hfam, hnodecl, hnoreach, hunres1⟩ := S.finalHyps_of_famEvent hev
  obtain ⟨k, hk1, hok, hdist, hsep, hfamF, hlen⟩ :=
    gen_skel3_final (S.Fcfg E) _ _ _ hFl _ _ hL ny hh hA2 hlong hdeclF he hx hfam hnodecl hnoreach hunres1
  have hLF : S.levSet (reach3 T w h r0) E ⊆ S.badSet ny E := S.levSet_sub _ ny E
  refine ⟨k, hk1, hok, hdist, hsep, hlen, fun b hb => ⟨?_, ?_⟩⟩
  · rw [← famF_eq_of_mem_families3 hFm hu]
    exact hfamF b hb
  · have hrb := famF_rows_bad (Bad := fun b E' => S.bad E' b) (X := E) (R := {b | ¬ declared3 ny b}) hLF he
      hnodecl (S.badSet_bad ny E) (fun _ hb => hb) (hfamF b hb)
    exact ⟨hrb.2, hrb.1⟩

end Stage13

end QECD1
