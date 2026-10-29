import QECD1.DecoderParity3

/-!
# Restricting to one family

The decoder's parity facts hold only for families between the strips: there the clusters are interior (2D:
`fam_skeleton`, hypothesis `hint`). The skeleton of a family uses only the family's blocks, so it suffices to assume
the facts for them.

A family is closed under cluster paths and level-1 paths (`sameComp_famF`, `sameComp_famL`). So the family's bad
blocks `famF` and level-1 blocks `famL` have the same clusters and level-1 components around the family as `F` and
`L`. Hence:
* family membership (`infamily_restrict`), W1 (`w1hyp_restrict`) and W0 (`w0_restrict`) carry over to the
  restricted sets;
* `gen_skel3_parity_family` gives the good skeleton from the parity facts of the family's own level-1 blocks. Its
  counted blocks lie in the family (`famF`), hence between the strips. Its route ends within `D - 1` of the exit `x`,
  so the next family's landing root is at least `J = 17` away (`skel_landing`).
-/

namespace QECD1

open Classical

/-- The bad blocks of the family of `e`. -/
noncomputable def famF (F L : Finset V3) (e : V3) : Finset V3 := F.filter (fun b => InFamily3 F L e b)

/-- The level-1 blocks of the family of `e`. -/
noncomputable def famL (F L : Finset V3) (e : V3) : Finset V3 := L.filter (fun b => InFamily3 F L e b)

theorem mem_famF {F L : Finset V3} {e b : V3} : b ∈ famF F L e ↔ b ∈ F ∧ InFamily3 F L e b := by
  unfold famF
  rw [Finset.mem_filter]

theorem mem_famL {F L : Finset V3} {e b : V3} : b ∈ famL F L e ↔ b ∈ L ∧ InFamily3 F L e b := by
  unfold famL
  rw [Finset.mem_filter]

theorem famF_sub (F L : Finset V3) (e : V3) : famF F L e ⊆ F := fun _ hb => (mem_famF.1 hb).1

theorem famL_sub_famF {F L : Finset V3} (hLF : L ⊆ F) (e : V3) : famL F L e ⊆ famF F L e := fun _ hb =>
  mem_famF.2 ⟨hLF (mem_famL.1 hb).1, (mem_famL.1 hb).2⟩

/-- **A cluster path from a family block stays in the family.** -/
theorem sameComp_famF {F L : Finset V3} {e c c' : V3} (hc : InFamily3 F L e c)
    (hcc' : SameComp F Const.a0 c c') : SameComp (famF F L e) Const.a0 c c' ∧ InFamily3 F L e c' := by
  induction hcc' with
  | refl => exact ⟨.refl, hc⟩
  | @tail b b' _ hadj ih =>
    obtain ⟨ih1, hb⟩ := ih
    have hb' : InFamily3 F L e b' := hb.tail ⟨hadj.1, hadj.2.1, Or.inl (.single hadj)⟩
    exact ⟨ih1.tail ⟨mem_famF.2 ⟨hadj.1, hb⟩, mem_famF.2 ⟨hadj.2.1, hb'⟩, hadj.2.2⟩, hb'⟩

/-- **A level-1 path from a family block stays in the family.** -/
theorem sameComp_famL {F L : Finset V3} (hLF : L ⊆ F) {e c c' : V3} (hc : InFamily3 F L e c)
    (hcc' : SameComp L Const.a1 c c') : SameComp (famL F L e) Const.a1 c c' ∧ InFamily3 F L e c' := by
  induction hcc' with
  | refl => exact ⟨.refl, hc⟩
  | @tail b b' _ hadj ih =>
    obtain ⟨ih1, hb⟩ := ih
    have hb' : InFamily3 F L e b' :=
      hb.tail ⟨hLF hadj.1, hLF hadj.2.1, Or.inr ⟨hadj.1, hadj.2.1, .single hadj⟩⟩
    exact ⟨ih1.tail ⟨mem_famL.2 ⟨hadj.1, hb⟩, mem_famL.2 ⟨hadj.2.1, hb'⟩, hadj.2.2⟩, hb'⟩

/-- Family membership carries over to the restricted sets. -/
theorem infamily_restrict {F L : Finset V3} (hLF : L ⊆ F) {e x : V3} (hx : InFamily3 F L e x) :
    InFamily3 (famF F L e) (famL F L e) e x := by
  have key : ∀ y, InFamily3 F L e y → InFamily3 (famF F L e) (famL F L e) e y := by
    intro y hy
    induction hy with
    | refl => exact .refl
    | @tail b c heb hl ih =>
      have hc : InFamily3 F L e c := heb.tail hl
      obtain ⟨hbF, hcF, hcl | ⟨hbL, hcL, hbc⟩⟩ := hl
      · exact ih.tail ⟨mem_famF.2 ⟨hbF, heb⟩, mem_famF.2 ⟨hcF, hc⟩, Or.inl (sameComp_famF heb hcl).1⟩
      · exact ih.tail ⟨mem_famF.2 ⟨hbF, heb⟩, mem_famF.2 ⟨hcF, hc⟩,
          Or.inr ⟨mem_famL.2 ⟨hbL, heb⟩, mem_famL.2 ⟨hcL, hc⟩, (sameComp_famL hLF heb hbc).1⟩⟩
  exact key x hx

/-- W1 carries over to the restricted sets. -/
theorem w1hyp_restrict {F L : Finset V3} (hLF : L ⊆ F) {e : V3} (hW1 : W1Hyp F L e) :
    W1Hyp (famF F L e) (famL F L e) e := by
  obtain ⟨c, hcL, ⟨k, hek, hkc⟩, hfar⟩ := hW1
  obtain ⟨hek', hk⟩ := sameComp_famL hLF (e := e) .refl hek
  obtain ⟨hkc', hc⟩ := sameComp_famF hk hkc
  exact ⟨c, mem_famL.2 ⟨hcL, hc⟩, ⟨k, hek', hkc'⟩,
    fun h => hfar (sameComp_mono_set (fun _ hb => (mem_famL.1 hb).1) h)⟩

/-- W0 carries over to the restricted sets. -/
theorem w0_restrict {F L : Finset V3} {e r : V3} (hr : InFamily3 F L e r)
    (h : ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) :
    ∃ b, SameComp (famF F L e) Const.a0 r b ∧ Const.D ≤ dist3 r b := by
  obtain ⟨b, hrb, hd⟩ := h
  exact ⟨b, (sameComp_famF hr hrb).1, hd⟩

/-- **Every family has a good skeleton, from the parity facts of its own blocks.** The hypotheses are the decoder
facts for the family of `e` only:
* `hpar`: blocks of nonzero residual parity are flagged;
* `hP0`: the level-0 component of each level-1 block of the family has odd parity;
* `hP1`: the cluster of each level-1 block of the family has even parity (P1: it is interior);
* `hodd1`: the level-1 component of `e` has odd parity;
* `hP2`: the level-1 blocks of the clusters meeting it have even total parity (P2);
* `hfam`: the exit `x ∈ L` is in the family of `e`. -/
theorem gen_skel3_parity_family (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F) (par : V3 → ZMod 2)
    (hpar : ∀ b, par b ≠ 0 → b ∈ Fl) {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hP0 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, par b ≠ 0)
    (hP1 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf F r, par b = 0)
    (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), par b ≠ 0)
    (hP2 : ∑ b ∈ L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b), par b = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length := by
  have hLF : L ⊆ F := hLFl.trans hFl
  have hW0 : ∀ r ∈ famL F L e, ∃ b, SameComp (famF F L e) Const.a0 r b ∧ Const.D ≤ dist3 r b := by
    intro r hr
    obtain ⟨hrL, hrf⟩ := mem_famL.1 hr
    exact w0_restrict hrf (w0_of_parity F Fl hFl par hpar (hLFl hrL) (hP0 r hrL hrf) (hP1 r hrL hrf))
  obtain ⟨k, hk1, hk2, hkc, hk3, hk4, hk5⟩ := gen_skel3_family (famF F L e) (famL F L e) (famL_sub_famF hLF e)
    (mem_famL.2 ⟨he, .refl⟩) (mem_famL.2 ⟨hx, hfam⟩) (infamily_restrict hLF hfam) hW0
    (w1hyp_restrict hLF (w1hyp_of_parity F L par hodd1 hP2))
  exact ⟨k, hk1, hk2, hkc, hk3, hk4, hk5⟩

/-- **The next family lands at least `J` away from this family's route end**: the route of `gen_skel3_parity_family`
ends within `D - 1` of the exit `x`, and the next family's landing root is a level-1 block of another level-1 component
(R0, `landing_dist`). These are the jumps of the transfer (`TData.transfer`, offsets with `|v|∞ ≥ J`). -/
theorem skel_landing {L : Finset V3} {x r' p : V3} (hx : x ∈ L) (hr' : r' ∈ L)
    (hdiff : ¬ SameComp L Const.a1 x r') (hcov : dist3 x p ≤ Const.D - 1) : Const.J ≤ linf (r' - p) :=
  landing_dist L hx hr' hdiff hcov

end QECD1
