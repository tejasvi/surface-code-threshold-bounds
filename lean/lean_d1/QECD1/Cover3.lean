import QECD1.Events3

/-!
# From the deterministic lemma to the union bound, and the decoder's sets

The generic part holds for any sets `F ⊇ Fl ⊇ L` that satisfy the hypotheses of `gen_skel3_final`:
* `infamily_cluster`, `famF_nodecl`: a block of the family `famF F L e` lies in the cluster of a level-1 block of the
  family, so under the strip hypothesis `hnodecl` it is undeclared.
* `famF_rows_bad`: if every undeclared block of `F` is bad at `X` and `R` contains the undeclared blocks, then every
  block of `famF F L e` lies in `R` and is bad at `X`. This connects `gen_skel3_final`'s `b ∈ famF F L e` to the
  `b ∈ R` and `Bad b X` that `skel_prob_le_rows` and `skel_union_le_rows` need.
* `FinalHyps` bundles the hypotheses of `gen_skel3_final`. `final_skeleton`: under them there is a good skeleton rooted
  at `e` whose counted blocks are pairwise `D`-separated, lie in `R` and are bad.
* `union_from_final`: if every configuration of an event `A` satisfies `FinalHyps` for some sets whose undeclared
  blocks are bad, then `P(A) ≤ ∑_{k ∈ K} ε^{|keyBlocks e k.2.2|}` for a finite set `K` of good skeletons rooted at
  `e`. `K` is the image of the event's configurations under a choice of skeleton, finite because the configuration
  space is.

The decoder, for a stage-1 rule `S` and noise `E` (`X = E + C_0`):
* `flSet S E` (`Fl`, the flagged blocks), `badSet S ny E` (`F`, the bad blocks and the declared ones, convention (i)),
  `levSet S reach0 E` (`L = level1Set3 Fl (blockPar3 X) reach0`);
* A2, `hlong` and `hdeclF` hold by these definitions (`flSet_hA2`, `badSet_hlong`, `badSet_hdeclF`), and an undeclared
  block of `F` is bad (`badSet_bad`);
* `FamEvent` collects the remaining hypotheses: `e` and `x` are level-1 blocks with `x` in the family of `e`, the
  strips (`hnodecl`, `hnoreach`), and the family is unresolved. `finalHyps_of_famEvent` gives `FinalHyps`;
* `gen_skel3_dec` and `famEvent_prob_le` are `final_skeleton` and `union_from_final` for the decoder. With the
  encoding (`famB3_skel`) this is the family bound of the count up to the tilt, which is the transfer's.
-/

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The blocks that contain a check. -/
noncomputable def latBlocks (T w h : ℕ) : Finset V3 := Finset.univ.image (blockOf3 (T := T) (w := w) (h := h))

theorem blockOf3_mem_latBlocks (v : PVert3 T w h) : blockOf3 v ∈ latBlocks T w h :=
  Finset.mem_image_of_mem _ (Finset.mem_univ v)

/-- A block in the family of `e` lies in the cluster of a level-1 block of the family. -/
theorem infamily_cluster {F L : Finset V3} (hLF : L ⊆ F) {e b : V3} (he : e ∈ L) (hb : InFamily3 F L e b) :
    ∃ r ∈ L, InFamily3 F L e r ∧ b ∈ clusterOf F r := by
  induction hb with
  | refl => exact ⟨e, he, .refl, self_mem_clusterOf (hLF he)⟩
  | tail hab hbc ih =>
    obtain ⟨r, hr, her, hbr⟩ := ih
    obtain ⟨_, hc1, hlink⟩ := id hbc
    rcases hlink with hcl | ⟨_, hcL, _⟩
    · exact ⟨r, hr, her, mem_clusterOf.2 ⟨hc1, (mem_clusterOf.1 hbr).2.trans hcl⟩⟩
    · exact ⟨_, hcL, hab.tail hbc, self_mem_clusterOf hc1⟩

/-- **The blocks of the family are undeclared**, under the strip hypothesis `hnodecl`. -/
theorem famF_nodecl {F L : Finset V3} (hLF : L ⊆ F) {e : V3} (he : e ∈ L) {ny : ℕ}
    (hnodecl : ∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b) {b : V3}
    (hb : b ∈ famF F L e) : ¬ declared3 ny b := by
  obtain ⟨r, hr, her, hbr⟩ := infamily_cluster hLF he (mem_famF.1 hb).2
  exact hnodecl r hr her b hbr

/-- **The blocks of the family lie in `R` and are bad**, if every undeclared block of `F` is bad and `R` contains the
undeclared blocks. -/
theorem famF_rows_bad {κ : Type} {F L : Finset V3} (hLF : L ⊆ F) {e : V3} (he : e ∈ L) {ny : ℕ}
    (hnodecl : ∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b)
    {Bad : V3 → κ → Prop} {X : κ} (hFbad : ∀ b ∈ F, ¬ declared3 ny b → Bad b X)
    {R : Set V3} (hR : ∀ b, ¬ declared3 ny b → b ∈ R) {b : V3} (hb : b ∈ famF F L e) : b ∈ R ∧ Bad b X :=
  ⟨hR b (famF_nodecl hLF he hnodecl hb), hFbad b (famF_sub F L e hb) (famF_nodecl hLF he hnodecl hb)⟩

/-- The hypotheses of `gen_skel3_final` for the configuration `cfg`, the sets `F`, `Fl`, `L`, the reach predicates,
the number `ny` of block rows, and the level-1 blocks `e`, `x`. -/
def FinalHyps (cfg : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (reach0 reach1 : Finset V3 → Prop) (ny : ℕ)
    (e x : V3) : Prop :=
  Fl ⊆ F ∧ L = level1Set3 Fl (blockPar3 cfg) reach0 ∧
    (∀ v : PVert3 T w h, psyn3 cfg v ≠ 0 → blockOf3 v ∈ Fl) ∧ (∀ c, c ∉ F → NotLong3 cfg c) ∧
    (∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ F) ∧
    e ∈ L ∧ x ∈ L ∧ InFamily3 F L e x ∧
    (∀ r ∈ L, InFamily3 F L e r → ∀ b ∈ clusterOf F r, ¬ declared3 ny b) ∧
    (∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → ¬ reach0 (clusterOf Fl b)) ∧
    ¬ Resolved3 (blockPar3 cfg) reach1 (L.filter (fun b => SameComp L Const.a1 e b))

/-- **The deterministic lemma, connected to the probability side.** Under `FinalHyps`, if every undeclared block of
`F` is bad and `R` contains the undeclared blocks, there is a good skeleton rooted at `e` whose counted blocks are
pairwise `D`-separated, lie in `R`, and are bad. -/
theorem final_skeleton {κ : Type} {cfg : PEdge3 T w h → ZMod 2} {F Fl L : Finset V3}
    {reach0 reach1 : Finset V3 → Prop} {ny : ℕ} (hh : h + 1 = ny * 35) {e x : V3}
    (hfin : FinalHyps cfg F Fl L reach0 reach1 ny e x) {Bad : V3 → κ → Prop} {X : κ}
    (hFbad : ∀ b ∈ F, ¬ declared3 ny b → Bad b X) {R : Set V3} (hR : ∀ b, ¬ declared3 ny b → b ∈ R) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ R) ∧ (∀ b ∈ keyBlocks e k.2.2, Bad b X) := by
  obtain ⟨hFl, hL, hA2, hlong, hdeclF, he, hx, hfam, hnodecl, hnoreach, hunres1⟩ := hfin
  obtain ⟨k, hk1, hok, hdist, hsep, hfamF, _⟩ :=
    gen_skel3_final cfg F Fl L hFl reach0 reach1 hL ny hh hA2 hlong hdeclF he hx hfam hnodecl hnoreach hunres1
  have hLF : L ⊆ F := by
    rw [hL]
    exact (level1Set3_sub _ _ _).trans hFl
  exact ⟨k, hk1, hok, hdist, hsep, fun b hb => (famF_rows_bad hLF he hnodecl hFbad hR (hfamF b hb)).1,
    fun b hb => (famF_rows_bad hLF he hnodecl hFbad hR (hfamF b hb)).2⟩

/-- **From the deterministic lemma to the union bound.** If every configuration of the event `A` satisfies
`FinalHyps` for some sets whose undeclared blocks are bad, each block's bad event depends only on `Nbhd3`, and
(H_eps) holds on a set `R` containing the undeclared blocks, then `P(A) ≤ ∑_{k ∈ K} ε^{|keyBlocks e k.2.2|}` for a
finite set `K` of good skeletons rooted at `e`. -/
theorem union_from_final {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε)
    (Bad : V3 → (PEdge3 T w h → Bool) → Prop) (hdep : ∀ b, DependsOn (Bad b) (Nbhd3 b))
    {ny : ℕ} (hh : h + 1 = ny * 35) (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R)
    (hε : ∀ b ∈ R, prob p (Bad b) ≤ ε) (e : V3) (A : (PEdge3 T w h → Bool) → Prop)
    (hA : ∀ X, A X → ∃ (cfg : PEdge3 T w h → ZMod 2) (F Fl L : Finset V3) (reach0 reach1 : Finset V3 → Prop)
      (x : V3), FinalHyps cfg F Fl L reach0 reach1 ny e x ∧ ∀ b ∈ F, ¬ declared3 ny b → Bad b X) :
    ∃ K : Finset Skel3, (∀ k ∈ K, k.1 = e ∧ SkelOK k) ∧ prob p A ≤ ∑ k ∈ K, ε ^ (keyBlocks e k.2.2).length := by
  have hch : ∀ X, A X → ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ R) ∧ ∀ b ∈ keyBlocks e k.2.2, Bad b X := by
    intro X hX
    obtain ⟨cfg, F, Fl, L, reach0, reach1, x, hfin, hFbad⟩ := hA X hX
    obtain ⟨k, hk1, hok, _, hsep, hR', hbad⟩ := final_skeleton hh hfin hFbad hR
    exact ⟨k, hk1, hok, hsep, hR', hbad⟩
  have hmem : ∀ X ∈ Finset.univ.filter A, A X := fun X hX => (Finset.mem_filter.1 hX).2
  let f : {X // X ∈ Finset.univ.filter A} → Skel3 := fun X => Classical.choose (hch X.1 (hmem X.1 X.2))
  let K : Finset Skel3 := Finset.image f (Finset.univ.filter A).attach
  refine ⟨K, ?_, ?_⟩
  · intro k hk
    obtain ⟨X, _, rfl⟩ := Finset.mem_image.1 hk
    have hs := Classical.choose_spec (hch X.1 (hmem X.1 X.2))
    exact ⟨hs.1, hs.2.1⟩
  · calc prob p A
        ≤ ∑ k ∈ K.filter (fun k => (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b)),
            ε ^ (keyBlocks e k.2.2).length := by
          refine skel_union_le_rows hp0 hp1 hε0 Bad hdep R hε K (fun k => keyBlocks e k.2.2) fun X hX => ?_
          have hXm : X ∈ Finset.univ.filter A := Finset.mem_filter.2 ⟨Finset.mem_univ _, hX⟩
          have hs := Classical.choose_spec (hch X hX)
          exact ⟨Classical.choose (hch X hX), Finset.mem_image.2 ⟨⟨X, hXm⟩, Finset.mem_attach _ _, rfl⟩,
            hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
      _ ≤ ∑ k ∈ K, ε ^ (keyBlocks e k.2.2).length :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => pow_nonneg hε0 _

namespace Stage13

variable (S : Stage13 T w h)

/-- The flagged set `Fl` of the decoder. -/
noncomputable def flSet (E : PEdge3 T w h → ZMod 2) : Finset V3 := (latBlocks T w h).filter (S.flagged E)

/-- The bad set `F` of the decoder: the bad blocks and the declared blocks (convention (i)). -/
noncomputable def badSet (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : Finset V3 :=
  (latBlocks T w h).filter (fun c => S.bad E c ∨ declared3 ny c)

/-- The level-1 set `L` of the decoder. -/
noncomputable def levSet (reach0 : Finset V3 → Prop) (E : PEdge3 T w h → ZMod 2) : Finset V3 :=
  level1Set3 (S.flSet E) (blockPar3 (S.Fcfg E)) reach0

theorem flSet_sub (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : S.flSet E ⊆ S.badSet ny E := by
  intro c hc
  rw [flSet, Finset.mem_filter] at hc
  exact Finset.mem_filter.2 ⟨hc.1, Or.inl (Or.inl hc.2)⟩

theorem levSet_sub (reach0 : Finset V3 → Prop) (ny : ℕ) (E : PEdge3 T w h → ZMod 2) :
    S.levSet reach0 E ⊆ S.badSet ny E :=
  (level1Set3_sub _ _ _).trans (S.flSet_sub ny E)

/-- A2 by definition: an odd check of `E + C_0` lies in a flagged block. -/
theorem flSet_hA2 (E : PEdge3 T w h → ZMod 2) :
    ∀ v : PVert3 T w h, psyn3 (S.Fcfg E) v ≠ 0 → blockOf3 v ∈ S.flSet E :=
  fun v hv => Finset.mem_filter.2 ⟨blockOf3_mem_latBlocks v, v, rfl, hv⟩

/-- The bad set contains the long blocks. -/
theorem badSet_hlong (ny : ℕ) (E : PEdge3 T w h → ZMod 2) :
    ∀ c, c ∉ S.badSet ny E → NotLong3 (S.Fcfg E) c := by
  intro c hc
  by_contra hl
  have hc' : c ∈ latBlocks T w h := by
    by_contra hnot
    apply hl
    intro x0 hx0
    exact absurd (hx0 ▸ blockOf3_mem_latBlocks x0) hnot
  exact hc (Finset.mem_filter.2 ⟨hc', Or.inl (Or.inr hl)⟩)

/-- The bad set contains the declared blocks (convention (i)). -/
theorem badSet_hdeclF (ny : ℕ) (E : PEdge3 T w h → ZMod 2) :
    ∀ v : PVert3 T w h, declared3 ny (blockOf3 v) → blockOf3 v ∈ S.badSet ny E :=
  fun v hv => Finset.mem_filter.2 ⟨blockOf3_mem_latBlocks v, Or.inr hv⟩

/-- An undeclared block of the bad set is bad. -/
theorem badSet_bad (ny : ℕ) (E : PEdge3 T w h → ZMod 2) :
    ∀ b ∈ S.badSet ny E, ¬ declared3 ny b → S.bad E b :=
  fun _ hb hnd => ((Finset.mem_filter.1 hb).2).resolve_right hnd

/-- The event that the decoder has a family of `e` containing `x` that meets the strip hypotheses and is unresolved:
the hypotheses of `gen_skel3_final` that do not hold by definition. -/
def FamEvent (reach0 reach1 : Finset V3 → Prop) (ny : ℕ) (e x : V3) (E : PEdge3 T w h → ZMod 2) : Prop :=
  e ∈ S.levSet reach0 E ∧ x ∈ S.levSet reach0 E ∧ InFamily3 (S.badSet ny E) (S.levSet reach0 E) e x ∧
    (∀ r ∈ S.levSet reach0 E, InFamily3 (S.badSet ny E) (S.levSet reach0 E) e r →
      ∀ b ∈ clusterOf (S.badSet ny E) r, ¬ declared3 ny b) ∧
    (∀ b ∈ S.flSet E, (∃ k ∈ S.levSet reach0 E, SameComp (S.levSet reach0 E) Const.a1 e k ∧
      SameComp (S.badSet ny E) Const.a0 k b) → ¬ reach0 (clusterOf (S.flSet E) b)) ∧
    ¬ Resolved3 (blockPar3 (S.Fcfg E)) reach1
      ((S.levSet reach0 E).filter (fun b => SameComp (S.levSet reach0 E) Const.a1 e b))

/-- On `FamEvent`, the decoder's sets satisfy the hypotheses of `gen_skel3_final`. -/
theorem finalHyps_of_famEvent {reach0 reach1 : Finset V3 → Prop} {ny : ℕ} {e x : V3} {E : PEdge3 T w h → ZMod 2}
    (hev : S.FamEvent reach0 reach1 ny e x E) :
    FinalHyps (S.Fcfg E) (S.badSet ny E) (S.flSet E) (S.levSet reach0 E) reach0 reach1 ny e x := by
  obtain ⟨he, hx, hfam, hnodecl, hnoreach, hunres1⟩ := hev
  exact ⟨S.flSet_sub ny E, rfl, S.flSet_hA2 E, S.badSet_hlong ny E, S.badSet_hdeclF ny E, he, hx, hfam, hnodecl,
    hnoreach, hunres1⟩

/-- **The deterministic lemma for the decoder.** On `FamEvent` there is a good skeleton rooted at `e` whose counted
blocks are pairwise `D`-separated, bad, and not declared. -/
theorem gen_skel3_dec (E : PEdge3 T w h → ZMod 2) (reach0 reach1 : Finset V3 → Prop) (ny : ℕ)
    (hh : h + 1 = ny * 35) {e x : V3} (hev : S.FamEvent reach0 reach1 ny e x E) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, S.bad E b ∧ ¬ declared3 ny b) := by
  obtain ⟨k, hk1, hok, hdist, hsep, hR, hbad⟩ := final_skeleton (Bad := fun b E' => S.bad E' b) (X := E)
    (R := {b | ¬ declared3 ny b}) hh (S.finalHyps_of_famEvent hev) (S.badSet_bad ny E) (fun _ hb => hb)
  exact ⟨k, hk1, hok, hdist, hsep, fun b hb => ⟨hbad b hb, hR b hb⟩⟩

/-- **The probability of a family's event.** If (H_eps) holds on a set `R` of blocks that contains the undeclared ones,
then the probability that the decoder has a family of `e` containing `x` with the strip hypotheses, unresolved, is at
most `∑_{k ∈ K} ε^{|keyBlocks e k.2.2|}` for a finite set `K` of good skeletons rooted at `e`. -/
theorem famEvent_prob_le {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (ny : ℕ) (hh : h + 1 = ny * 35)
    (R : Set V3) (hR : ∀ b, ¬ declared3 ny b → b ∈ R) (hε : ∀ b ∈ R, prob p (fun X => S.bad (toZ2 X) b) ≤ ε)
    (reach0 reach1 : Finset V3 → Prop) (e x : V3) :
    ∃ K : Finset Skel3, (∀ k ∈ K, k.1 = e ∧ SkelOK k) ∧
      prob p (fun X => S.FamEvent reach0 reach1 ny e x (toZ2 X)) ≤ ∑ k ∈ K, ε ^ (keyBlocks e k.2.2).length :=
  union_from_final hp0 hp1 hε0 (fun b X => S.bad (toZ2 X) b) S.bad_dependsOn hh R hR hε e _ fun X hX =>
    ⟨S.Fcfg (toZ2 X), S.badSet ny (toZ2 X), S.flSet (toZ2 X), S.levSet reach0 (toZ2 X), reach0, reach1, x,
      S.finalHyps_of_famEvent hX, S.badSet_bad ny (toZ2 X)⟩

end Stage13

end QECD1
