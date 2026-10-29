import QECD1.NonVac3

/-!
# P2 from P1 (2D `lev1_parity`)

P2 says that the level-1 residual is even on a union of interior clusters. It follows from three facts:
* P1: each of these clusters is even;
* a resolved interior level-0 component is even;
* level-1 membership is a property of level-0 components.

The last two are definitional in the decoder (2D `resolved`, `level1Set`). The argument:
* a union of whole components with even component sums has even total (`sum_union_comps_zero`, by peeling off one
  component at a time);
* apply this to the clusters of the union, and to the resolved level-0 components in it;
* the level-1 part is what remains (`lev1_parity3`).

`gen_skel3_parity_family2` is `gen_skel3_parity_family` with P2 replaced by these facts. Its decoder facts are A2
(`hpar`), P1 (`hP1`) and three definitional ones (`hP0`, `hodd1`, `hres` with `hLcomp`). `main_nonvac2` applies it to
the example of NonVac3.
-/

namespace QECD1

open Classical

/-- Blocks in one cluster have the same cluster. -/
theorem clusterOf_eq {G : Finset V3} {k b : V3} (hkb : SameComp G Const.a0 k b) : clusterOf G b = clusterOf G k := by
  ext c
  rw [mem_clusterOf, mem_clusterOf]
  constructor
  · rintro ⟨hc, hbc⟩
    exact ⟨hc, hkb.trans hbc⟩
  · rintro ⟨hc, hkc⟩
    exact ⟨hc, (sameComp_symm G _ hkb).trans hkc⟩

/-- **A union of whole components with even component sums has even total.** -/
theorem sum_union_comps_zero (G : Finset V3) (par : V3 → ZMod 2) :
    ∀ (n : ℕ) (U : Finset V3), U.card ≤ n → U ⊆ G → (∀ b ∈ U, clusterOf G b ⊆ U) →
      (∀ b ∈ U, ∑ c ∈ clusterOf G b, par c = 0) → ∑ c ∈ U, par c = 0
  | 0, U, hn, _, _, _ => by
    have hU0 : U = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [hU0, Finset.sum_empty]
  | n + 1, U, hn, hUG, hcl, hev => by
    by_cases hU : U = ∅
    · rw [hU, Finset.sum_empty]
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.2 hU
    have hCU : clusterOf G b ⊆ U := hcl b hb
    rw [← Finset.sum_sdiff hCU, hev b hb, add_zero]
    refine sum_union_comps_zero G par n (U \ clusterOf G b) ?_ ?_ ?_ ?_
    · have hbC : b ∈ clusterOf G b := self_mem_clusterOf (hUG hb)
      have hsd : (U \ clusterOf G b).card = U.card - (clusterOf G b ∩ U).card := Finset.card_sdiff
      rw [Finset.inter_eq_left.2 hCU] at hsd
      have hC1 : 1 ≤ (clusterOf G b).card := Finset.card_pos.2 ⟨b, hbC⟩
      have hle : (clusterOf G b).card ≤ U.card := Finset.card_le_card hCU
      omega
    · exact fun x hx => hUG (Finset.mem_sdiff.1 hx).1
    · intro x hx y hy
      obtain ⟨hxU, hxC⟩ := Finset.mem_sdiff.1 hx
      refine Finset.mem_sdiff.2 ⟨hcl x hxU hy, fun hyC => hxC ?_⟩
      obtain ⟨_, hxy⟩ := mem_clusterOf.1 hy
      obtain ⟨_, hby⟩ := mem_clusterOf.1 hyC
      exact mem_clusterOf.2 ⟨hUG hxU, hby.trans (sameComp_symm G _ hxy)⟩
    · exact fun x hx => hev x (Finset.mem_sdiff.1 hx).1

/-- **P2** (2D `lev1_parity`): in a union `U` of even clusters whose resolved level-0 components are even, the
level-1 blocks have even total parity. -/
theorem lev1_parity3 (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F) (par : V3 → ZMod 2)
    (hpar : ∀ b, par b ≠ 0 → b ∈ Fl) {U : Finset V3} (hUF : U ⊆ F) (hcl : ∀ b ∈ U, clusterOf F b ⊆ U)
    (hP1 : ∀ b ∈ U, ∑ c ∈ clusterOf F b, par c = 0)
    (hLcomp : ∀ b ∈ U, b ∈ Fl → b ∉ L → ∀ c ∈ clusterOf Fl b, c ∉ L)
    (hres : ∀ b ∈ U, b ∈ Fl → b ∉ L → ∑ c ∈ clusterOf Fl b, par c = 0) :
    ∑ c ∈ U.filter (fun c => c ∈ L), par c = 0 := by
  have htot : ∑ c ∈ U, par c = 0 := sum_union_comps_zero F par U.card U le_rfl hUF hcl hP1
  -- the resolved flagged part is a union of even level-0 components
  set V := U.filter (fun c => c ∈ Fl ∧ c ∉ L) with hV
  have hVsub : ∀ b ∈ V, b ∈ U ∧ b ∈ Fl ∧ b ∉ L := fun b hb => by
    rw [hV, Finset.mem_filter] at hb
    exact ⟨hb.1, hb.2.1, hb.2.2⟩
  have hVtot : ∑ c ∈ V, par c = 0 := by
    refine sum_union_comps_zero Fl par V.card V le_rfl (fun b hb => (hVsub b hb).2.1) ?_ ?_
    · intro b hb c hc
      obtain ⟨hbU, hbFl, hbL⟩ := hVsub b hb
      obtain ⟨hcFl, hbc⟩ := mem_clusterOf.1 hc
      have hcU : c ∈ U := hcl b hbU (mem_clusterOf.2 ⟨hFl hcFl, sameComp_mono_set hFl hbc⟩)
      rw [hV, Finset.mem_filter]
      exact ⟨hcU, hcFl, hLcomp b hbU hbFl hbL c hc⟩
    · intro b hb
      obtain ⟨hbU, hbFl, hbL⟩ := hVsub b hb
      exact hres b hbU hbFl hbL
  -- the unflagged part has zero parity
  have hW : ∑ c ∈ U.filter (fun c => c ∉ Fl), par c = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    by_contra h
    exact (Finset.mem_filter.1 hc).2 (hpar c h)
  -- split `U` into the level-1 part, the resolved flagged part and the unflagged part
  have hsplit1 := Finset.sum_filter_add_sum_filter_not U (fun c => c ∈ L) par
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (U.filter (fun c => c ∉ L)) (fun c => c ∈ Fl) par
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
  have e1 : U.filter (fun c => c ∉ L ∧ c ∈ Fl) = V := by
    rw [hV]
    exact Finset.filter_congr fun c _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have e2 : U.filter (fun c => c ∉ L ∧ c ∉ Fl) = U.filter (fun c => c ∉ Fl) :=
    Finset.filter_congr fun c _ => ⟨fun h => h.2, fun h => ⟨fun hL => h (hLFl hL), h⟩⟩
  rw [e1, e2, hVtot, hW, add_zero] at hsplit2
  rw [← hsplit2, add_zero, htot] at hsplit1
  exact hsplit1

/-- **Every family has a good skeleton, from A2, P1 and the definitional decoder facts.** This is
`gen_skel3_parity_family` with P2 derived by `lev1_parity3`. The extra hypotheses, for the flagged blocks of the
clusters meeting the level-1 component of `e`, are:
* `hLcomp`: level-1 membership is constant on level-0 components;
* `hres`: a resolved (non-level-1) level-0 component there is even. -/
theorem gen_skel3_parity_family2 (F Fl L : Finset V3) (hLFl : L ⊆ Fl) (hFl : Fl ⊆ F) (par : V3 → ZMod 2)
    (hpar : ∀ b, par b ≠ 0 → b ∈ Fl) {e x : V3} (he : e ∈ L) (hx : x ∈ L) (hfam : InFamily3 F L e x)
    (hP0 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf Fl r, par b ≠ 0)
    (hP1 : ∀ r ∈ L, InFamily3 F L e r → ∑ b ∈ clusterOf F r, par b = 0)
    (hodd1 : ∑ b ∈ L.filter (fun b => SameComp L Const.a1 e b), par b ≠ 0)
    (hLcomp : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∀ c ∈ clusterOf Fl b, c ∉ L)
    (hres : ∀ b ∈ Fl, (∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) → b ∉ L →
      ∑ c ∈ clusterOf Fl b, par c = 0) :
    ∃ k : Skel3, k.1 = e ∧ SkelOK k ∧ dist3 x (endOf e (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks e k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks e k.2.2, b ∈ famF F L e) ∧
      (keyBlocks e k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length := by
  have hLF : L ⊆ F := hLFl.trans hFl
  -- the union of the clusters meeting the level-1 component of `e`
  set U := F.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) with hU
  have hmemU : ∀ b, b ∈ U ↔ b ∈ F ∧ ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b := fun b => by
    rw [hU, Finset.mem_filter]
  have hP2 : ∑ b ∈ L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b), par b = 0 := by
    have hset : L.filter (fun b => ∃ k ∈ L, SameComp L Const.a1 e k ∧ SameComp F Const.a0 k b) =
        U.filter (fun c => c ∈ L) := by
      ext b
      rw [Finset.mem_filter, Finset.mem_filter, hmemU]
      exact ⟨fun h => ⟨⟨hLF h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
    rw [hset]
    refine lev1_parity3 F Fl L hLFl hFl par hpar (fun b hb => ((hmemU b).1 hb).1) ?_ ?_ ?_ ?_
    · intro b hb c hc
      obtain ⟨_, k, hkL, hek, hkb⟩ := (hmemU b).1 hb
      obtain ⟨hcF, hbc⟩ := mem_clusterOf.1 hc
      exact (hmemU c).2 ⟨hcF, k, hkL, hek, hkb.trans hbc⟩
    · intro b hb
      obtain ⟨_, k, hkL, hek, hkb⟩ := (hmemU b).1 hb
      rw [clusterOf_eq hkb]
      exact hP1 k hkL (sameComp_famL hLF (e := e) .refl hek).2
    · intro b hb hbFl hbL
      exact hLcomp b hbFl ((hmemU b).1 hb).2 hbL
    · intro b hb hbFl hbL
      exact hres b hbFl ((hmemU b).1 hb).2 hbL
  exact gen_skel3_parity_family F Fl L hLFl hFl par hpar he hx hfam hP0 hP1 hodd1 hP2

/-- **`gen_skel3_parity_family2` is not vacuous**: it applies to the example of NonVac3, where every flagged block is
level-1, so `hLcomp` and `hres` hold trivially. -/
theorem main_nonvac2 :
    ∃ k : Skel3, k.1 = (0, 0, 0) ∧ SkelOK k ∧
      dist3 (0, 0, 0) (endOf (0, 0, 0) (k.2.2.1 ++ k.2.2.2.2)) ≤ Const.D - 1 ∧
      (keyBlocks (0, 0, 0) k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (∀ b ∈ keyBlocks (0, 0, 0) k.2.2, b ∈ famF exF exL (0, 0, 0)) ∧
      (keyBlocks (0, 0, 0) k.2.2).length = 1 + k.2.2.1.length + witLen k.2.2.2.1 + k.2.2.2.2.length :=
  gen_skel3_parity_family2 exF exL exL (Finset.Subset.refl _) exL_sub exPar ex_hpar (by decide) (by decide) .refl
    ex_hP0 ex_hP1 ex_hodd1 (fun _ hb _ hbL => absurd hb hbL) (fun _ hb _ hbL => absurd hb hbL)

end QECD1
