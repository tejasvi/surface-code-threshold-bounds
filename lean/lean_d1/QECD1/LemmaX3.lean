import QECD1.LemmaC3

/-!
# (R), the strip families of Lemma C, and the path form of Lemma C (3D)

The 3D analogue of the second half of the 2D `TwoD/LemmaX` (the exchange itself is `exchange3`).

* `om_far3` ((R), second part): odd checks of `Ω` in different families lie in blocks more than `a1` apart (they lie
  in different level-1 components).
* `strip_bot_of_pcls3`, `strip_top_of_pclsT3`: a family whose `Y_𝓕` has odd class at `b₁` (`b₂`) has a block in the
  bottom (top) strip, the block rows `≤ hs3` (`≥ n_y - 1 - hs3`), `hs3 = a1/2 + 1`: the half-edge's check is in a
  block of the family, or in the region of a resolved component of the family (radius `≤ hs3`).
* `T1_of_spanning3`: a family with odd class at both boundaries has blocks in both strips.
* `exists_simple_chain`, `lemmaC3_path`: if the decoder fails, a simple path of `Γ` runs from `b₁` to `b₂`.
-/

open Finset

namespace QECD1

open Classical

variable {T w h : ℕ}

/-- The strip height `hs3 = a1/2 + 1`. -/
def hs3 : ℕ := Const.a1 / 2 + 1

theorem r0_le_hs3 : (Const.a0 + 1) / 2 ≤ hs3 := by decide
theorem r1_le_hs3 : (Const.a1 + 1) / 2 ≤ hs3 := by decide

/-- A block within distance `r` of the block of a check on the bottom side is in block row `≤ r`. -/
theorem row_bot {r : ℕ} {k : V3} (t : Fin (T + 1)) (x : Fin (w + 1))
    (hk : dist3 (blockOf3 ((t, x, 0) : PVert3 T w h)) k ≤ r) : k.2.2 ≤ r := by
  simp only [dist3, linf, blockOf3, blockOf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, max_le_iff] at hk
  simp only [Fin.val_zero, Nat.cast_zero, Int.zero_ediv] at hk
  omega

/-- A block within distance `r` of the block of a check on the top side is in block row `≥ n_y - 1 - r`. -/
theorem row_top {r ny : ℕ} (hh : h + 1 = ny * 35) {k : V3} (t : Fin (T + 1)) (x : Fin (w + 1))
    (hk : dist3 (blockOf3 ((t, x, Fin.last h) : PVert3 T w h)) k ≤ r) : (ny : ℤ) ≤ k.2.2 + 1 + r := by
  simp only [dist3, linf, blockOf3, blockOf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, max_le_iff, Fin.val_last]
    at hk
  omega

/-- A bottom half-edge ends in a block of row 0. -/
theorem row_bot_self (t : Fin (T + 1)) (x : Fin (w + 1)) : (blockOf3 ((t, x, 0) : PVert3 T w h)).2.2 = 0 := by
  simp [blockOf3, blockOf, PVert3.toV3]

/-- A top half-edge ends in a block of row `n_y - 1`. -/
theorem row_top_self {ny : ℕ} (hh : h + 1 = ny * 35) (t : Fin (T + 1)) (x : Fin (w + 1)) :
    (ny : ℤ) ≤ (blockOf3 ((t, x, Fin.last h) : PVert3 T w h)).2.2 + 1 := by
  simp only [blockOf3, blockOf, PVert3.toV3, Fin.val_last]
  omega

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **(R), second part**: odd checks of `Ω` in different families lie in blocks more than `a1` apart. -/
theorem om_far3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {u v : PVert3 T w h} (hu : S.om3 E u ≠ 0) (hv : S.om3 E v ≠ 0)
    (hne : famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) ≠
      famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 v)) :
    Const.a1 < dist3 (blockOf3 u) (blockOf3 v) := by
  have hlev : ∀ {x : PVert3 T w h}, S.om3 E x ≠ 0 → blockOf3 x ∈ S.levSet (reach3 T w h r0) E := fun {x} hx => by
    simp only [om3, omega3] at hx
    split_ifs at hx with hc
    · rw [← lev1Set3_eq]
      exact hc.1
    · exact absurd rfl hx
  refine not_le.mp fun hd => hne ?_
  have hu1 := hlev hu
  have hv1 := hlev hv
  have hLF := S.levSet_sub (reach3 T w h r0) ny E
  have hmem : blockOf3 v ∈ famF (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (blockOf3 u) :=
    mem_famF.2 ⟨hLF hv1, .single ⟨hLF hu1, hLF hv1, Or.inr ⟨hu1, hv1, .single ⟨hu1, hv1, hd⟩⟩⟩⟩
  exact (famF_eq_of_mem hmem).symm

/-- A correction of a resolved component meeting the family, nonzero on an edge, has the edge's ends in its region;
so the ends are within the region's radius of a block of the family. -/
theorem corr_near {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) {e : PEdge3 T w h} {v : PVert3 T w h}
    (hv : v ∈ e.ends) :
    ((∑ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a0 + 1) / 2) E K) e ≠ 0 →
      ∃ k ∈ Fm, dist3 (blockOf3 v) k ≤ (Const.a0 + 1) / 2) ∧
    ((∑ K ∈ (S.res1 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a1 + 1) / 2) E K) e ≠ 0 →
      ∃ k ∈ Fm, dist3 (blockOf3 v) k ≤ (Const.a1 + 1) / 2) := by
  constructor
  · intro hne
    rw [Finset.sum_apply] at hne
    obtain ⟨K, hK, hKe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
    obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
    obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK1
    obtain ⟨k', hk', hdk⟩ := Z.inside _ _ (realizable_resolved (flagSet3_blocks _) hres) e hKe v hv
    exact ⟨k', res0_sub hFm hKr hk hkF hk', hdk⟩
  · intro hne
    rw [Finset.sum_apply] at hne
    obtain ⟨K, hK, hKe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hKr, k, hk, hkF⟩ := Finset.mem_filter.1 hK
    obtain ⟨hK1, hres⟩ := Finset.mem_filter.1 hKr
    obtain ⟨c, _, rfl⟩ := mem_comps3.1 hK1
    obtain ⟨k', hk', hdk⟩ := Z.inside _ _ (realizable_resolved (lev1Set3_blocks _) hres) e hKe v hv
    exact ⟨k', res1_sub hFm hKr hk hkF hk', hdk⟩

/-- **A family whose `Y_𝓕` has odd class at `b₁` has a block in the bottom strip.** -/
theorem strip_bot_of_pcls3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) (hc : pcls3 (S.Yfam3 Z E Fm) ≠ 0) :
    ∃ c ∈ Fm, c.2.2 ≤ hs3 := by
  unfold pcls3 at hc
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  have hv : ((t, x, 0) : PVert3 T w h) ∈ (PEdge3.bot t x : PEdge3 T w h).ends := by simp [PEdge3.ends]
  have hnear := S.corr_near Z hFm hv
  simp only [Yfam3, Pi.add_apply] at hx
  by_cases h1 : edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.bot t x) ≠ 0
  · have hQ : ((t, x, 0) : PVert3 T w h) ∈ compUnion3 (S.Fcfg E) Fm := by
      by_contra hn
      exact h1 (by simp [edgesIn, PEdge3.ends, hn])
    have hb : blockOf3 ((t, x, 0) : PVert3 T w h) ∈ S.badSet ny E := S.badSet_hdeclF ny E _ (declared_bot ny t x)
    refine ⟨_, mem_of_famQ (S.badSet_hlong ny E) hFm (families3_sub hFm) hQ hb, ?_⟩
    rw [row_bot_self]
    exact Nat.cast_nonneg _
  · push Not at h1
    rw [h1, zero_add] at hx
    by_cases h2 : (∑ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a0 + 1) / 2) E K)
        (.bot t x) ≠ 0
    · obtain ⟨k, hk, hdk⟩ := hnear.1 h2
      have := row_bot t x hdk
      exact ⟨k, hk, by have := r0_le_hs3; omega⟩
    · push Not at h2
      rw [h2, zero_add] at hx
      obtain ⟨k, hk, hdk⟩ := hnear.2 hx
      have := row_bot t x hdk
      exact ⟨k, hk, by have := r1_le_hs3; omega⟩

/-- **A family whose `Y_𝓕` has odd class at `b₂` has a block in the top strip.** -/
theorem strip_top_of_pclsT3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) (hc : pclsT3 (S.Yfam3 Z E Fm) ≠ 0) :
    ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3 := by
  unfold pclsT3 at hc
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  have hv : ((t, x, Fin.last h) : PVert3 T w h) ∈ (PEdge3.top t x : PEdge3 T w h).ends := by simp [PEdge3.ends]
  have hnear := S.corr_near Z hFm hv
  simp only [Yfam3, Pi.add_apply] at hx
  by_cases h1 : edgesIn (S.Fcfg E) (compUnion3 (S.Fcfg E) Fm) (.top t x) ≠ 0
  · have hQ : ((t, x, Fin.last h) : PVert3 T w h) ∈ compUnion3 (S.Fcfg E) Fm := by
      by_contra hn
      exact h1 (by simp [edgesIn, PEdge3.ends, hn])
    have hdecl : declared3 ny (blockOf3 ((t, x, Fin.last h) : PVert3 T w h)) :=
      declared_of_rough ny hh _ (Or.inr (by simp))
    have hb : blockOf3 ((t, x, Fin.last h) : PVert3 T w h) ∈ S.badSet ny E := S.badSet_hdeclF ny E _ hdecl
    refine ⟨_, mem_of_famQ (S.badSet_hlong ny E) hFm (families3_sub hFm) hQ hb, ?_⟩
    have := row_top_self hh t x
    omega
  · push Not at h1
    rw [h1, zero_add] at hx
    by_cases h2 : (∑ K ∈ (S.res0 E).filter (fun K => ∃ c ∈ K, c ∈ Fm), S.corrK Z ((Const.a0 + 1) / 2) E K)
        (.top t x) ≠ 0
    · obtain ⟨k, hk, hdk⟩ := hnear.1 h2
      have := row_top hh t x hdk
      exact ⟨k, hk, by have := r0_le_hs3; omega⟩
    · push Not at h2
      rw [h2, zero_add] at hx
      obtain ⟨k, hk, hdk⟩ := hnear.2 hx
      have := row_top hh t x hdk
      exact ⟨k, hk, by have := r1_le_hs3; omega⟩

/-- **A spanning family has blocks in both strips.** -/
theorem T1_of_spanning3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) (h1 : pcls3 (S.Yfam3 Z E Fm) ≠ 0)
    (h2 : pclsT3 (S.Yfam3 Z E Fm) ≠ 0) :
    (∃ c ∈ Fm, c.2.2 ≤ hs3) ∧ ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3 :=
  ⟨S.strip_bot_of_pcls3 Z hFm h1, S.strip_top_of_pclsT3 Z hh hFm h2⟩

end Stage13

/-- A reflexive-transitive chain contains a simple one (a path with distinct nodes). -/
theorem exists_simple_chain {α : Type} {r : α → α → Prop} {a b : α} (hab : Relation.ReflTransGen r a b) :
    ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧
      List.IsChain (fun x y => x ≠ y ∧ (r x y ∨ r y x)) l := by
  have hreach : (SimpleGraph.fromRel r).Reachable a b := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    induction hab with
    | refl => exact .refl
    | @tail c d _ hcd ih =>
      by_cases hc : c = d
      · rw [← hc]
        exact ih
      · exact ih.tail ((SimpleGraph.fromRel_adj r c d).2 ⟨hc, Or.inl hcd⟩)
  obtain ⟨wk⟩ := hreach
  refine ⟨wk.toPath.1.support, ?_, ?_, wk.toPath.isPath.support_nodup, ?_⟩
  · rw [List.head?_eq_some_head (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _), SimpleGraph.Walk.getLast_support]
  · exact (SimpleGraph.Walk.isChain_adj_support wk.toPath.1).imp fun x y hxy =>
      (SimpleGraph.fromRel_adj r x y).1 hxy

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **Lemma C, path form**: if the decoder fails, a simple path of `Γ` runs from `b₁` to `b₂`. -/
theorem lemmaC3_path {ny : ℕ} {E : PEdge3 T w h → ZMod 2} (hfail : failsOn3 (dec3 S Z) E) :
    ∃ l : List (GNode3 T w h), l.head? = some (.inr (.inl false)) ∧ l.getLast? = some (.inr (.inl true)) ∧
      l.Nodup ∧ List.IsChain (S.gadj3 Z ny E) l := by
  obtain ⟨l, hhd, hlt, hnd, hch⟩ := exists_simple_chain (S.lemmaC3 Z (ny := ny) hfail)
  refine ⟨l, hhd, hlt, hnd, hch.imp fun x y hxy => ?_⟩
  rcases hxy.2 with hr | hr
  · exact hr
  · exact (Or.comm.1 hr)

end Stage13

end QECD1
