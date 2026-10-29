import QECD1.T2Sk3

/-!
# Existence of 3D T2 skeletons

The 3D analogue of the 2D `Stage1.t2SkelExistsOn` (TwoD/T2Count): every error in the T2 event without T1 has a
valid 3D T2 skeleton (`T2Sk3.OK`) whose counted blocks are bad.

* `tailOK_range`, `tailOKex_range`: a tail of families indexed `1, …, m` is valid in the transfer's sense when its
  roots, skeletons, jumps and top are.
* `station_facts3`, `station_inj3`: the families at the stations of a T2 path, with their entry and exit checks.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

theorem covAt_zero (c : V3) (K : ℕ → Skel3) : covAt c K 0 = c := if_pos rfl

theorem covAt_succ (c : V3) (K : ℕ → Skel3) (i : ℕ) : covAt c K (i + 1) = exitSk (K (i + 1)) :=
  if_neg (Nat.succ_ne_zero i)

theorem covAt_shift (c : V3) (K : ℕ → Skel3) (i : ℕ) :
    covAt (exitSk (K 1)) (fun j => K (j + 1)) i = covAt c K (i + 1) := by
  rw [covAt_succ]
  unfold covAt
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl]
  · rw [if_neg hi]

/-- **A tail of families indexed `1, …, m`** is valid in the transfer's sense if every family's skeleton is good
and rooted at its landing root, every jump is valid, and the top is valid from the last cover. -/
theorem tailOK_range (Y : ℤ) (top : Top3) : ∀ (m : ℕ) (R : ℕ → V3) (K : ℕ → Skel3) (c : V3),
    (∀ i < m, (K (i + 1)).1 = R (i + 1) ∧ SkelOK (K (i + 1))) →
    (∀ i < m, jok3 (covAt c K i) (R (i + 1))) → tok3 Y (covAt c K m) top →
    (t2TD Y).TailOK c ((List.range m).map (fun i => (R (i + 1), K (i + 1)))) top
  | 0, R, K, c, _, _, htop => by
    simp only [List.range_zero, List.map_nil]
    rw [covAt_zero] at htop
    exact htop
  | m + 1, R, K, c, hk, hj, htop => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hj0 := hj 0 (Nat.succ_pos _)
    rw [covAt_zero] at hj0
    refine ⟨hj0, (hk 0 (Nat.succ_pos _)).1, (hk 0 (Nat.succ_pos _)).2, ?_⟩
    have ih := tailOK_range Y top m (fun j => R (j + 1)) (fun j => K (j + 1)) (exitSk (K 1))
      (fun i hi => hk (i + 1) (by omega))
      (fun i hi => by rw [covAt_shift c K i]; exact hj (i + 1) (by omega))
      (by rw [covAt_shift c K m]; exact htop)
    exact ih

/-- **A tail with an exempt first jump** (from the bottom part's cover). -/
theorem tailOKex_range (Y : ℤ) (top : Top3) (m : ℕ) (R : ℕ → V3) (K : ℕ → Skel3) (c : V3)
    (hk : ∀ i < m, (K (i + 1)).1 = R (i + 1) ∧ SkelOK (K (i + 1)))
    (hj : ∀ i, 1 ≤ i → i < m → jok3 (exitSk (K i)) (R (i + 1)))
    (h0 : m = 0 → tok3ex Y c top) (hm : 1 ≤ m → tok3 Y (exitSk (K m)) top) :
    (t2TD Y).TailOKex (tok3ex Y) c ((List.range m).map (fun i => (R (i + 1), K (i + 1)))) top := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    simp only [List.range_zero, List.map_nil]
    exact h0 rfl
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨(hk 0 (Nat.succ_pos _)).1, (hk 0 (Nat.succ_pos _)).2, ?_⟩
    exact tailOK_range Y top m' (fun j => R (j + 1)) (fun j => K (j + 1)) (exitSk (K 1))
      (fun i hi => hk (i + 1) (by omega))
      (fun i hi => by rw [covAt_shift c K i, covAt_succ]; exact hj (i + 1) (by omega) (by omega))
      (by rw [covAt_shift c K m', covAt_succ]; exact hm (by omega))

/-- Distinct stations hold distinct nodes. -/
theorem station_inj3 {l : List (GNode3 T w h)} (hnd : l.Nodup) {m : ℕ} {p : ℕ → ℕ}
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hpl : p (m + 1) = l.length - 1) (hlen : 2 ≤ l.length)
    {i j : ℕ} (hi : i ≤ m + 1) (hj : j ≤ m + 1) (hij : nd3 l (p i) = nd3 l (p j)) : i = j := by
  have hlt : ∀ k ≤ m + 1, p k < l.length := by
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hk'
    · omega
    · have := hp k (m + 1) hk' le_rfl
      omega
  have hpij := (nd3_eq_iff hnd (hlt i hi) (hlt j hj)).1 hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt'
  · have := hp i j hlt' hj
    omega
  · have := hp j i hgt' hi
    omega

/-- **The metric constraint, converted to covers and roots**: each check-level jump (from the exit check `X i` to
the entry check `R (i+1)`, in block units) differs from the jump from the cover `C i` by at most `12`, and each
family span likewise. -/
theorem metric_convert3 (m : ℕ) (R X C : ℕ → V3) (hC : ∀ i ≤ m, dist3 (X i) (C i) ≤ Const.D - 1) (Lg : ℝ)
    (hmet : (35 : ℝ) * ∑ i ∈ range (m + 1), (l1 (X i - R (i + 1)) : ℝ) ≤
      (35 : ℝ) * ∑ i ∈ range m, (l1 (R (i + 1) - X (i + 1)) : ℝ) + ((m + 1 : ℝ) + m) * 102 + Lg) :
    (∑ i ∈ range (m + 1), (l1 (R (i + 1) - C i) : ℝ)) ≤
      ∑ i ∈ range m, (l1 (C (i + 1) - R (i + 1)) : ℝ) + m * (24 + 204 / 35) + (12 + 102 / 35) + Lg / 35 := by
  have h1 : ∀ i ∈ range (m + 1), (l1 (R (i + 1) - C i) : ℝ) ≤ (l1 (X i - R (i + 1)) : ℝ) + 12 := by
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.1 hi
      omega
    have t1 := l1_sub_le (R (i + 1)) (X i) (C i)
    have t2 := l1_sub_comm (R (i + 1)) (X i)
    have t3 := l1_le_of_dist3 (hC i hi')
    have hn : l1 (R (i + 1) - C i) ≤ l1 (X i - R (i + 1)) + 12 := by omega
    exact_mod_cast hn
  have h2 : ∀ i ∈ range m, (l1 (R (i + 1) - X (i + 1)) : ℝ) ≤ (l1 (C (i + 1) - R (i + 1)) : ℝ) + 12 := by
    intro i hi
    have hi' : i + 1 ≤ m := by
      have := Finset.mem_range.1 hi
      omega
    have t1 := l1_sub_le (R (i + 1)) (C (i + 1)) (X (i + 1))
    have t2 := l1_sub_comm (R (i + 1)) (C (i + 1))
    have t3 := l1_le_of_dist3 (hC (i + 1) hi')
    have t4 := l1_sub_comm (C (i + 1)) (X (i + 1))
    have hn : l1 (R (i + 1) - X (i + 1)) ≤ l1 (C (i + 1) - R (i + 1)) + 12 := by omega
    exact_mod_cast hn
  have s1 := Finset.sum_le_sum h1
  have s2 := Finset.sum_le_sum h2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at s1 s2
  push_cast at s1 s2
  linarith

/-- Level-1 blocks of different families are not `a1`-connected in `L`. -/
theorem not_sameComp_of_fam_ne {F L : Finset V3} (hLF : L ⊆ F) {Fm Fm' : Finset V3} (hFm : Fm ∈ families3 F L)
    (hFm' : Fm' ∈ families3 F L) (hne : Fm ≠ Fm') {c d : V3} (hc : c ∈ Fm) (hd : d ∈ Fm') (hcL : c ∈ L)
    (hdL : d ∈ L) : ¬ SameComp L Const.a1 c d := by
  intro hcd
  have hdc : d ∈ Fm := by
    rw [← famF_eq_of_mem_families3 hFm hc]
    exact mem_famF.2 ⟨hLF hdL, Relation.ReflTransGen.single ⟨hLF hcL, hLF hdL, Or.inr ⟨hcL, hdL, hcd⟩⟩⟩
  exact hne (families3_eq_of_mem hFm hFm' hdc hd)

/-- Families at distinct stations of a T2 path are distinct. -/
theorem station_fam_ne3 {l : List (GNode3 T w h)} (hnd : l.Nodup) {m : ℕ} {p : ℕ → ℕ}
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hpl : p (m + 1) = l.length - 1) (hlen : 2 ≤ l.length)
    {i j : ℕ} (hi : i ≤ m + 1) (hj : j ≤ m + 1) (hij : i ≠ j) {G G' : Finset V3}
    (hG : nd3 l (p i) = .inr (.inr G)) (hG' : nd3 l (p j) = .inr (.inr G')) : G ≠ G' := by
  intro hGG
  exact hij (station_inj3 hnd hp hpl hlen hi hj (by rw [hG, hG', hGG]))

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- **The families at the stations of a T2 path**: at each intermediate station a family with no block in either
strip, entered at an odd check of `Ω` in one of its blocks and left at another. -/
theorem station_facts3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hhd : l.head? = some x) (hlst : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj3 Z ny E) l) (hint : ∀ z ∈ l, z ≠ x → z ≠ y → S.interFam3 ny E z)
    {m : ℕ} {p : ℕ → ℕ} {u v : ℕ → PVert3 T w h}
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hp0 : p 0 = 0) (hpl : p (m + 1) = l.length - 1)
    (hfam : ∀ i, 1 ≤ i → i ≤ m → isFam3 (nd3 l (p i)))
    (hu : ∀ i, 1 ≤ i → i ≤ m + 1 → nd3 l (p i - 1) = .inl (u i))
    (hv : ∀ i ≤ m, nd3 l (p i + 1) = .inl (v i)) (hlen : 2 ≤ l.length) :
    ∃ Fs : ℕ → Finset V3, ∀ i, 1 ≤ i → i ≤ m →
      nd3 l (p i) = .inr (.inr (Fs i)) ∧ Fs i ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧
      (∀ c ∈ Fs i, (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny) ∧
      blockOf3 (u i) ∈ Fs i ∧ S.om3 E (u i) ≠ 0 ∧ blockOf3 (v i) ∈ Fs i ∧ S.om3 E (v i) ≠ 0 := by
  have hex : ∀ i, ∃ F : Finset V3, 1 ≤ i → i ≤ m → nd3 l (p i) = .inr (.inr F) := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ m
    · obtain ⟨F, hF⟩ := hfam i hi.1 hi.2
      exact ⟨F, fun _ _ => hF⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose Fs hFs using hex
  refine ⟨Fs, fun i hi1 him => ?_⟩
  have hnode := hFs i hi1 him
  have hpi : 0 < p i := by
    have := hp 0 i (by omega) (by omega)
    omega
  have hpim : p i + 1 < l.length := by
    have := hp i (m + 1) (by omega) le_rfl
    omega
  have hplt : p i < l.length := by omega
  have hg1 : S.gadj3 Z ny E (nd3 l (p i - 1)) (nd3 l (p i)) :=
    chain_step hch (getElem?_nd3 (by omega)) (by rw [show p i - 1 + 1 = p i by omega]; exact getElem?_nd3 hplt)
  rw [hu i hi1 (by omega), hnode] at hg1
  obtain ⟨hFm, hu1, hou⟩ := S.gadj_check_fam3 Z hg1
  have hg2 : S.gadj3 Z ny E (nd3 l (p i)) (nd3 l (p i + 1)) :=
    chain_step hch (getElem?_nd3 hplt) (getElem?_nd3 hpim)
  rw [hnode, hv i (by omega)] at hg2
  obtain ⟨-, hv1, hov⟩ := S.gadj_fam_check3 Z hg2
  have hx0 : nd3 l 0 = x := nd3_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hyl : nd3 l (l.length - 1) = y := nd3_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have hmem : (.inr (.inr (Fs i)) : GNode3 T w h) ∈ l := by
    rw [← hnode, nd3_of_getElem? (List.getElem?_eq_getElem hplt)]
    exact List.getElem_mem hplt
  have hnx : (.inr (.inr (Fs i)) : GNode3 T w h) ≠ x := by
    intro hcon
    rw [← hnode, ← hx0, nd3_eq_iff hnd hplt (by omega)] at hcon
    omega
  have hny : (.inr (.inr (Fs i)) : GNode3 T w h) ≠ y := by
    intro hcon
    rw [← hnode, ← hyl, nd3_eq_iff hnd hplt (by omega)] at hcon
    have := hp i (m + 1) (by omega) le_rfl
    omega
  obtain ⟨-, hall⟩ := hint _ hmem hnx hny
  exact ⟨hnode, hFm, hall, hu1, hou, hv1, hov⟩

theorem badSet_sub_lat (ny : ℕ) (E : PEdge3 T w h → ZMod 2) : S.badSet ny E ⊆ latBlocks T w h :=
  fun _ hc => (Finset.mem_filter.1 hc).1

theorem fam_sub_bad {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E)) : Fm ⊆ S.badSet ny E := by
  obtain ⟨c0, -, hc0⟩ := mem_families3.1 hFm
  rw [← hc0]
  exact famF_sub _ _ _

/-- **The bottom part of a T2 skeleton**: from `b₁` (the block of the check next to it, not counted, no route) or
from a bottom-strip family (`bot_route3`). -/
theorem bottom_part3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} (hT1 : ¬ S.T1ev3 ny E)
    {x : GNode3 T w h} {v0 : PVert3 T w h}
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hadj : S.gadj3 Z ny E x (.inl v0)) :
    ∃ (b0 : V3) (ms0 : List Tok), b0 ∈ latBlocks T w h ∧ b0.2.2 ≤ hs3 ∧ route3.Gram 1 ms0 ∧
      dist3 (blockOf3 v0) (endOf b0 ms0) ≤ Const.D - 1 ∧ (endOf b0 ms0).2.2 + 1 ≤ ny ∧
      (blocksOf b0 ms0).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      ∀ b ∈ blocksOf b0 ms0, S.bad E b ∧ ¬ declared3 ny b ∧ b ∈ latBlocks T w h ∧
        ∃ G, x = .inr (.inr G) ∧ G ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ b ∈ G := by
  rcases hx with rfl | hbf
  · rcases hadj with hg | hg
    · simp [gadj0] at hg
    · obtain ⟨t, x', rfl, -⟩ := hg
      refine ⟨blockOf3 ((t, x', 0) : PVert3 T w h), [], blockOf3_mem_latBlocks _, ?_, trivial, ?_, ?_,
        List.Pairwise.nil,
        fun b hb => absurd hb (by simp [blocksOf])⟩
      · rw [row_bot_self]
        exact Int.natCast_nonneg _
      · simp [endOf, dist3_self]
      · simp only [endOf]
        rw [row_bot_self]
        omega
  · rcases x with u0 | b | F0
    · simp [botFam3] at hbf
    · simp [botFam3] at hbf
    · obtain ⟨hF0, hbot⟩ := hbf
      obtain ⟨-, hx0, -⟩ := S.gadj_fam_check3 Z hadj
      have hntop : ∀ c ∈ F0, c.2.2 + 1 + hs3 < ny := by
        intro c hc
        by_contra hle
        exact hT1 ⟨F0, hF0, hbot, c, hc, not_lt.1 hle⟩
      obtain ⟨b0, ms0, hb0F, hb0y, hgram, hblk, hpw, hend, hdist⟩ := S.bot_route3 hh hF0 hbot hntop hx0
      refine ⟨b0, ms0, S.badSet_sub_lat ny E (S.fam_sub_bad hF0 hb0F), hb0y, hgram, hdist, ?_, hpw, fun b hb => ?_⟩
      · have := hntop _ hend
        omega
      · obtain ⟨hbF, hby⟩ := hblk b hb
        have hnd : ¬ declared3 ny b := not_declared_of_inter ⟨hby, hntop b hbF⟩
        have hbB := S.fam_sub_bad hF0 hbF
        exact ⟨S.badSet_bad ny E b hbB hnd, hnd, S.badSet_sub_lat ny E hbB, F0, rfl, hF0, hbF⟩

/-- **The top part of a T2 skeleton**: to `b₂` (the block of the check next to it, in the boundary plane, not
counted) or into a top-strip family (its level-1 root, counted, and `top_route3`). -/
theorem top_part3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} (hT1 : ¬ S.T1ev3 ny E)
    {y : GNode3 T w h} {u1 : PVert3 T w h}
    (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y) (hadj : S.gadj3 Z ny E (.inl u1) y) :
    ∃ top : Top3, top.1 = blockOf3 u1 ∧
      (top.2.2 = false → top.2.1 = [] ∧ top.1.2.2 = (ny : ℤ) - 1) ∧
      (top.2.2 = true → route3.Gram 1 top.2.1 ∧ top.1 ∈ S.levSet (reach3 T w h r0) E ∧
        ∃ G, y = .inr (.inr G) ∧ G ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ top.1 ∈ G) ∧
      (ny : ℤ) ≤ (endOf top.1 top.2.1).2.2 + 1 + hs3 + Const.A1 ∧
      (top.2.2 = true → (top.1 :: blocksOf top.1 top.2.1).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
        ∀ b ∈ top.1 :: blocksOf top.1 top.2.1, S.bad E b ∧ ¬ declared3 ny b ∧ b ∈ latBlocks T w h ∧
          ∃ G, y = .inr (.inr G) ∧ G ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) ∧ b ∈ G) := by
  rcases hy with rfl | htf
  · rcases hadj with hg | hg
    · obtain ⟨t, x', rfl, -⟩ := hg
      have hy1 : (blockOf3 ((t, x', Fin.last h) : PVert3 T w h)).2.2 = (ny : ℤ) - 1 := by
        simp only [blockOf3, blockOf, PVert3.toV3, Fin.val_last]
        omega
      refine ⟨(blockOf3 ((t, x', Fin.last h) : PVert3 T w h), [], false), rfl, fun _ => ⟨rfl, hy1⟩,
        fun hc => absurd hc (by simp), ?_, fun hc => absurd hc (by simp)⟩
      simp only [endOf]
      rw [hy1]
      omega
    · simp [gadj0] at hg
  · rcases y with u0 | b | Ft
    · simp [topFam3] at htf
    · simp [topFam3] at htf
    · obtain ⟨hFt, htop⟩ := htf
      obtain ⟨-, he, heo⟩ := S.gadj_check_fam3 Z hadj
      have heL := S.lev_of_om3 heo
      have hnbot : ∀ c ∈ Ft, (hs3 : ℤ) < c.2.2 := by
        intro c hc
        by_contra hle
        exact hT1 ⟨Ft, hFt, ⟨c, hc, not_lt.1 hle⟩, htop⟩
      have hntop' : ∀ c ∈ Ft, c.2.2 + 1 + hs3 < ny → ¬ declared3 ny c := fun c hc hlt =>
        not_declared_of_inter ⟨hnbot c hc, hlt⟩
      obtain ⟨mst, hgram, hblk, hpw, hht⟩ := S.top_route3 hh hFt htop hnbot he
      refine ⟨(blockOf3 u1, mst, true), rfl, fun hc => absurd hc (by simp), fun _ => ⟨hgram, heL, Ft, rfl, hFt, he⟩,
        hht, fun _ => ⟨hpw, fun b hb => ?_⟩⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · have hnd := S.lev_not_declared3 hh heL
        have hbB := S.levSet_sub _ ny E heL
        exact ⟨S.badSet_bad ny E _ hbB hnd, hnd, S.badSet_sub_lat ny E hbB, Ft, rfl, hFt, he⟩
      · obtain ⟨hbF, hby⟩ := hblk b hb
        have hnd := hntop' b hbF hby
        have hbB := S.fam_sub_bad hFt hbF
        exact ⟨S.badSet_bad ny E b hbB hnd, hnd, S.badSet_sub_lat ny E hbB, Ft, rfl, hFt, hbF⟩

/-- The vertical projection of `c` on the plane `y = Y` is no farther in `ℓ1` than any block of that plane. -/
theorem l1_proj_le (c b : V3) (Y : ℤ) (hb : b.2.2 = Y) : l1 (((c.1, c.2.1, Y) : V3) - c) ≤ l1 (b - c) := by
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c
  simp only at hb
  subst hb
  simp only [l1, Prod.mk_sub_mk, sub_self, Int.natAbs_zero, zero_add]
  exact Nat.le_add_left _ _

/-- The uncounted top part at the vertical projection of `c` is valid after an exempt jump. -/
theorem tok3ex_proj (Y : ℤ) (c : V3) (hc : c.2.2 ≤ Y) : tok3ex Y c ((((c.1, c.2.1, Y) : V3), [], false) : Top3) := by
  unfold tok3ex
  rw [ite_eq_right Bool.false_ne_true]
  exact ⟨rfl, rfl, hc⟩

/-- The uncounted top part at the vertical projection of `c` is valid. -/
theorem tok3_proj (Y : ℤ) (c : V3) (hc : c.2.2 ≤ Y) : tok3 Y c ((((c.1, c.2.1, Y) : V3), [], false) : Top3) := by
  unfold tok3
  rw [ite_eq_right Bool.false_ne_true]
  exact ⟨rfl, rfl, hc⟩

set_option maxRecDepth 10000 in
/-- **T2 skeleton existence on the 3D code** (2D `t2SkelExistsOn`). For a solver with unit weights on the bulk
edges and weights in `[0, wh]` on the half-edges, every error in the T2 event without T1 has a valid 3D T2 skeleton
(end constant `67 + 2 wh / 35`) whose bottom block is a block of the lattice and whose counted blocks are bad blocks
of the lattice. -/
theorem t2SkelExistsOn3 {ny : ℕ} (hh : h + 1 = ny * 35) {wh : ℝ} (hwh0 : 0 ≤ wh)
    (hwt0 : ∀ e, 0 ≤ Z.wt e) (hunit : ∀ e, ¬ e.isHalf → Z.wt e = 1) (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh)
    {E : PEdge3 T w h → ZMod 2} (hT2 : S.T2ev3 Z ny E) (hT1 : ¬ S.T1ev3 ny E) :
    ∃ sk : T2Sk3, sk.OK ny (67 + 2 * wh / 35) ∧ sk.b0 ∈ latBlocks T w h ∧
      ∀ c ∈ sk.counted, S.bad E c ∧ c ∈ latBlocks T w h := by
  obtain ⟨l, x, y, hhd, hlst, hnd, hch, hx, hy, hbd, hint⟩ := hT2
  obtain ⟨m, p, u, v, hlen, hp, hp0, hpl, hfam, hnofam, hu, hv, -⟩ :=
    S.t2_stations3 Z hh hT1 hhd hlst hnd hch hx hy hbd hint
  obtain ⟨Fs, hFs⟩ := S.station_facts3 Z hhd hlst hnd hch hint hp hp0 hpl hfam hu hv hlen
  have hx0 : nd3 l (p 0) = x := by
    rw [hp0]
    exact nd3_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hyl : nd3 l (p (m + 1)) = y := by
    rw [hpl]
    exact nd3_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have hplt : ∀ i ≤ m + 1, p i < l.length := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | hi'
    · omega
    · have := hp i (m + 1) hi' le_rfl
      omega
  have hLF : S.levSet (reach3 T w h r0) E ⊆ S.badSet ny E := S.levSet_sub _ ny E
  -- the family skeletons
  have hKex : ∀ i, ∃ k : Skel3, 1 ≤ i → i ≤ m → k.1 = blockOf3 (u i) ∧ SkelOK k ∧
      dist3 (blockOf3 (v i)) (exitSk k) ≤ Const.D - 1 ∧
      (keyBlocks (blockOf3 (u i)) k.2.2).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      ∀ b ∈ keyBlocks (blockOf3 (u i)) k.2.2, b ∈ Fs i ∧ S.bad E b ∧ ¬ declared3 ny b := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ m
    · obtain ⟨-, hFm, hint', hu1, hou, hv1, hov⟩ := hFs i hi.1 hi.2
      obtain ⟨k, hk1, hok, hdist, hpw, -, hkb⟩ := S.inter_skel3 hh hFm hint' hu1 hv1 hou hov
      refine ⟨k, fun _ _ => ⟨hk1, hok, ?_, hpw, hkb⟩⟩
      unfold exitSk
      rw [hk1]
      exact hdist
    · exact ⟨((0, 0, 0), 0, ([], .inl [], [])), fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose K hK using hKex
  -- the bottom part
  have hadj0 : S.gadj3 Z ny E x (.inl (v 0)) := by
    have hg := chain_step hch (getElem?_nd3 (hplt 0 (by omega))) (getElem?_nd3 (show p 0 + 1 < l.length by omega))
    rw [hx0, hv 0 (Nat.zero_le _)] at hg
    exact hg
  obtain ⟨b0, ms0, hb0lat, hb0y, hgram0, hc0d, hc0y, hbpw, hbblk⟩ := S.bottom_part3 Z hh hT1 hx hadj0
  -- the top part
  have hadjt : S.gadj3 Z ny E (.inl (u (m + 1))) y := by
    have hg := chain_step hch (getElem?_nd3 (show p (m + 1) - 1 < l.length by omega))
      (by rw [show p (m + 1) - 1 + 1 = p (m + 1) by omega]; exact getElem?_nd3 (hplt (m + 1) le_rfl))
    rw [hu (m + 1) (by omega) le_rfl, hyl] at hg
    exact hg
  obtain ⟨top, htop1, htopF, htopT, hht, htopC⟩ := S.top_part3 Z hh hT1 hy hadjt
  -- separation of blocks at different stations
  have hsepst : ∀ i j, i ≤ m + 1 → j ≤ m + 1 → i ≠ j → ∀ G G' : Finset V3,
      nd3 l (p i) = .inr (.inr G) → nd3 l (p j) = .inr (.inr G') →
      G ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) →
      G' ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) →
      ∀ a ∈ G, ∀ b ∈ G', Const.D ≤ dist3 a b := by
    intro i j hi hj hij G G' hG hG' hGm hG'm a ha b hb
    exact sep_of_families hGm hG'm (station_fam_ne3 hnd hp hpl hlen hi hj hij hG hG') ha hb
  -- the uncounted top part is the vertical projection of the last cover
  obtain ⟨top', htop'⟩ : ∃ t : Top3, t = if top.2.2 = true then top else
      ((((covAt (endOf b0 ms0) K m).1, (covAt (endOf b0 ms0) K m).2.1, (ny : ℤ) - 1) : V3), [], false) := ⟨_, rfl⟩
  have htopT' : top.2.2 = true → top' = top := fun h => by rw [htop', if_pos h]
  have htopF' : top.2.2 = false → top' =
      ((((covAt (endOf b0 ms0) K m).1, (covAt (endOf b0 ms0) K m).2.1, (ny : ℤ) - 1) : V3), [], false) :=
    fun h => by rw [htop']; simp [h]
  have hcount : (⟨b0, ms0, (List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1))), top'⟩ : T2Sk3).counted =
      (⟨b0, ms0, (List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1))), top⟩ : T2Sk3).counted := by
    unfold T2Sk3.counted
    by_cases h : top.2.2 = true
    · rw [htopT' h]
    · have h' : top.2.2 = false := by simpa using h
      rw [htopF' h']
      simp [h']
  refine ⟨⟨b0, ms0, (List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1))), top'⟩,
    ⟨hb0y, hgram0, ?_, ?_, ?_, ?_, ?_⟩, hb0lat, ?_⟩
  · -- the tail
    refine tailOKex_range ((ny : ℤ) - 1) top' m (fun j => blockOf3 (u j)) K (endOf b0 ms0)
      (fun i hi => ⟨(hK (i + 1) (by omega) (by omega)).1, (hK (i + 1) (by omega) (by omega)).2.1⟩) ?_ ?_ ?_
    · intro i hi1 him
      obtain ⟨hni, hFmi, -, -, -, hv1, hov⟩ := hFs i hi1 (by omega)
      obtain ⟨hnj, hFmj, -, hu1, hou, -, -⟩ := hFs (i + 1) (by omega) (by omega)
      have hne : Fs i ≠ Fs (i + 1) := station_fam_ne3 hnd hp hpl hlen (by omega) (by omega) (by omega) hni hnj
      exact skel_landing (S.lev_of_om3 hov) (S.lev_of_om3 hou)
        (not_sameComp_of_fam_ne hLF hFmi hFmj hne hv1 hu1 (S.lev_of_om3 hov) (S.lev_of_om3 hou))
        (hK i hi1 (by omega)).2.2.1
    · intro hm0
      by_cases htf : top.2.2 = true
      · rw [htopT' htf]
        unfold tok3ex
        rw [if_pos htf]
        exact (htopT htf).1
      · have h' : top.2.2 = false := by simpa using htf
        obtain ⟨hmst, hety⟩ := htopF h'
        have hcL0 : covAt (endOf b0 ms0) K m = endOf b0 ms0 := by rw [hm0, covAt_zero]
        rw [htopF' h', hcL0]
        refine tok3ex_proj _ _ ?_
        omega
    · intro hm1
      obtain ⟨hnm, hFmm, hintm, -, -, hv1, hov⟩ := hFs m hm1 le_rfl
      by_cases htf : top.2.2 = true
      · rw [htopT' htf]
        unfold tok3
        rw [if_pos htf]
        obtain ⟨hg, heL, G, hyG, hGm, heG⟩ := htopT htf
        have hne : Fs m ≠ G :=
          station_fam_ne3 hnd hp hpl hlen (by omega) le_rfl (by omega) hnm (by rw [hyl, hyG])
        exact ⟨skel_landing (S.lev_of_om3 hov) heL
          (not_sameComp_of_fam_ne hLF hFmm hGm hne hv1 heG (S.lev_of_om3 hov) heL) (hK m hm1 le_rfl).2.2.1, hg⟩
      · have h' : top.2.2 = false := by simpa using htf
        obtain ⟨hmst, hety⟩ := htopF h'
        have hcLm : covAt (endOf b0 ms0) K m = exitSk (K m) := by
          obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
          exact covAt_succ _ _ _
        rw [htopF' h', hcLm]
        refine tok3_proj _ _ ?_
        have hd := (hK m hm1 le_rfl).2.2.1
        have hrow := row_le_dist3 (blockOf3 (v m)) (exitSk (K m))
        have hvm := (hintm _ hv1).2
        have hD : Const.D - 1 = 4 := by decide
        rw [hs3_val] at hvm
        omega
  · -- the height of the top part
    by_cases htf : top.2.2 = true
    · rw [htopT' htf]
      exact hht
    · have h' : top.2.2 = false := by simpa using htf
      rw [htopF' h']
      simp only [endOf]
      rw [hs3_val, Const.A1_val]
      omega
  · -- the metric constraint: the projected top jump is no longer than the jump to the block next to `b₂`
    have hrl : rlen top'.2.1 = rlen top.2.1 := by
      by_cases htf : top.2.2 = true
      · rw [htopT' htf]
      · have h' : top.2.2 = false := by simpa using htf
        rw [htopF' h', (htopF h').1]
    have hJle : (jsum3 (endOf b0 ms0) ((List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1)))) top'.1 : ℝ)
        ≤ (jsum3 (endOf b0 ms0) ((List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1)))) top.1 : ℝ) := by
      have hJa := jsum3_range top'.1 m (fun j => blockOf3 (u j)) K (endOf b0 ms0)
      have hJb := jsum3_range top.1 m (fun j => blockOf3 (u j)) K (endOf b0 ms0)
      have hlast : l1 (top'.1 - covAt (endOf b0 ms0) K m) ≤ l1 (top.1 - covAt (endOf b0 ms0) K m) := by
        by_cases htf : top.2.2 = true
        · rw [htopT' htf]
        · have h' : top.2.2 = false := by simpa using htf
          rw [htopF' h']
          exact l1_proj_le _ top.1 ((ny : ℤ) - 1) (htopF h').2
      rw [hJa, hJb]
      exact_mod_cast Nat.add_le_add_left hlast _
    rw [hrl]
    refine le_trans hJle ?_
    have hJ := jsum3_range top.1 m (fun j => blockOf3 (u j)) K (endOf b0 ms0)
    have hS := ssum3_range m (fun j => blockOf3 (u j)) K
    have hlenf : ((List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1)))).length = m := by simp
    have hms := S.metric_stations_block3 Z hwt0 (wmin := 1) (wmax := 1) zero_le_one zero_le_one hwh0
      (fun e he => (hunit e he).ge) (fun e he => (hunit e he).le) hwh hhd hlst hnd hch hx hy hbd m p u v hp hp0
      hpl hfam hnofam hu hv
    simp only [blockL1_3, one_mul] at hms
    have hmet : (35 : ℝ) * ∑ i ∈ range (m + 1), (l1 (blockOf3 (v i) - blockOf3 (u (i + 1))) : ℝ) ≤
        (35 : ℝ) * ∑ i ∈ range m, (l1 (blockOf3 (u (i + 1)) - blockOf3 (v (i + 1))) : ℝ) +
          ((m + 1 : ℝ) + m) * 102 + (((v 0).2.2.val : ℝ) + ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) + 2 * wh) := by
      have e102 : ((3 * 34 : ℕ) : ℝ) = 102 := by norm_num
      rw [e102] at hms
      linarith
    have hC : ∀ i ≤ m, dist3 (blockOf3 (v i)) (covAt (endOf b0 ms0) K i) ≤ Const.D - 1 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [covAt_zero]
        exact hc0d
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [covAt_succ]
        exact (hK (j + 1) (by omega) hi).2.2.1
    have hconv := metric_convert3 m (fun j => blockOf3 (u j)) (fun j => blockOf3 (v j))
      (covAt (endOf b0 ms0) K) hC _ hmet
    -- the jumps and spans of the skeleton
    have hJ' : (jsum3 (endOf b0 ms0) ((List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1)))) top.1 : ℝ)
        = ∑ i ∈ range (m + 1), (l1 (blockOf3 (u (i + 1)) - covAt (endOf b0 ms0) K i) : ℝ) := by
      rw [hJ, Finset.sum_range_succ, htop1]
      push_cast
      rfl
    have hS' : (ssum3 ((List.range m).map (fun i => (blockOf3 (u (i + 1)), K (i + 1)))) : ℝ) =
        ∑ i ∈ range m, (l1 (covAt (endOf b0 ms0) K (i + 1) - blockOf3 (u (i + 1))) : ℝ) := by
      rw [hS]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [covAt_succ]
    -- the legs
    have hlegs : (v 0).2.2.val + (h - (u (m + 1)).2.2.val) ≤ 35 * (rlen ms0 + rlen top.2.1) + 1818 := by
      have hX0 : (blockOf3 (v 0)).2.2 = ((v 0).2.2.val : ℤ) / 35 := rfl
      have hX0c := row_le_dist3 (endOf b0 ms0) (blockOf3 (v 0))
      rw [dist3_comm] at hX0c
      have hc0b := endOf_row_le b0 ms0
      have het : top.1.2.2 = ((u (m + 1)).2.2.val : ℤ) / 35 := by
        rw [htop1]
        rfl
      have hte := endOf_row_le top.1 top.2.1
      have hu1 := (u (m + 1)).2.2.isLt
      have hD : Const.D - 1 = 4 := by decide
      rw [hs3_val, Const.A1_val] at hht
      rw [hs3_val] at hb0y
      omega
    have hlegsR : ((v 0).2.2.val : ℝ) + ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) ≤
        35 * ((rlen ms0 : ℝ) + rlen top.2.1) + 1818 := by
      exact_mod_cast hlegs
    rw [hJ', hS', hlenf]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · -- counted blocks are undeclared
    rw [hcount]
    intro b hb
    unfold T2Sk3.counted at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact (hbblk b hb).2.1
    · rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        have hi' := List.mem_range.1 hi
        exact ((hK (i + 1) (by omega) (by omega)).2.2.2.2 b hbf).2.2
      · split_ifs at hb with htf
        · exact ((htopC htf).2 b hb).2.1
        · simp at hb
  · -- counted blocks are pairwise separated
    rw [hcount]
    unfold T2Sk3.counted
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨hbpw, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.pairwise_flatMap]
      refine ⟨fun f hf => ?_, ?_⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        have hi' := List.mem_range.1 hi
        exact (hK (i + 1) (by omega) (by omega)).2.2.2.1
      · rw [List.pairwise_map]
        refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij a ha b hb => ?_
        have hi' := List.mem_range.1 hi
        have hj' := List.mem_range.1 hj
        obtain ⟨hni, hFmi, -⟩ := hFs (i + 1) (by omega) (by omega)
        obtain ⟨hnj, hFmj, -⟩ := hFs (j + 1) (by omega) (by omega)
        exact hsepst (i + 1) (j + 1) (by omega) (by omega) (by omega) _ _ hni hnj hFmi hFmj a
          ((hK (i + 1) (by omega) (by omega)).2.2.2.2 a ha).1 b ((hK (j + 1) (by omega) (by omega)).2.2.2.2 b hb).1
    · split_ifs with htf
      · exact (htopC htf).1
      · exact List.Pairwise.nil
    · intro a ha b hb
      obtain ⟨f, hf, haf⟩ := List.mem_flatMap.1 ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
      have hi' := List.mem_range.1 hi
      split_ifs at hb with htf
      · obtain ⟨-, -, -, G, hyG, hGm, hbG⟩ := (htopC htf).2 b hb
        obtain ⟨hni, hFmi, -⟩ := hFs (i + 1) (by omega) (by omega)
        exact hsepst (i + 1) (m + 1) (by omega) le_rfl (by omega) _ _ hni (by rw [hyl, hyG]) hFmi hGm a
          ((hK (i + 1) (by omega) (by omega)).2.2.2.2 a haf).1 b hbG
      · simp at hb
    · intro a ha b hb
      obtain ⟨-, -, -, G0, hxG0, hG0m, haG0⟩ := hbblk a ha
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        have hi' := List.mem_range.1 hi
        obtain ⟨hni, hFmi, -⟩ := hFs (i + 1) (by omega) (by omega)
        exact hsepst 0 (i + 1) (by omega) (by omega) (by omega) _ _ (by rw [hx0, hxG0]) hni hG0m hFmi a haG0 b
          ((hK (i + 1) (by omega) (by omega)).2.2.2.2 b hbf).1
      · split_ifs at hb with htf
        · obtain ⟨-, -, -, G, hyG, hGm, hbG⟩ := (htopC htf).2 b hb
          exact hsepst 0 (m + 1) (by omega) le_rfl (by omega) _ _ (by rw [hx0, hxG0]) (by rw [hyl, hyG]) hG0m hGm
            a haG0 b hbG
        · simp at hb
  · -- counted blocks are bad blocks of the lattice
    rw [hcount]
    intro c hc
    unfold T2Sk3.counted at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact ⟨(hbblk c hc).1, (hbblk c hc).2.2.1⟩
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨f, hf, hcf⟩ := List.mem_flatMap.1 hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
        have hi' := List.mem_range.1 hi
        obtain ⟨-, hFmi, -⟩ := hFs (i + 1) (by omega) (by omega)
        obtain ⟨hcF, hcb, -⟩ := (hK (i + 1) (by omega) (by omega)).2.2.2.2 c hcf
        exact ⟨hcb, S.badSet_sub_lat ny E (S.fam_sub_bad hFmi hcF)⟩
      · split_ifs at hc with htf
        · exact ⟨((htopC htf).2 c hc).1, ((htopC htf).2 c hc).2.2.1⟩
        · simp at hc

end Stage13

end QECD1
