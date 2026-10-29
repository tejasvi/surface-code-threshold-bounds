import QECD1.T2Final3
import QECD1.Route1

/-!
# The 3D T1 route (existence)

The 3D analogue of the 2D `TwoD/RouteExist` `t1RouteExistsOn`. A T1 family (a family with a block in each strip)
contains a route word from `A` from its last bottom-strip block, stopped before the first top-strip block, whose
counted blocks lie in the family strictly between the strips and are pairwise `D`-separated (`t1_route3`): from a
shortest cluster chain from the bottom strip to the top strip, the path in the first cluster cut at its last
bottom-strip block, the route of the middle clusters (`fchain_route3`), and the path in the last cluster cut before the
top strip (`final_cut3`).
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

namespace Stage13

variable (S : Stage13 T w h)

set_option maxRecDepth 10000 in
/-- **The T1 route**: in a family with a block in each strip, a route word from `A` from its last bottom-strip block
`b0` (not counted), stopped before the top strip; its counted blocks lie in the family strictly between the strips and
are pairwise `D`-separated, and it ends within `A1 + h_s + 1` rows of the top. -/
theorem t1_route3 {ny : ℕ} (hh : h + 1 = ny * 35) {E : PEdge3 T w h → ZMod 2} {Fm : Finset V3}
    (hFm : Fm ∈ families3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E))
    (hbot : ∃ c ∈ Fm, c.2.2 ≤ hs3) (htop : ∃ c ∈ Fm, (ny : ℤ) ≤ c.2.2 + 1 + hs3) :
    ∃ (b0 : V3) (ms : List Tok), b0 ∈ Fm ∧ b0.2.2 ≤ hs3 ∧ route3.Gram 1 ms ∧
      (∀ b ∈ blocksOf b0 ms, b ∈ Fm ∧ (hs3 : ℤ) < b.2.2 ∧ b.2.2 + 1 + hs3 < ny) ∧
      (blocksOf b0 ms).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      (ny : ℤ) ≤ (endOf b0 ms).2.2 + 1 + hs3 + Const.A1 := by
  have hLF : S.levSet (reach3 T w h r0) E ⊆ S.badSet ny E := S.levSet_sub _ ny E
  have hA0 : Const.D - 1 + Const.a1 = Const.A1 := by decide
  have hDA : Const.D - 1 ≤ Const.A1 := by decide
  obtain ⟨c1, hc1, hr1⟩ := hbot
  obtain ⟨c2, hc2, hr2⟩ := htop
  obtain ⟨c0, -, hc0⟩ := mem_families3.1 hFm
  have hFmF : Fm ⊆ S.badSet ny E := by
    rw [← hc0]
    exact famF_sub _ _ _
  have hinfam : InFamily3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) c1 c2 := by
    have hc2' := hc2
    rw [← famF_eq_of_mem_families3 hFm hc1] at hc2'
    exact (mem_famF.1 hc2').2
  obtain ⟨n0, f0, hf0⟩ := exists_fchain3 _ _ hLF (hFmF hc1) hinfam
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, hnost, hnoen⟩ :=
    exists_min_gchain3 (F := S.badSet ny E) (L := S.levSet (reach3 T w h r0) E)
      (Pst := fun c => c ∈ Fm ∧ c.2.2 ≤ hs3) (Pen := fun c => (ny : ℤ) ≤ c.2.2 + 1 + hs3)
      ⟨n0, f0, hf0.1, hf0.2.1, ⟨by rw [hf0.2.2.1]; exact hc1, by rw [hf0.2.2.1]; exact hr1⟩,
        by show (ny : ℤ) ≤ (f0 n0).2.2.2 + 1 + hs3; rw [hf0.2.2.2]; exact hr2⟩
  obtain ⟨h0F, h0r⟩ : (f 0).1 ∈ Fm ∧ (f 0).1.2.2 ≤ hs3 := h0
  have hn' : (ny : ℤ) ≤ (f n).2.2.2 + 1 + hs3 := hn
  have hfam : ∀ i ≤ n, ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, c ∈ Fm := by
    intro i hi c hc
    have hinf := gchain_family3 hLF hP hL i hi c hc
    rw [← famF_eq_of_mem_families3 hFm h0F]
    exact mem_famF.2 ⟨(mem_clusterOf.1 hc).1, hinf⟩
  have habove : ∀ i, 1 ≤ i → i ≤ n → ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, (hs3 : ℤ) < c.2.2 := by
    intro i hi1 hin c hc
    by_contra hle
    exact hnost i hi1 hin c hc ⟨hfam i hin c hc, not_lt.1 hle⟩
  have hbelow : ∀ i, i < n → ∀ c ∈ clusterOf (S.badSet ny E) (f i).1, c.2.2 + 1 + hs3 < ny :=
    fun i hin c hc => not_le.1 (hnoen i hin c hc)
  have hcl : ∀ i ≤ n, (f i).1 ∈ clusterOf (S.badSet ny E) (f i).1 := fun i hi =>
    self_mem_clusterOf (hP i hi).1
  have hpath : ∀ i ≤ n, ∃ (Sel : Finset V3) (rest : List V3),
      IsSelection3 (clusterOf (S.badSet ny E) (f i).1) Sel (f i).1 Const.D Const.A0 ∧ ((f i).1 :: rest).Nodup ∧
      List.IsChain (selGraph Sel Const.A0).Adj ((f i).1 :: rest) ∧
      dist3 (f i).2 (((f i).1 :: rest).getLast (List.cons_ne_nil _ _)) ≤ Const.D - 1 := by
    intro i hi
    obtain ⟨hrF, hxF, hrx⟩ := hP i hi
    obtain ⟨Sel, rest, hS, -, hnd, hch, hxs⟩ := cluster_path3 hrF (mem_clusterOf.2 ⟨hxF, hrx⟩)
    exact ⟨Sel, rest, hS, hnd, hch, hxs⟩
  -- the first cluster: its path cut at its last bottom-strip block
  obtain ⟨Sel0, rest0, hS0, hnd0, hch0, hxs0⟩ := hpath 0 (Nat.zero_le _)
  have hmem0 : ∀ b ∈ (f 0).1 :: rest0, b ∈ Sel0 := path_mem_sel _ _ hS0.2.1 hch0
  have hK0 : ∀ b ∈ (f 0).1 :: rest0, b ∈ clusterOf (S.badSet ny E) (f 0).1 := fun b hb => hS0.1 (hmem0 b hb)
  obtain ⟨pre, b, suf, hsplit, hb, hsuf⟩ := exists_last_split3 (fun c : V3 => c.2.2 ≤ hs3) (f 0).1 rest0 h0r
  have hbmem : b ∈ (f 0).1 :: rest0 := by rw [hsplit]; simp
  have hsufmem : ∀ c ∈ suf, c ∈ (f 0).1 :: rest0 := fun c hc => by rw [hsplit]; simp [hc]
  have hchb : List.IsChain (selGraph Sel0 Const.A0).Adj (b :: suf) := by
    rw [hsplit] at hch0
    exact hch0.right_of_append
  have hndb : (b :: suf).Nodup := by
    rw [hsplit] at hnd0
    exact (List.nodup_append.1 hnd0).2.1
  have hlastb := getLast_split3 hsplit
  have hgram1 : route3.Gram 1 (pathToks b suf) := pathToks_gram hS0 1 le_rfl b suf hchb
  have hbFm : b ∈ Fm := hfam 0 (Nat.zero_le _) b (hK0 b hbmem)
  have hsufabove : ∀ c ∈ suf, (hs3 : ℤ) < c.2.2 := fun c hc => not_le.1 (hsuf c hc)
  have hsK : (b :: suf).getLast (List.cons_ne_nil _ _) ∈ clusterOf (S.badSet ny E) (f 0).1 := by
    rw [← hlastb]
    exact hK0 _ (List.getLast_mem _)
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: steps from `b`, cut before the top strip
    subst hn0
    have hend : (ny : ℤ) ≤ ((b :: suf).getLast (List.cons_ne_nil _ _)).2.2 + 1 + hs3 + Const.A1 := by
      have h1 := row_le_dist3 ((b :: suf).getLast (List.cons_ne_nil _ _)) (f 0).2
      rw [dist3_comm, ← hlastb] at h1
      rw [← hlastb]
      have h2 := hxs0
      omega
    obtain ⟨l1, l2, hsp, hch1, hbl1, hhl1⟩ := final_cut3 b suf hchb hend
    have hl1suf : ∀ c ∈ l1, c ∈ suf := fun c hc => by rw [hsp]; exact List.mem_append_left _ hc
    have hl1nd : l1.Nodup := by
      have := (List.nodup_cons.1 hndb).2
      rw [hsp] at this
      exact (List.nodup_append.1 this).1
    refine ⟨b, pathToks b l1, hbFm, hb, pathToks_gram hS0 1 le_rfl b l1 hch1, ?_, ?_, ?_⟩
    · rw [pathToks_blocks]
      intro c hc
      exact ⟨hfam 0 le_rfl c (hK0 c (hsufmem c (hl1suf c hc))), hsufabove c (hl1suf c hc), hbl1 c hc⟩
    · rw [pathToks_blocks]
      exact sel_pairwise hl1nd (fun c hc => hmem0 c (hsufmem c (hl1suf c hc))) hS0.2.2.1
    · rw [pathToks_end]
      exact hhl1
  -- several clusters: the prefix through the clusters before the last
  have hsufpw : suf.Pairwise (fun a b => Const.D ≤ dist3 a b) :=
    sel_pairwise (List.nodup_cons.1 hndb).2 (fun c hc => hmem0 c (hsufmem c hc)) hS0.2.2.1
  have hpre : ∃ wp : List Tok, route3.Gram 1 wp ∧ 1 ≤ route3.stAfter 1 wp ∧
      (∀ c ∈ blocksOf b wp, (∃ i, i < n ∧ c ∈ clusterOf (S.badSet ny E) (f i).1) ∧ (hs3 : ℤ) < c.2.2) ∧
      (blocksOf b wp).Pairwise (fun a b => Const.D ≤ dist3 a b) ∧
      endOf b wp ∈ clusterOf (S.badSet ny E) (f (n - 1)).1 ∧
      dist3 (f (n - 1)).2 (endOf b wp) ≤ Const.D - 1 := by
    have hxs0' : dist3 (f 0).2 ((b :: suf).getLast (List.cons_ne_nil _ _)) ≤ Const.D - 1 := by
      rw [← hlastb]
      exact hxs0
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · have hn1' : n = 1 := by omega
      subst hn1'
      refine ⟨pathToks b suf, hgram1, by rw [stAfter_pathToks_one], ?_, ?_, ?_, ?_⟩
      · rw [pathToks_blocks]
        intro c hc
        exact ⟨⟨0, Nat.one_pos, hK0 c (hsufmem c hc)⟩, hsufabove c hc⟩
      · rw [pathToks_blocks]
        exact hsufpw
      · rw [pathToks_end]
        exact hsK
      · rw [pathToks_end]
        exact hxs0'
    · have hgch : FChain3 (S.badSet ny E) (S.levSet (reach3 T w h r0) E) (f 1).1 (f (n - 1)).2 (n - 2)
          (fun i => f (i + 1)) :=
        ⟨fun i hi => hP (i + 1) (by omega), fun i hi => hL (i + 1) (by omega), rfl,
          by show (f (n - 2 + 1)).2 = (f (n - 1)).2; rw [show n - 2 + 1 = n - 1 by omega]⟩
      have hgdist : ∀ i j, i < j → j ≤ n - 2 →
          ¬ SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 (f (j + 1)).1 :=
        fun i j hij hj => hdist (i + 1) (j + 1) (by omega) (by omega)
      have hgW0 : ∀ i ≤ n - 2, ∃ c, SameComp (S.badSet ny E) Const.a0 (f (i + 1)).1 c ∧
          Const.D ≤ dist3 (f (i + 1)).1 c := by
        intro i hi
        refine S.w0_dec3 hh (hL i (by omega)).2.1 fun c hc => not_declared_of_inter ⟨?_, ?_⟩
        · exact habove (i + 1) (by omega) (by omega) c hc
        · exact hbelow (i + 1) (by omega) c hc
      obtain ⟨ws, hwsg, hwsst, hwspw, hwsK, hwsend, hwsx⟩ := fchain_route3 hgch hgdist hgW0
      have hl01 : dist3 (f 0).2 (f 1).1 ≤ Const.a1 := (hL 0 (by omega)).2.2
      have hcl1 : (f 1).1 ∈ clusterOf (S.badSet ny E) (f 1).1 := hcl 1 (by omega)
      have hd01 : ¬ SameComp (S.badSet ny E) Const.a0 (f 0).1 (f 1).1 := hdist 0 1 (by omega) (by omega)
      have hlink := link_of_clusters hsK hcl1 hd01 hxs0' hl01
      obtain ⟨hg, hblk, hend⟩ := steps_link_chain b (f 1).1 suf ws hgram1 hlink hwsg
      refine ⟨pathToks b suf ++ Tok.link ((f 1).1 - (b :: suf).getLast (List.cons_ne_nil _ _)) :: ws, hg,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [WA.stAfter_append, stAfter_pathToks_one]
        exact hwsst
      · rw [hblk]
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact ⟨⟨0, by omega, hK0 c (hsufmem c hc)⟩, hsufabove c hc⟩
        · obtain ⟨i, hi, hci⟩ := hwsK c hc
          exact ⟨⟨i + 1, by omega, hci⟩, habove (i + 1) (by omega) (by omega) c hci⟩
      · rw [hblk, List.pairwise_append]
        refine ⟨hsufpw, hwspw, fun c hc d hd => ?_⟩
        obtain ⟨i, hi, hdi⟩ := hwsK d hd
        exact sep_of_clusters (hK0 c (hsufmem c hc)) hdi (hdist 0 (i + 1) (by omega) (by omega))
      · rw [hend]
        have := hwsend
        rw [show n - 2 + 1 = n - 1 by omega] at this
        exact this
      · rw [hend]
        exact hwsx
  obtain ⟨wp, hwpg, hwpst, hwpK, hwppw, hwpend, hwpx⟩ := hpre
  have hwpok : ∀ c ∈ blocksOf b wp, c ∈ Fm ∧ (hs3 : ℤ) < c.2.2 ∧ c.2.2 + 1 + hs3 < ny := by
    intro c hc
    obtain ⟨⟨i, hi, hci⟩, hca⟩ := hwpK c hc
    exact ⟨hfam i hi.le c hci, hca, hbelow i hi c hci⟩
  have hlinkn : dist3 (f (n - 1)).2 (f n).1 ≤ Const.a1 := by
    have := (hL (n - 1) (by omega)).2.2
    rw [show n - 1 + 1 = n by omega] at this
    exact this
  by_cases hrtop : (ny : ℤ) ≤ (f n).1.2.2 + 1 + hs3
  · -- the root of the last cluster is in the top strip: the prefix is the route
    refine ⟨b, wp, hbFm, hb, hwpg, hwpok, hwppw, ?_⟩
    have h1 := row_le_dist3 (endOf b wp) (f n).1
    have h2 := dist3_triangle (endOf b wp) (f (n - 1)).2 (f n).1
    rw [dist3_comm] at hwpx
    omega
  · -- a link into the last cluster, then its path cut before the top strip
    obtain ⟨Seln, restn, hSn, hndn, hchn, hxsn⟩ := hpath n le_rfl
    have hendn : (ny : ℤ) ≤ (((f n).1 :: restn).getLast (List.cons_ne_nil _ _)).2.2 + 1 + hs3 + Const.A1 := by
      have h1 := row_le_dist3 (((f n).1 :: restn).getLast (List.cons_ne_nil _ _)) (f n).2
      rw [dist3_comm] at h1
      omega
    obtain ⟨l1, l2, hsplitn, hchl1, hbl1, hhl1⟩ := final_cut3 (f n).1 restn hchn hendn
    have hmemn : ∀ c ∈ (f n).1 :: restn, c ∈ Seln := path_mem_sel _ _ hSn.2.1 hchn
    have hl1sub : ∀ c ∈ (f n).1 :: l1, c ∈ (f n).1 :: restn := by
      intro c hc
      rw [hsplitn]
      rcases List.mem_cons.1 hc with rfl | hc
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hc)
    have hl1nd : ((f n).1 :: l1).Nodup := by
      rw [hsplitn, ← List.cons_append] at hndn
      exact (List.nodup_append.1 hndn).1
    have hl1pw : ((f n).1 :: l1).Pairwise (fun a b => Const.D ≤ dist3 a b) :=
      sel_pairwise hl1nd (fun c hc => hmemn c (hl1sub c hc)) hSn.2.2.1
    have hl1K : ∀ c ∈ (f n).1 :: l1, c ∈ clusterOf (S.badSet ny E) (f n).1 := fun c hc =>
      hSn.1 (hmemn c (hl1sub c hc))
    have hlink := link_of_clusters hwpend (hcl n le_rfl) (hdist (n - 1) n (by omega) le_rfl) hwpx hlinkn
    have hgl : route3.Gram 0 (pathToks (f n).1 l1) := pathToks_gram hSn 0 (Nat.zero_le _) _ l1 hchl1
    refine ⟨b, wp ++ Tok.link ((f n).1 - endOf b wp) :: pathToks (f n).1 l1, hbFm, hb, ?_, ?_, ?_, ?_⟩
    · rw [WA.gram_append]
      exact ⟨hwpg, gram_link _ hwpst _ hlink _ hgl⟩
    · rw [blocksOf_append, blocksOf_link, add_sub_cancel, pathToks_blocks]
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hwpok c hc
      · rcases List.mem_cons.1 hc with rfl | hc
        · exact ⟨hfam n le_rfl _ (hcl n le_rfl), habove n hn0 le_rfl _ (hcl n le_rfl), not_le.1 hrtop⟩
        · exact ⟨hfam n le_rfl c (hl1K c (List.mem_cons_of_mem _ hc)),
            habove n hn0 le_rfl c (hl1K c (List.mem_cons_of_mem _ hc)), hbl1 c hc⟩
    · rw [blocksOf_append, blocksOf_link, add_sub_cancel, pathToks_blocks, List.pairwise_append]
      refine ⟨hwppw, hl1pw, fun c hc d hd => ?_⟩
      obtain ⟨⟨i, hi, hci⟩, -⟩ := hwpK c hc
      exact sep_of_clusters hci (hl1K d hd) (hdist i n hi le_rfl)
    · rw [endOf_append, endOf_link, add_sub_cancel, pathToks_end]
      exact hhl1

end Stage13

end QECD1
