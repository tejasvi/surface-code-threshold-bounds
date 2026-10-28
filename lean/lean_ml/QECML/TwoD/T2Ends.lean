import QECML.TwoD.T2Skel

/-!
# T2 end routes (bottom end and top end)

On the T2 sub-path, `F_0` is the last bottom-strip family and `F_{m+1}` the first top-strip family after it. Without
T1, `F_0` has no block in the top strip and `F_{m+1}` none in the bottom strip.

* `bot_route`: a route in `F_0` from its last bottom-strip block `b` (not counted) to the selected block `σ` covering a
  given block `x0` of `F_0` (the block of the exit check `v_0`): in-cluster steps, links, and a leaf after every link
  into a cluster whose route part is the root alone; all counted blocks lie strictly between the strips.
* `top_route`: a route in `F_{m+1}` from the level-1 root `e` (the block of the entry check `u_{m+1}`), stopped before
  the first block in the top strip, so its end is within `A1 + h_s + 1` rows of the top; the route is empty if `e`
  itself lies in the top strip (then `e` is not counted).
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- Without T1, a family with a block in the bottom strip has no block in the top strip. -/
theorem family_below_top {a0 a1 : ℕ} {E : G.Ed → ZMod 2} (hT1 : ¬ S.T1 a0 a1 E) {c c1 c' : G.Block}
    (hc : S.badD E c) (h1 : c1 ∈ S.family a0 a1 E c) (hr1 : c1.2.val ≤ hs a1) (h' : c' ∈ S.family a0 a1 E c) :
    c'.2.val + 1 + hs a1 < G.ny := by
  by_contra h
  exact hT1 ⟨c, hc, ⟨c1, h1, hr1⟩, ⟨c', h', by omega⟩⟩

/-- Without T1, a family with a block in the top strip has no block in the bottom strip. -/
theorem family_above_bot {a0 a1 : ℕ} {E : G.Ed → ZMod 2} (hT1 : ¬ S.T1 a0 a1 E) {c c2 c' : G.Block}
    (hc : S.badD E c) (h2 : c2 ∈ S.family a0 a1 E c) (hr2 : G.ny ≤ c2.2.val + 1 + hs a1)
    (h' : c' ∈ S.family a0 a1 E c) : hs a1 < c'.2.val := by
  by_contra h
  exact hT1 ⟨c, hc, ⟨c', h', by omega⟩, ⟨c2, h2, hr2⟩⟩

/-- **The bottom end route** (F4): in a family with a block in the bottom strip, without T1, from the last
bottom-strip block `b` of a route (not counted) to the selected block `σ` covering a given block `x0` of the family. -/
theorem bot_route {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1)
    {E : G.Ed → ZMod 2} (hT1 : ¬ S.T1 a0 a1 E) {c1 x0 : G.Block} (hc1 : S.badD E c1) (hrow1 : c1.2.val ≤ hs a1)
    (hx0 : x0 ∈ S.family a0 a1 E c1) :
    ∃ (b σ : G.Block) (ms : List G.Move), b.2.val ≤ hs a1 ∧ b ∈ S.family a0 a1 E c1 ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) b ms ∧
      (∀ m ∈ ms.head?, ¬ m.isLeaf) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, m.blk ∈ S.family a0 a1 E c1) ∧ S3Geom.endBlock b ms = σ ∧ σ ∈ S.family a0 a1 E c1 ∧
      G.blockDist x0 σ ≤ G.D - 1 := by
  have hftop : ∀ c ∈ S.family a0 a1 E c1, c.2.val + 1 + hs a1 < G.ny := fun c hc =>
    S.family_below_top hT1 hc1 (S.mem_family_self hc1) hrow1 hc
  obtain ⟨n0, f0, hP0, hL0, h00, hn0⟩ := S.exists_partial_chain hc1 x0 hx0.2
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, hbot, -⟩ :=
    S.exists_min_gchain (a0 := a0) (a1 := a1) (E := E)
      (Pst := fun c : G.Block => c.2.val ≤ hs a1 ∧ c ∈ S.family a0 a1 E c1) (Pen := fun c : G.Block => c = x0)
      ⟨n0, f0, hP0, hL0, by rw [h00]; exact ⟨hrow1, S.mem_family_self hc1⟩, hn0⟩
  obtain ⟨h0r, h0F⟩ : (f 0).1.2.val ≤ hs a1 ∧ (f 0).1 ∈ S.family a0 a1 E c1 := h0
  have hn' : (f n).2 = x0 := hn
  have hFeq : S.family a0 a1 E (f 0).1 = S.family a0 a1 E c1 := S.family_eq_of_mem h0F
  have hfam : ∀ i ≤ n, ∀ c ∈ S.cluster E a0 (f i).1, c ∈ S.family a0 a1 E c1 := by
    intro i hi c hc
    rw [← hFeq]
    exact S.fchain_family (hP 0 (Nat.zero_le _)).1 (x := (f n).2) ⟨hP, hL, rfl, rfl⟩ i hi c hc
  have heK0 : (f 0).1 ∈ S.cluster E a0 (f 0).1 := S.mem_cluster_self (hP 0 (Nat.zero_le _)).1
  have hxK0 : (f 0).2 ∈ S.cluster E a0 (f 0).1 := by
    rw [(hP 0 (Nat.zero_le _)).2.2]
    exact S.mem_cluster_self (hP 0 (Nat.zero_le _)).2.1
  -- the first cluster: a selection rooted at its entry and a simple path to the cover of its exit
  obtain ⟨Sel0, rest0, s0, hSK0, hsep0, hmem0, hnd0, hch0, hlast0, hxs0⟩ :
      ∃ (Sel : Finset G.Block) (rest : List G.Block) (s : G.Block),
        (∀ b ∈ Sel, b ∈ S.cluster E a0 (f 0).1) ∧ (∀ b ∈ Sel, ∀ b' ∈ Sel, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        (∀ b ∈ (f 0).1 :: rest, b ∈ Sel) ∧ ((f 0).1 :: rest).Nodup ∧
        List.IsChain (fun x y => x ≠ y ∧ G.blockDist x y ≤ G.D - 1 + a0) ((f 0).1 :: rest) ∧
        ((f 0).1 :: rest).getLast? = some s ∧ G.blockDist (f 0).2 s ≤ G.D - 1 := by
    have hconnK : ∀ x ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f 0).1), Relation.ReflTransGen
        (fun x y => x ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f 0).1) ∧
          y ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f 0).1) ∧ G.blockDist x y ≤ a0) (f 0).1 x := by
      intro x hx
      have h := S3Geom.comp_chain (B := {c | S.badD E c}) (a := a0) (hP 0 (Nat.zero_le _)).1 (f 0).1 heK0 x
        (Finset.mem_filter.1 hx).2
      clear hx
      induction h with
      | refl => exact .refl
      | tail _ huv ih =>
        exact ih.tail ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.1⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.2.1⟩, huv.2.2⟩
    obtain ⟨Sel, ⟨hSK, hrS, hsep, hconn⟩, hcov⟩ := S3Geom.exists_selection (a := a0) hD1
      (K := Finset.univ.filter (· ∈ S.cluster E a0 (f 0).1)) (r := (f 0).1) (by simpa using heK0) hconnK
    obtain ⟨s, hsS, hxs⟩ := hcov (f 0).2 (by simpa using hxK0)
    obtain ⟨l, hhead, hlast, hnd, hmem, hch⟩ := S3Geom.exists_simple_path hrS (hconn s hsS)
    cases l with
    | nil => simp at hhead
    | cons e rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact ⟨Sel, rest, s, fun b hb => by simpa using hSK hb, hsep, hmem, hnd, hch, hlast, hxs⟩
  have hpath0 : List.IsChain (fun x y => G.D ≤ G.blockDist x y ∧ G.blockDist x y ≤ G.D - 1 + a0)
      ((f 0).1 :: rest0) :=
    hch0.imp_of_mem_imp fun x y hx hy hxy => ⟨hsep0 x (hmem0 x hx) y (hmem0 y hy) hxy.1, hxy.2⟩
  have hpw0 : ((f 0).1 :: rest0).Pairwise (fun b b' => G.D ≤ G.blockDist b b') :=
    List.Pairwise.imp_of_mem (fun hx hy hxy => hsep0 _ (hmem0 _ hx) _ (hmem0 _ hy) hxy) hnd0
  have hpK0 : ∀ b ∈ (f 0).1 :: rest0, b ∈ S.cluster E a0 (f 0).1 := fun b hb => hSK0 b (hmem0 b hb)
  have hs0K : s0 ∈ S.cluster E a0 (f 0).1 := hpK0 s0 (List.mem_of_getLast? hlast0)
  -- cut the first path at its last bottom-strip block
  obtain ⟨pre, b, suf, hsplit, hb, hsuf⟩ :=
    S3Geom.exists_last_split (fun c : G.Block => c.2.val ≤ hs a1) (f 0).1 rest0 h0r
  rw [hsplit] at hpath0 hpw0 hpK0 hlast0
  rw [S3Geom.getLast?_append_cons] at hlast0
  have hpw' := (List.pairwise_append.1 hpw0).2.1
  rw [List.pairwise_cons] at hpw'
  have hbK : b ∈ S.cluster E a0 (f 0).1 := hpK0 b (List.mem_append_right pre List.mem_cons_self)
  have hsufK : ∀ c ∈ suf, c ∈ S.cluster E a0 (f 0).1 :=
    fun c hc => hpK0 c (List.mem_append_right pre (List.mem_cons_of_mem b hc))
  have hsufrow : ∀ c ∈ suf, hs a1 + 1 ≤ c.2.val ∧ c.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E c := fun c hc => by
    have h1 : ¬ c.2.val ≤ hs a1 := hsuf c hc
    have h2 := hftop c (hfam 0 (Nat.zero_le _) c (hsufK c hc))
    exact ⟨by omega, by omega, S3Geom.comp_subset (hsufK c hc)⟩
  have hF1 : S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) b (suf.map S3Geom.Move.step) :=
    S3Geom.Frag.steps b suf hpath0.right_of_append hsufrow hpw'.2
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: steps from `b` to the cover of `x0`
    subst hn0
    refine ⟨b, s0, suf.map S3Geom.Move.step, hb, hfam 0 le_rfl b hbK, hF1, S3Geom.steps_head suf,
      S3Geom.steps_last suf, fun m hm => ?_, S3Geom.endBlock_steps b suf hlast0, hfam 0 le_rfl s0 hs0K, ?_⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact hfam 0 le_rfl c (hsufK c hc)
    · rw [← hn']
      exact hxs0
  · -- several clusters: steps in the first cluster, a link, and the route along the later clusters
    have hrowK : ∀ i ≤ n - 1, ∀ c ∈ S.cluster E a0 (f (i + 1)).1, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny := by
      intro i hi c hc
      have hcF := hfam (i + 1) (by omega) c hc
      have h1 : ¬ (c.2.val ≤ hs a1 ∧ c ∈ S.family a0 a1 E c1) := hbot (i + 1) (by omega) (by omega) c hc
      refine ⟨?_, hftop c hcF⟩
      by_contra h
      exact h1 ⟨by omega, hcF⟩
    have he1 : (f 1).1 ∈ S.lev1 a0 E := (hL 0 hn0).2.1
    obtain ⟨Sel, rest, sEnd, ms, hdat, hfrag, hsepe, hne, hhead, hlast, hblk, hend⟩ :=
      S.route_of_chain (a1 := a1) ha0 hD1 hDa he1 (n := n - 1) (f := fun i => f (i + 1))
        (fun i hi => hP (i + 1) (by omega)) (fun i hi => hL (i + 1) (by omega)) rfl
        (fun i j hij hj => hdist (i + 1) (j + 1) (by omega) (by omega)) hrowK
    have hdl := hdat (n - 1) le_rfl
    have hSKl : ∀ c ∈ Sel (n - 1), c ∈ S.cluster E a0 (f (n - 1 + 1)).1 := hdl.1
    have hmeml : ∀ c ∈ (f (n - 1 + 1)).1 :: rest (n - 1), c ∈ Sel (n - 1) := hdl.2.2.2.2.2.1
    have hlastl : ((f (n - 1 + 1)).1 :: rest (n - 1)).getLast? = some (sEnd (n - 1)) := hdl.2.2.2.2.2.2.2.1
    have hxsl : G.blockDist (f (n - 1 + 1)).2 (sEnd (n - 1)) ≤ G.D - 1 := hdl.2.2.2.2.2.2.2.2
    rw [show n - 1 + 1 = n by omega] at hSKl hmeml hlastl hxsl
    have hselK : ∀ i ≤ n - 1, ∀ c ∈ Sel i, c ∈ S.cluster E a0 (f (i + 1)).1 := fun i hi => (hdat i hi).1
    -- the link from the cover of the first exit to the second entry
    have he1K : (f 1).1 ∈ S.cluster E a0 (f 1).1 := S.mem_cluster_self (hP 1 hn0).1
    have hlo : G.D ≤ G.blockDist s0 (f 1).1 := by
      have := S.cluster_sep hs0K he1K (hdist 0 1 (by omega) hn0)
      omega
    have hhi : G.blockDist s0 (f 1).1 ≤ G.D - 1 + a1 := by
      have t1 := G.blockDist_triangle s0 (f 0).2 (f 1).1
      have t2 : G.blockDist s0 (f 0).2 ≤ G.D - 1 := by
        rw [G.blockDist_comm]
        exact hxs0
      have t3 : G.blockDist (f 0).2 (f 1).1 ≤ a1 := (hL 0 hn0).2.2
      omega
    have herow1 : hs a1 + 1 ≤ (f 1).1.2.val ∧ (f 1).1.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E (f 1).1 := by
      have := hrowK 0 (Nat.zero_le _) (f 1).1 he1K
      exact ⟨by omega, by omega, (hP 1 hn0).1⟩
    have hlinkF : S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) s0
        [S3Geom.Move.link (f 1).1] :=
      ⟨⟨hlo, hhi, trivial⟩, List.isChain_singleton _, fun m hm => by
        rw [List.mem_singleton.1 hm]
        exact herow1, List.pairwise_singleton _ _⟩
    have hF2 : S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) s0
        (S3Geom.Move.link (f 1).1 :: ms) := by
      have := S3Geom.Frag.append (ms1 := [S3Geom.Move.link (f 1).1]) (ms2 := ms) hlinkF hfrag ?_ ?_
      · exact this
      · intro m hm m' hm'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hm
        subst hm
        have := hhead m' hm'
        cases m' with
        | step c => exact S3Geom.gram_link_step _ c
        | link c => exact absurd trivial this
        | leaf c => exact S3Geom.gram_link_leaf _ c
      · intro m hm m' hm'
        rw [List.mem_singleton.1 hm]
        exact hsepe m' hm'
    have hF : S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) b
        (suf.map S3Geom.Move.step ++ S3Geom.Move.link (f 1).1 :: ms) := by
      refine S3Geom.Frag.append hF1 (by rw [S3Geom.endBlock_steps b suf hlast0]; exact hF2) ?_ ?_
      · intro m hm m' hm'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm'
        subst hm'
        exact S3Geom.gram_to_link (S3Geom.steps_last suf m hm) _
      · intro m hm m' hm'
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
        have hcK := hsufK c hc
        rcases List.mem_cons.1 hm' with rfl | hm'
        · have := S.cluster_sep hcK he1K (hdist 0 1 (by omega) hn0)
          show G.D ≤ G.blockDist c (f 1).1
          omega
        · obtain ⟨i, hi, hmi⟩ := hblk m' hm'
          have hK : m'.blk ∈ S.cluster E a0 (f (i + 1)).1 := hselK i hi _ hmi
          have := S.cluster_sep hcK hK (hdist 0 (i + 1) (by omega) (by omega))
          show G.D ≤ G.blockDist c m'.blk
          omega
    have hhead' : ∀ m ∈ (suf.map S3Geom.Move.step ++ S3Geom.Move.link (f 1).1 :: ms).head?, ¬ m.isLeaf :=
      S3Geom.head?_append_forall (S3Geom.steps_head suf) (fun m hm => by
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
        subst hm
        exact fun h => False.elim h)
    have hlast' : ∀ m ∈ (suf.map S3Geom.Move.step ++ S3Geom.Move.link (f 1).1 :: ms).getLast?,
        ¬ m.isLink := by
      refine S3Geom.getLast?_append_forall (S3Geom.steps_last suf) (fun m hm => ?_)
      obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
      rw [hat, List.getLast?_cons_cons, ← hat] at hm
      exact hlast m hm
    have hend' : S3Geom.endBlock b (suf.map S3Geom.Move.step ++ S3Geom.Move.link (f 1).1 :: ms) =
        sEnd (n - 1) := by
      rw [S3Geom.endBlock_append, S3Geom.endBlock_steps b suf hlast0]
      exact hend
    refine ⟨b, sEnd (n - 1), suf.map S3Geom.Move.step ++ S3Geom.Move.link (f 1).1 :: ms, hb,
      hfam 0 (Nat.zero_le _) b hbK, hF, hhead', hlast', fun m hm => ?_, hend',
      hfam n le_rfl _ (hSKl _ (hmeml _ (List.mem_of_getLast? hlastl))), ?_⟩
    · rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
        exact hfam 0 (Nat.zero_le _) c (hsufK c hc)
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact hfam 1 hn0 _ he1K
        · obtain ⟨i, hi, hmi⟩ := hblk m hm
          exact hfam (i + 1) (by omega) _ (hselK i hi _ hmi)
    · rw [← hn']
      exact hxsl

/-- **The top end route** (F4): in a family with a block in the top strip, without T1, from a level-1 root `e`:
in-cluster steps and links, with a leaf after every link into a cluster strictly between the strips whose route part is
the root alone, stopped before the first block in the top strip. The route is empty if `e` lies in the top strip. -/
theorem top_route {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) (ha01 : a0 ≤ a1)
    {E : G.Ed → ZMod 2} (hT1 : ¬ S.T1 a0 a1 E) {e c2 : G.Block} (he : e ∈ S.lev1 a0 E)
    (hc2 : c2 ∈ S.family a0 a1 E e) (hrow2 : G.ny ≤ c2.2.val + 1 + hs a1) :
    ∃ ms : List G.Move, hs a1 + 1 ≤ e.2.val ∧ (G.ny ≤ e.2.val + 1 + hs a1 → ms = []) ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms.head?, ¬ m.isLeaf) ∧ (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧
      (∀ m ∈ ms, m.blk ∈ S.family a0 a1 E e) ∧
      G.ny ≤ (S3Geom.endBlock e ms).2.val + 1 + hs a1 + (G.D - 1 + a1) := by
  have hebad : S.badD E e := S.badD_of_lev1 he
  have hhs1 : 1 ≤ hs a1 := by simp [hs]
  have hfrow : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val := fun c hc =>
    S.family_above_bot hT1 hebad hc2 hrow2 hc
  have he1 : hs a1 + 1 ≤ e.2.val := hfrow e (S.mem_family_self hebad)
  by_cases hetop : G.ny ≤ e.2.val + 1 + hs a1
  · refine ⟨[], he1, fun _ => rfl, ⟨trivial, List.isChain_nil, fun m hm => absurd hm (by simp),
      List.Pairwise.nil⟩, fun m hm => absurd hm (by simp), fun m hm => absurd hm (by simp),
      fun m hm => absurd hm (by simp), ?_⟩
    show G.ny ≤ e.2.val + 1 + hs a1 + (G.D - 1 + a1)
    omega
  obtain ⟨n0, f0, hP0, hL0, h00, hn0⟩ := S.exists_partial_chain hebad c2 hc2.2
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, -, htop⟩ :=
    S.exists_min_gchain (a0 := a0) (a1 := a1) (E := E) (Pst := fun c : G.Block => c = e)
      (Pen := fun c : G.Block => G.ny ≤ c.2.val + 1 + hs a1) ⟨n0, f0, hP0, hL0, h00, by rw [hn0]; exact hrow2⟩
  have h0' : (f 0).1 = e := h0
  have hn' : G.ny ≤ (f n).2.2.val + 1 + hs a1 := hn
  have hfam : ∀ i ≤ n, ∀ c ∈ S.cluster E a0 (f i).1, c ∈ S.family a0 a1 E e :=
    S.fchain_family hebad (x := (f n).2) ⟨hP, hL, h0', rfl⟩
  -- cluster facts
  have heK : ∀ i ≤ n, (f i).1 ∈ S.cluster E a0 (f i).1 := fun i hi => S.mem_cluster_self (hP i hi).1
  have hxK : ∀ i ≤ n, (f i).2 ∈ S.cluster E a0 (f i).1 := fun i hi => by
    rw [(hP i hi).2.2]
    exact S.mem_cluster_self (hP i hi).2.1
  have hbadK : ∀ i, ∀ c ∈ S.cluster E a0 (f i).1, S.badD E c := fun i c hc => S3Geom.comp_subset hc
  have hsepK : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → ∀ x ∈ S.cluster E a0 (f i).1, ∀ y ∈ S.cluster E a0 (f j).1,
      G.D ≤ G.blockDist x y := by
    intro i hi j hj hij x hx y hy
    rcases lt_or_gt_of_ne hij with h | h
    · have := S.cluster_sep hx hy (hdist i j h hj)
      omega
    · have := S.cluster_sep hy hx (hdist j i h hi)
      rw [G.blockDist_comm] at this
      omega
  -- clusters before the last lie strictly between the strips
  have hmid : ∀ i < n, ∀ c ∈ S.cluster E a0 (f i).1,
      hs a1 + 1 ≤ c.2.val ∧ c.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E c := fun i hi c hc => by
    have h1 := hfrow c (hfam i hi.le c hc)
    have h2 : ¬ G.ny ≤ c.2.val + 1 + hs a1 := htop i hi c hc
    exact ⟨by omega, by omega, hbadK i c hc⟩
  -- per cluster: a selection rooted at the entry and a simple path to the cover of the exit
  have hdata : ∀ i, ∃ (Sel : Finset G.Block) (rest : List G.Block) (s : G.Block), i ≤ n →
      (∀ b ∈ Sel, b ∈ S.cluster E a0 (f i).1) ∧
      (∀ b ∈ Sel, ∀ b' ∈ Sel, b ≠ b' → G.D ≤ G.blockDist b b') ∧
      (∀ b ∈ Sel, Relation.ReflTransGen
        (fun x y => x ∈ Sel ∧ y ∈ Sel ∧ G.blockDist x y ≤ G.D - 1 + a0) (f i).1 b) ∧
      (∀ c ∈ S.cluster E a0 (f i).1, ∃ b ∈ Sel, G.blockDist c b ≤ G.D - 1) ∧
      ((f i).1 :: rest).Nodup ∧ (∀ b ∈ (f i).1 :: rest, b ∈ Sel) ∧
      List.IsChain (fun x y => x ≠ y ∧ G.blockDist x y ≤ G.D - 1 + a0) ((f i).1 :: rest) ∧
      ((f i).1 :: rest).getLast? = some s ∧ G.blockDist (f i).2 s ≤ G.D - 1 := by
    intro i
    by_cases hi : i ≤ n
    · have hconnK : ∀ x ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1), Relation.ReflTransGen
          (fun x y => x ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1) ∧
            y ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1) ∧ G.blockDist x y ≤ a0) (f i).1 x := by
        intro x hx
        have h := S3Geom.comp_chain (B := {c | S.badD E c}) (a := a0) (hP i hi).1 (f i).1 (heK i hi) x
          (Finset.mem_filter.1 hx).2
        clear hx
        induction h with
        | refl => exact .refl
        | tail _ huv ih =>
          exact ih.tail ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.1⟩,
            Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.2.1⟩, huv.2.2⟩
      obtain ⟨Sel, ⟨hSK, hrS, hsep, hconn⟩, hcov⟩ := S3Geom.exists_selection (a := a0) hD1
        (K := Finset.univ.filter (· ∈ S.cluster E a0 (f i).1)) (r := (f i).1) (by simpa using heK i hi) hconnK
      obtain ⟨s, hsS, hxs⟩ := hcov (f i).2 (by simpa using hxK i hi)
      obtain ⟨l, hhead, hlast, hnd, hmem, hch⟩ := S3Geom.exists_simple_path hrS (hconn s hsS)
      cases l with
      | nil => simp at hhead
      | cons e' rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        refine ⟨Sel, rest, s, fun _ => ⟨fun b hb => ?_, hsep, hconn, fun c hc => hcov c (by simpa using hc), hnd,
          hmem, hch, hlast, hxs⟩⟩
        have := hSK hb
        simpa using this
    · exact ⟨∅, [], (f i).1, fun h => absurd h hi⟩
  choose Sel rest sEnd hdat using hdata
  -- the path of a cluster, with separation
  have hpath : ∀ i ≤ n, List.IsChain (fun x y => G.D ≤ G.blockDist x y ∧ G.blockDist x y ≤ G.D - 1 + a0)
      ((f i).1 :: rest i) := by
    intro i hi
    obtain ⟨-, hsep, -, -, -, hmem, hch, -, -⟩ := hdat i hi
    exact hch.imp_of_mem_imp fun x y hx hy hxy => ⟨hsep x (hmem x hx) y (hmem y hy) hxy.1, hxy.2⟩
  have hpw : ∀ i ≤ n, ((f i).1 :: rest i).Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
    intro i hi
    obtain ⟨-, hsep, -, -, hnd, hmem, -, -, -⟩ := hdat i hi
    exact List.Pairwise.imp_of_mem (fun hx hy hxy => hsep _ (hmem _ hx) _ (hmem _ hy) hxy) hnd
  have hpK : ∀ i ≤ n, ∀ b ∈ (f i).1 :: rest i, b ∈ S.cluster E a0 (f i).1 := by
    intro i hi b hb
    obtain ⟨hSK, -, -, -, -, hmem, -, -, -⟩ := hdat i hi
    exact hSK b (hmem b hb)
  have hsK : ∀ i ≤ n, sEnd i ∈ S.cluster E a0 (f i).1 := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, -, hlastP, -⟩ := hdat i hi
    exact hpK i hi _ (List.mem_of_getLast? hlastP)
  -- links from the cover of an exit to the next entry
  have hlink : ∀ i, i < n → G.D ≤ G.blockDist (sEnd i) (f (i + 1)).1 ∧
      G.blockDist (sEnd i) (f (i + 1)).1 ≤ G.D - 1 + a1 := by
    intro i hin
    obtain ⟨-, -, -, -, -, -, -, -, hxs⟩ := hdat i hin.le
    refine ⟨hsepK i hin.le (i + 1) hin (by omega) _ (hsK i hin.le) _ (heK (i + 1) hin), ?_⟩
    have t1 := G.blockDist_triangle (sEnd i) (f i).2 (f (i + 1)).1
    have t2 : G.blockDist (sEnd i) (f i).2 ≤ G.D - 1 := by
      rw [G.blockDist_comm]
      exact hxs
    have t3 := (hL i hin).2.2
    omega
  -- leaves in middle clusters, from (W0)
  have hleaf : ∀ i, 1 ≤ i → i < n → ∃ l ∈ Sel i, l ≠ (f i).1 ∧ G.blockDist (f i).1 l ≤ G.D - 1 + a0 := by
    intro i hi1 hin
    obtain ⟨-, -, hconn, hcov, -, hmem, -, -, -⟩ := hdat i hin.le
    have hlev : (f i).1 ∈ S.lev1 a0 E := by
      have := (hL (i - 1) (by omega)).2.1
      rwa [show i - 1 + 1 = i by omega] at this
    obtain ⟨hfl, hunres⟩ := hlev
    have hodd : ∑ v, G.restrictTo (G.comp (S3Geom.flaggedSet (S.resid E)) a0 (f i).1) (S.resid E) v ≠ 0 :=
      fun h => hunres (Or.inl h)
    have hint : Interior (S.cluster E a0 (f i).1) := by
      intro c hc hdecl
      have := hmid i hin c hc
      rcases hdecl with h | h <;> omega
    obtain ⟨c'', hc''K, -, hfar⟩ := S.W0 ha0 hfl hint hodd
    have hfar' := hfar (f i).1 (S3Geom.mem_comp_self hfl)
    obtain ⟨s, hsS, hcs⟩ := hcov c'' hc''K
    have hsne : s ≠ (f i).1 := by
      rintro rfl
      rw [G.blockDist_comm] at hcs
      omega
    obtain ⟨l, hhead, hlast, -, hmemL, hch⟩ :=
      S3Geom.exists_simple_path (hmem _ List.mem_cons_self) (hconn s hsS)
    rcases l with _ | ⟨e', _ | ⟨y, l⟩⟩
    · simp at hhead
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd (hlast.symm.trans hhead) hsne
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rw [List.isChain_cons_cons] at hch
      exact ⟨y, hmemL y (by simp), fun h => hch.1.1 h.symm, hch.1.2⟩
  -- the end of the last path is high enough
  have hendN : ∀ s', ((f n).1 :: rest n).getLast? = some s' →
      G.ny ≤ s'.2.val + 1 + hs a1 + (G.D - 1 + a1) := by
    intro s' hs'
    obtain ⟨-, -, -, -, -, -, -, hlastP, hxs⟩ := hdat n le_rfl
    rw [hlastP, Option.some.injEq] at hs'
    subst hs'
    have := S3Geom.row_le_add_blockDist (sEnd n) (f n).2
    rw [G.blockDist_comm] at this
    omega
  have heK0 : e ∈ S.cluster E a0 (f 0).1 := by
    rw [← h0']
    exact heK 0 (Nat.zero_le _)
  -- the prefix through cluster i < n
  have hinv : ∀ i, i < n → ∃ ms : List G.Move,
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms.head?, ¬ m.isLeaf) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ j ≤ i, m.blk ∈ S.cluster E a0 (f j).1) ∧ (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧
      S3Geom.endBlock e ms = sEnd i := by
    intro i
    induction i with
    | zero =>
      intro hn0
      obtain ⟨-, -, -, -, -, -, -, hlastP, -⟩ := hdat 0 (by omega)
      have hch := hpath 0 (by omega)
      have hpw0 := hpw 0 (by omega)
      rw [List.pairwise_cons] at hpw0
      rw [h0'] at hlastP hch hpw0
      refine ⟨(rest 0).map S3Geom.Move.step,
        S3Geom.Frag.steps e (rest 0) hch
          (fun c hc => hmid 0 hn0 c (hpK 0 (by omega) c (List.mem_cons_of_mem _ hc))) hpw0.2,
        S3Geom.steps_head _, S3Geom.steps_last _, fun m hm => ?_, fun m hm => ?_,
        S3Geom.endBlock_steps e _ hlastP⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
        exact ⟨0, le_rfl, hpK 0 (by omega) c (List.mem_cons_of_mem _ hc)⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
        exact hpw0.1 c hc
    | succ i ih =>
      intro hin
      obtain ⟨ms, hfrag, hhead, hlast, hblk, hsepe, hend⟩ := ih (by omega)
      obtain ⟨hSK, hsep, -, -, -, hmem, -, hlastP, -⟩ := hdat (i + 1) hin.le
      obtain ⟨hlo, hhi⟩ := hlink i (by omega)
      have hmid1 := hmid (i + 1) hin
      -- the unit of the middle cluster i + 1: a link, then steps or a leaf
      obtain ⟨unit, hufrag, huhead, hulast, hublk, huend⟩ : ∃ unit : List G.Move,
          S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (sEnd i) unit ∧
          (∀ m ∈ unit.head?, m = S3Geom.Move.link (f (i + 1)).1) ∧ (∀ m ∈ unit.getLast?, ¬ m.isLink) ∧
          (∀ m ∈ unit, m.blk ∈ S.cluster E a0 (f (i + 1)).1) ∧
          S3Geom.endBlock (sEnd i) unit = sEnd (i + 1) := by
        by_cases hr : rest (i + 1) = []
        · obtain ⟨l, hlS, hlne, hll⟩ := hleaf (i + 1) (by omega) hin
          have hsend : sEnd (i + 1) = (f (i + 1)).1 := by
            rw [hr] at hlastP
            simp only [List.getLast?_singleton, Option.some.injEq] at hlastP
            exact hlastP.symm
          refine ⟨[S3Geom.Move.link (f (i + 1)).1, S3Geom.Move.leaf l],
            S3Geom.Frag.link_leaf _ _ _ hlo hhi (hsep _ (hmem _ List.mem_cons_self) _ hlS hlne.symm) hll
              (hmid1 _ (heK _ hin.le)) (hmid1 _ (hSK l hlS)), by simp, fun m hm => ?_, fun m hm => ?_, ?_⟩
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
              Option.some.injEq] at hm
            subst hm
            exact fun h => False.elim h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact heK _ hin.le
            · exact hSK l hlS
          · rw [hsend]
            rfl
        · refine ⟨S3Geom.Move.link (f (i + 1)).1 :: (rest (i + 1)).map S3Geom.Move.step,
            S3Geom.Frag.link_steps _ _ _ hlo hhi (hpath _ hin.le) (fun c hc => hmid1 c (hpK _ hin.le c hc))
              (hpw _ hin.le), by simp, fun m hm => ?_, fun m hm => ?_, S3Geom.endBlock_steps _ _ hlastP⟩
          · obtain ⟨c, rest', hcr⟩ := List.exists_cons_of_ne_nil hr
            rw [hcr, List.map_cons, List.getLast?_cons_cons, ← List.map_cons] at hm
            exact S3Geom.steps_last _ m hm
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact heK _ hin.le
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
              exact hpK _ hin.le c (List.mem_cons_of_mem _ hc)
      refine ⟨ms ++ unit, S3Geom.Frag.append hfrag (by rw [hend]; exact hufrag) (fun m hm m' hm' => ?_)
        (fun m hm m' hm' => ?_), S3Geom.head?_append_forall hhead (fun m hm => ?_),
        S3Geom.getLast?_append_forall hlast hulast, fun m hm => ?_, fun m hm => ?_, ?_⟩
      · rw [huhead m' hm']
        exact S3Geom.gram_to_link (hlast m hm) _
      · obtain ⟨j, hj, hmj⟩ := hblk m hm
        exact hsepK j (by omega) (i + 1) hin.le (by omega) _ hmj _ (hublk m' hm')
      · rw [huhead m hm]
        exact fun h => False.elim h
      · rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨j, hj, hmj⟩ := hblk m hm
          exact ⟨j, by omega, hmj⟩
        · exact ⟨i + 1, le_rfl, hublk m hm⟩
      · rcases List.mem_append.1 hm with hm | hm
        · exact hsepe m hm
        · exact hsepK 0 (by omega) (i + 1) hin.le (by omega) _ heK0 _ (hublk m hm)
      · rw [S3Geom.endBlock_append, hend, huend]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: steps from the root until the top strip
    subst hn0
    have hch := hpath 0 le_rfl
    have hpw0 := hpw 0 le_rfl
    rw [List.pairwise_cons] at hpw0
    have hend0 := hendN
    rw [h0'] at hch hpw0 hend0
    have hrow0 : ∀ c ∈ rest 0, hs a1 + 1 ≤ c.2.val ∧ S.badD E c := fun c hc => by
      have hcK := hpK 0 le_rfl c (List.mem_cons_of_mem _ hc)
      exact ⟨hfrow c (hfam 0 le_rfl c hcK), hbadK 0 c hcK⟩
    obtain ⟨l1, hfrag, htop1, hl1⟩ := S3Geom.final_cut (by omega : G.D - 1 + a0 ≤ G.D - 1 + a1) e (rest 0)
      hch hrow0 hpw0.2 hend0
    refine ⟨l1.map S3Geom.Move.step, he1, fun h => absurd h hetop, hfrag, S3Geom.steps_head l1,
      fun m hm => ?_, fun m hm => ?_, htop1⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact hpw0.1 c (hl1 c hc)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact hfam 0 le_rfl c (hpK 0 le_rfl c (List.mem_cons_of_mem _ (hl1 c hc)))
  · -- several clusters: the prefix through cluster n - 1, then the last cluster
    obtain ⟨ms, hfrag, hhead, hlast, hblk, hsepe, hend⟩ := hinv (n - 1) (by omega)
    obtain ⟨hlo, hhi⟩ := hlink (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at hlo hhi
    have hmsF : ∀ m ∈ ms, m.blk ∈ S.family a0 a1 E e := fun m hm => by
      obtain ⟨j, hj, hmj⟩ := hblk m hm
      exact hfam j (by omega) _ hmj
    by_cases htopn : G.ny ≤ (f n).1.2.val + 1 + hs a1
    · -- the entry of the last cluster is in the top strip: the prefix is the route
      refine ⟨ms, he1, fun h => absurd h hetop, hfrag, hhead, hsepe, hmsF, ?_⟩
      rw [hend]
      have := S3Geom.row_le_add_blockDist (sEnd (n - 1)) (f n).1
      omega
    · -- link into the last cluster, then steps until the top strip
      have hrowN : ∀ c ∈ rest n, hs a1 + 1 ≤ c.2.val ∧ S.badD E c := fun c hc => by
        have hcK := hpK n le_rfl c (List.mem_cons_of_mem _ hc)
        exact ⟨hfrow c (hfam n le_rfl c hcK), hbadK n c hcK⟩
      have hpwN := hpw n le_rfl
      rw [List.pairwise_cons] at hpwN
      obtain ⟨l1, hfrag1, htop1, hl1⟩ := S3Geom.final_cut (by omega : G.D - 1 + a0 ≤ G.D - 1 + a1) (f n).1
        (rest n) (hpath n le_rfl) hrowN hpwN.2 hendN
      have herow : hs a1 + 1 ≤ (f n).1.2.val ∧ (f n).1.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E (f n).1 := by
        have := hfrow _ (hfam n le_rfl _ (heK n le_rfl))
        exact ⟨by omega, by omega, (hP n le_rfl).1⟩
      have hlinkF : S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (sEnd (n - 1))
          [S3Geom.Move.link (f n).1] :=
        ⟨⟨hlo, hhi, trivial⟩, List.isChain_singleton _, fun m hm => by
          rw [List.mem_singleton.1 hm]
          exact herow, List.pairwise_singleton _ _⟩
      have hj1 : ∀ m ∈ [S3Geom.Move.link (f n).1].getLast?, ∀ m' ∈ (l1.map S3Geom.Move.step).head?,
          S3Geom.GramOK m m' := by
        intro m hm m' hm'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hm
        subst hm
        cases l1 with
        | nil => simp at hm'
        | cons c l1 =>
          simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hm'
          subst hm'
          exact S3Geom.gram_link_step _ c
      have hs1 : ∀ m ∈ [S3Geom.Move.link (f n).1], ∀ m' ∈ l1.map S3Geom.Move.step,
          G.D ≤ G.blockDist m.blk m'.blk := by
        intro m hm m' hm'
        rw [List.mem_singleton.1 hm]
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm'
        exact hpwN.1 c (hl1 c hc)
      have hunit := S3Geom.Frag.append hlinkF hfrag1 hj1 hs1
      have hunitK : ∀ m ∈ [S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step,
          m.blk ∈ S.cluster E a0 (f n).1 := by
        intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · rw [List.mem_singleton.1 hm]
          exact heK n le_rfl
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
          exact hpK n le_rfl c (List.mem_cons_of_mem _ (hl1 c hc))
      have hj2 : ∀ m ∈ ms.getLast?, ∀ m' ∈ ([S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step).head?,
          S3Geom.GramOK m m' := by
        intro m hm m' hm'
        simp only [List.singleton_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hm'
        subst hm'
        exact S3Geom.gram_to_link (hlast m hm) _
      have hs2 : ∀ m ∈ ms, ∀ m' ∈ [S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step,
          G.D ≤ G.blockDist m.blk m'.blk := by
        intro m hm m' hm'
        obtain ⟨j, hj, hmj⟩ := hblk m hm
        exact hsepK j (by omega) n le_rfl (by omega) _ hmj _ (hunitK m' hm')
      have hfull := S3Geom.Frag.append hfrag (by rw [hend]; exact hunit) hj2 hs2
      have hhead2 : ∀ m ∈ ([S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step).head?, ¬ m.isLeaf := by
        intro m hm
        simp only [List.singleton_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hm
        subst hm
        exact fun h => False.elim h
      refine ⟨ms ++ ([S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step), he1, fun h => absurd h hetop, hfull,
        S3Geom.head?_append_forall hhead hhead2, fun m hm => ?_, fun m hm => ?_, ?_⟩
      · rcases List.mem_append.1 hm with hm | hm
        · exact hsepe m hm
        · exact hsepK 0 (Nat.zero_le _) n le_rfl (by omega) _ heK0 _ (hunitK m hm)
      · rcases List.mem_append.1 hm with hm | hm
        · exact hmsF m hm
        · exact hfam n le_rfl _ (hunitK m hm)
      · rw [S3Geom.endBlock_append, hend]
        exact htop1

end Stage1

end QECML
