import QECML.TwoD.LemmaX

/-!
# T2 skeletons

Part 1: the route of an intermediate family (Steps 2-4). For a family all of whose blocks lie strictly between the
strips, an entry block `e` (a level-1 block, e.g. the block of an odd check of `Ω`) and an exit block `x` in the same
family:

* `exists_min_fchain`: a chain of (entry, exit) pairs of clusters from `e` to `x`, consecutive clusters joined by a
  level-1 link, with pairwise distinct clusters (a shortest chain);
* `fam_route`: the route of selected blocks from `e` to the selected block covering `x`: in-cluster steps (offsets in
  `S0`), links (offsets in `S1`), and a leaf (from (W0)) right after the root of every route cluster whose route part
  is the root alone (the first cluster included: its root is a level-1 block too).
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- A cluster chain with fixed ends: pairs `f 0, …, f n`, entry `e`, exit `x`. -/
def FChain (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (e x : G.Block) (n : ℕ) (f : ℕ → G.Block × G.Block) : Prop :=
  (∀ i ≤ n, S.PairOK a0 E (f i)) ∧ (∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1) ∧ (f 0).1 = e ∧ (f n).2 = x

/-- **A shortest chain with fixed ends has distinct clusters.** -/
theorem exists_min_fchain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e x : G.Block}
    (hex : ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e x n f) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e x n f ∧
      ∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1 := by
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → G.Block × G.Block, S.FChain a0 a1 E e x m g) → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨hP, hL, h0, hn⟩ := hf
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, ?_⟩
  intro i j hij hjn hcl
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧
      g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
    ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
      fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
  have hg : S.FChain a0 a1 E e x (n - (j - i)) g := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        exact hP k (by omega)
      · rw [h, hg2]
        obtain ⟨hei, _, _⟩ := hP i (by omega)
        obtain ⟨_, hxj, hclj⟩ := hP j hjn
        exact ⟨hei, hxj, hcl.trans hclj⟩
      · rw [hg3 k h]
        exact hP _ (by omega)
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        rcases (show k + 1 < i ∨ k + 1 = i by omega) with h' | h'
        · rw [hg1 (k + 1) h']
          exact hL k (by omega)
        · rw [h', hg2]
          have := hL k (by omega)
          rw [h'] at this
          exact this
      · rw [h, hg2, hg3 (i + 1) (by omega), show i + 1 + (j - i) = j + 1 by omega]
        exact hL j (by omega)
      · rw [hg3 k h, hg3 (k + 1) (by omega), show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hL _ (by omega)
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [hg2]
        exact h0
      · rw [hg1 0 h]
        exact h0
    · rcases eq_or_lt_of_le (show i ≤ n - (j - i) by omega) with h | h
      · rw [← h, hg2, show j = n by omega]
        exact hn
      · rw [hg3 _ h, show n - (j - i) + (j - i) = n by omega]
        exact hn
  have := hmin _ ⟨g, hg⟩
  omega

/-- A chain inside a family exists between any two of its blocks. -/
theorem exists_fchain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e x : G.Block} (he : S.badD E e)
    (hx : x ∈ S.family a0 a1 E e) : ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e x n f :=
  S.exists_partial_chain he x hx.2

/-- Blocks linked to a block of a family are in the family; a chain stays in the family of its entry. -/
theorem fchain_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e x : G.Block} (he : S.badD E e) {n : ℕ}
    {f : ℕ → G.Block × G.Block} (hf : S.FChain a0 a1 E e x n f) :
    ∀ i ≤ n, ∀ c ∈ S.cluster E a0 (f i).1, c ∈ S.family a0 a1 E e := by
  obtain ⟨hP, hL, h0, _⟩ := hf
  have hroot : ∀ i ≤ n, (f i).1 ∈ S.family a0 a1 E e := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact S.mem_family_self he
    | succ i ih =>
      intro hi
      obtain ⟨hbe, hbx, hcl⟩ := hP i (by omega)
      have hfi := ih (by omega)
      -- the exit is in the same cluster as the entry
      have hx : (f i).2 ∈ S.family a0 a1 E e := by
        rw [← S.family_eq_of_mem hfi]
        exact ⟨hbe, .single ⟨hbe, hbx, Or.inl hcl⟩⟩
      -- the level-1 link
      obtain ⟨hx1, he1, hd⟩ := hL i (by omega)
      have hmem : (f (i + 1)).1 ∈ G.comp (S.lev1 a0 E) a1 (f i).2 := ⟨hx1, .single ⟨hx1, he1, hd⟩⟩
      have hlk : S.linked a0 a1 E (f i).2 (f (i + 1)).1 :=
        ⟨hbx, S.badD_of_lev1 he1, Or.inr ⟨hx1, he1, (S3Geom.comp_eq_of_mem hmem).symm⟩⟩
      rw [← S.family_eq_of_mem hx]
      exact ⟨hbx, .single hlk⟩
  intro i hi c hc
  have hfi := hroot i hi
  rw [← S.family_eq_of_mem hfi]
  exact S.mem_family_of_cluster (S.badD_of_mem_family hfi) hc

/-- **The route along a cluster chain** with distinct clusters strictly between the strips and a level-1 first root:
from the first root to the selected block covering the last exit, with a leaf after the root of every cluster whose
route part is the root alone. -/
theorem route_of_chain {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1)
    {E : G.Ed → ZMod 2} {e : G.Block} (he : e ∈ S.lev1 a0 E) {n : ℕ} {f : ℕ → G.Block × G.Block}
    (hP : ∀ i ≤ n, S.PairOK a0 E (f i)) (hL : ∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1)
    (h0 : (f 0).1 = e) (hdist : ∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1)
    (hrowK : ∀ i ≤ n, ∀ c ∈ S.cluster E a0 (f i).1, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny) :
    ∃ (Sel : ℕ → Finset G.Block) (rest : ℕ → List G.Block) (sEnd : ℕ → G.Block) (ms : List G.Move),
      (∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
        (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        (∀ b ∈ Sel i, Relation.ReflTransGen
          (fun y z => y ∈ Sel i ∧ z ∈ Sel i ∧ G.blockDist y z ≤ G.D - 1 + a0) (f i).1 b) ∧
        (∀ c ∈ S.cluster E a0 (f i).1, ∃ b ∈ Sel i, G.blockDist c b ≤ G.D - 1) ∧
        ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
        ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1) ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧ ms ≠ [] ∧
      (∀ m ∈ ms.head?, ¬ m.isLink) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ i ≤ n, m.blk ∈ Sel i) ∧ S3Geom.endBlock e ms = sEnd n := by
  have hebad : S.badD E e := S.badD_of_lev1 he
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
  have hrow : ∀ i ≤ n, ∀ c ∈ S.cluster E a0 (f i).1,
      hs a1 + 1 ≤ c.2.val ∧ c.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E c := fun i hi c hc => by
    have := hrowK i hi c hc
    exact ⟨by omega, by omega, hbadK i c hc⟩
  -- per cluster: a selection rooted at the entry and a simple path to the cover of the exit
  have hdata : ∀ i, ∃ (Sel : Finset G.Block) (rest : List G.Block) (s : G.Block), i ≤ n →
      (∀ b ∈ Sel, b ∈ S.cluster E a0 (f i).1) ∧
      (∀ b ∈ Sel, ∀ b' ∈ Sel, b ≠ b' → G.D ≤ G.blockDist b b') ∧
      (∀ b ∈ Sel, Relation.ReflTransGen
        (fun y z => y ∈ Sel ∧ z ∈ Sel ∧ G.blockDist y z ≤ G.D - 1 + a0) (f i).1 b) ∧
      (∀ c ∈ S.cluster E a0 (f i).1, ∃ b ∈ Sel, G.blockDist c b ≤ G.D - 1) ∧
      ((f i).1 :: rest).Nodup ∧ (∀ b ∈ (f i).1 :: rest, b ∈ Sel) ∧
      List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest) ∧
      ((f i).1 :: rest).getLast? = some s ∧ G.blockDist (f i).2 s ≤ G.D - 1 := by
    intro i
    by_cases hi : i ≤ n
    · have hconnK : ∀ y ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1), Relation.ReflTransGen
          (fun y z => y ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1) ∧
            z ∈ Finset.univ.filter (· ∈ S.cluster E a0 (f i).1) ∧ G.blockDist y z ≤ a0) (f i).1 y := by
        intro y hy
        have h := S3Geom.comp_chain (B := {c | S.badD E c}) (a := a0) (hP i hi).1 (f i).1 (heK i hi) y
          (Finset.mem_filter.1 hy).2
        clear hy
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
  have hpath : ∀ i ≤ n, List.IsChain (fun y z => G.D ≤ G.blockDist y z ∧ G.blockDist y z ≤ G.D - 1 + a0)
      ((f i).1 :: rest i) := by
    intro i hi
    obtain ⟨-, hsep, -, -, -, hmem, hch, -, -⟩ := hdat i hi
    exact hch.imp_of_mem_imp fun y z hy hz hyz => ⟨hsep y (hmem y hy) z (hmem z hz) hyz.1, hyz.2⟩
  have hpw : ∀ i ≤ n, ((f i).1 :: rest i).Pairwise (fun b b' => G.D ≤ G.blockDist b b') := by
    intro i hi
    obtain ⟨-, hsep, -, -, hnd, hmem, -, -, -⟩ := hdat i hi
    exact List.Pairwise.imp_of_mem (fun hy hz hyz => hsep _ (hmem _ hy) _ (hmem _ hz) hyz) hnd
  have hpK : ∀ i ≤ n, ∀ b ∈ (f i).1 :: rest i, b ∈ S.cluster E a0 (f i).1 := by
    intro i hi b hb
    obtain ⟨hSK, -, -, -, -, hmem, -, -, -⟩ := hdat i hi
    exact hSK b (hmem b hb)
  have hpS : ∀ i ≤ n, ∀ b ∈ (f i).1 :: rest i, b ∈ Sel i := by
    intro i hi b hb
    obtain ⟨-, -, -, -, -, hmem, -, -, -⟩ := hdat i hi
    exact hmem b hb
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
  -- the roots are level-1 blocks
  have hroot1 : ∀ i ≤ n, (f i).1 ∈ S.lev1 a0 E := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, h0]
      exact he
    · have := (hL (i - 1) (by omega)).2.1
      rwa [show i - 1 + 1 = i by omega] at this
  -- leaves in every cluster, from (W0)
  have hleaf : ∀ i ≤ n, ∃ l ∈ Sel i, l ≠ (f i).1 ∧ G.blockDist (f i).1 l ≤ G.D - 1 + a0 := by
    intro i hin
    obtain ⟨-, -, hconn, hcov, -, hmem, -, -, -⟩ := hdat i hin
    obtain ⟨hfl, hunres⟩ := hroot1 i hin
    have hodd : ∑ v, G.restrictTo (G.comp (S3Geom.flaggedSet (S.resid E)) a0 (f i).1) (S.resid E) v ≠ 0 :=
      fun h => hunres (Or.inl h)
    have hintr : Interior (S.cluster E a0 (f i).1) := by
      intro c hc hdecl
      have h1 := hrowK i hin c hc
      have hhs1 : 1 ≤ hs a1 := by simp [hs]
      rcases hdecl with h | h <;> omega
    obtain ⟨c'', hc''K, -, hfar⟩ := S.W0 ha0 hfl hintr hodd
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
  -- the prefix through cluster i
  have hinv : ∀ i, i ≤ n → ∃ ms : List G.Move,
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧ ms ≠ [] ∧
      (∀ m ∈ ms.head?, ¬ m.isLink) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ j ≤ i, m.blk ∈ Sel j) ∧ S3Geom.endBlock e ms = sEnd i := by
    intro i
    induction i with
    | zero =>
      intro hn0
      obtain ⟨hSK, hsep, -, -, hnd0, hmem, -, hlastP, -⟩ := hdat 0 hn0
      rw [h0] at hnd0 hmem hlastP
      by_cases hr : rest 0 = []
      · obtain ⟨l, hlS, hlne, hll⟩ := hleaf 0 hn0
        rw [h0] at hlne hll
        have hsend : sEnd 0 = e := by
          rw [hr] at hlastP
          simp only [List.getLast?_singleton, Option.some.injEq] at hlastP
          exact hlastP.symm
        have hlK : l ∈ S.cluster E a0 (f 0).1 := hSK l hlS
        have hel : G.D ≤ G.blockDist e l :=
          hsep e (by have := hmem e List.mem_cons_self; exact this) l hlS hlne.symm
        refine ⟨[S3Geom.Move.leaf l], ⟨⟨hel, hll, trivial⟩, List.isChain_singleton _, fun m hm => ?_,
          List.pairwise_singleton _ _⟩, fun m hm => ?_, List.cons_ne_nil _ _, ?_, ?_, fun m hm => ?_, ?_⟩
        · rw [List.mem_singleton.1 hm]
          exact hrow 0 hn0 l hlK
        · rw [List.mem_singleton.1 hm]
          exact hel
        · intro m hm
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hm
          subst hm
          exact fun h => False.elim h
        · intro m hm
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hm
          subst hm
          exact fun h => False.elim h
        · rw [List.mem_singleton.1 hm]
          exact ⟨0, le_rfl, hlS⟩
        · rw [hsend]
          rfl
      · have hch := hpath 0 hn0
        have hpw0 := hpw 0 hn0
        rw [h0] at hch hpw0
        rw [List.pairwise_cons] at hpw0
        refine ⟨(rest 0).map S3Geom.Move.step, S3Geom.Frag.steps e (rest 0) hch (fun c hc => ?_) hpw0.2,
          fun m hm => ?_, by simpa using hr, ?_, S3Geom.steps_last _, fun m hm => ?_,
          S3Geom.endBlock_steps e (rest 0) hlastP⟩
        · have hcK := hpK 0 hn0 c (by rw [h0]; exact List.mem_cons_of_mem _ hc)
          exact hrow 0 hn0 c hcK
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
          exact hpw0.1 c hc
        · intro m hm
          obtain ⟨c, rest', hcr⟩ := List.exists_cons_of_ne_nil hr
          rw [hcr] at hm
          simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hm
          subst hm
          exact fun h => False.elim h
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
          exact ⟨0, le_rfl, hpS 0 hn0 c (by rw [h0]; exact List.mem_cons_of_mem _ hc)⟩
    | succ i ih =>
      intro hin
      obtain ⟨ms, hfrag, he0, hne, hhead, hlast, hblk, hend⟩ := ih (by omega)
      obtain ⟨hSK, hsep, -, -, -, hmem, -, hlastP, -⟩ := hdat (i + 1) hin
      obtain ⟨hlo, hhi⟩ := hlink i (by omega)
      -- the unit of cluster i + 1: a link, then steps or a leaf
      obtain ⟨unit, hufrag, huhead, hulast, hublk, huend⟩ : ∃ unit : List G.Move,
          S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (sEnd i) unit ∧
          (∀ m ∈ unit.head?, m = S3Geom.Move.link (f (i + 1)).1) ∧ (∀ m ∈ unit.getLast?, ¬ m.isLink) ∧
          (∀ m ∈ unit, m.blk ∈ Sel (i + 1)) ∧ S3Geom.endBlock (sEnd i) unit = sEnd (i + 1) := by
        by_cases hr : rest (i + 1) = []
        · obtain ⟨l, hlS, hlne, hll⟩ := hleaf (i + 1) hin
          have hsend : sEnd (i + 1) = (f (i + 1)).1 := by
            rw [hr] at hlastP
            simp only [List.getLast?_singleton, Option.some.injEq] at hlastP
            exact hlastP.symm
          refine ⟨[S3Geom.Move.link (f (i + 1)).1, S3Geom.Move.leaf l],
            S3Geom.Frag.link_leaf _ _ _ hlo hhi (hsep _ (hmem _ List.mem_cons_self) _ hlS hlne.symm) hll
              (hrow _ hin _ (heK _ hin)) (hrow _ hin _ (hSK l hlS)), by simp, fun m hm => ?_, fun m hm => ?_, ?_⟩
          · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
              Option.some.injEq] at hm
            subst hm
            exact fun h => False.elim h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact hmem _ List.mem_cons_self
            · exact hlS
          · rw [hsend]
            rfl
        · refine ⟨S3Geom.Move.link (f (i + 1)).1 :: (rest (i + 1)).map S3Geom.Move.step,
            S3Geom.Frag.link_steps _ _ _ hlo hhi (hpath _ hin) (fun c hc => hrow _ hin c (hpK _ hin c hc))
              (hpw _ hin), by simp, fun m hm => ?_, fun m hm => ?_, S3Geom.endBlock_steps _ _ hlastP⟩
          · obtain ⟨c, rest', hcr⟩ := List.exists_cons_of_ne_nil hr
            rw [hcr, List.map_cons, List.getLast?_cons_cons, ← List.map_cons] at hm
            exact S3Geom.steps_last _ m hm
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact hmem _ List.mem_cons_self
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
              exact hmem c (List.mem_cons_of_mem _ hc)
      have hSKi : ∀ j ≤ n, ∀ b ∈ Sel j, b ∈ S.cluster E a0 (f j).1 := fun j hj b hb => (hdat j hj).1 b hb
      have hhead2 : ∀ m ∈ (ms ++ unit).head?, ¬ m.isLink := by
        obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
        intro m hm
        apply hhead m
        rw [hat] at hm ⊢
        simpa using hm
      refine ⟨ms ++ unit, S3Geom.Frag.append hfrag (by rw [hend]; exact hufrag) (fun m hm m' hm' => ?_)
        (fun m hm m' hm' => ?_), fun m hm => ?_, by simp [hne], hhead2,
        S3Geom.getLast?_append_forall hlast hulast, fun m hm => ?_, ?_⟩
      · rw [huhead m' hm']
        exact S3Geom.gram_to_link (hlast m hm) _
      · obtain ⟨j, hj, hmj⟩ := hblk m hm
        exact hsepK j (by omega) (i + 1) hin (by omega) _ (hSKi j (by omega) _ hmj) _
          (hSKi (i + 1) hin _ (hublk m' hm'))
      · rcases List.mem_append.1 hm with hm | hm
        · exact he0 m hm
        · have h1 := hSKi (i + 1) hin _ (hublk m hm)
          have h2 : e ∈ S.cluster E a0 (f 0).1 := by rw [h0]; exact S.mem_cluster_self hebad
          exact hsepK 0 (by omega) (i + 1) hin (by omega) e h2 _ h1
      · rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨j, hj, hmj⟩ := hblk m hm
          exact ⟨j, by omega, hmj⟩
        · exact ⟨i + 1, le_rfl, hublk m hm⟩
      · rw [S3Geom.endBlock_append, hend, huend]
  obtain ⟨ms, hfrag, he0, hne, hhead, hlast, hblk, hend⟩ := hinv n le_rfl
  exact ⟨Sel, rest, sEnd, ms, fun i hi => hdat i hi, hfrag, he0, hne, hhead, hlast, hblk, hend⟩

/-- **The route of an intermediate family**: from the entry block `e` (a level-1 block) to
the selected block covering the exit `x`, along a shortest cluster chain of the family. -/
theorem fam_route {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1)
    {E : G.Ed → ZMod 2} {e x : G.Block} (he : e ∈ S.lev1 a0 E) (hx : x ∈ S.family a0 a1 E e)
    (hint : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block) (Sel : ℕ → Finset G.Block) (rest : ℕ → List G.Block)
      (sEnd : ℕ → G.Block) (ms : List G.Move),
      S.FChain a0 a1 E e x n f ∧
      (∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1) ∧
      (∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
        (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        (∀ b ∈ Sel i, Relation.ReflTransGen
          (fun y z => y ∈ Sel i ∧ z ∈ Sel i ∧ G.blockDist y z ≤ G.D - 1 + a0) (f i).1 b) ∧
        (∀ c ∈ S.cluster E a0 (f i).1, ∃ b ∈ Sel i, G.blockDist c b ≤ G.D - 1) ∧
        ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
        ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1) ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧ ms ≠ [] ∧
      (∀ m ∈ ms.head?, ¬ m.isLink) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ i ≤ n, m.blk ∈ Sel i) ∧ S3Geom.endBlock e ms = sEnd n := by
  have hebad : S.badD E e := S.badD_of_lev1 he
  obtain ⟨n, f, hfch, hdist⟩ := S.exists_min_fchain (S.exists_fchain hebad hx)
  have hfam := S.fchain_family hebad hfch
  obtain ⟨hP, hL, h0, hn⟩ := hfch
  obtain ⟨Sel, rest, sEnd, ms, hdat, hrest⟩ := S.route_of_chain ha0 hD1 hDa he hP hL h0 hdist
    (fun i hi c hc => hint c (hfam i hi c hc))
  exact ⟨n, f, Sel, rest, sEnd, ms, ⟨hP, hL, h0, hn⟩, hdist, hdat, hrest⟩

/-- The level-1 component of a block. -/
def lev1comp (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (b : G.Block) : Set G.Block := G.comp (S.lev1 a0 E) a1 b

theorem lev1comp_eq_of_close {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {b b' : G.Block} (hb : b ∈ S.lev1 a0 E)
    (hb' : b' ∈ S.lev1 a0 E) (hd : G.blockDist b b' ≤ a1) : S.lev1comp a0 a1 E b' = S.lev1comp a0 a1 E b :=
  S3Geom.comp_eq_of_mem ⟨hb, .single ⟨hb, hb', hd⟩⟩

/-- **The witness dichotomy** (cases α and α'): on the route of an intermediate family whose
entry lies in an odd level-1 component, either some route cluster has a selected block at distance at least
`a1 + 2 - D` from its root, or (W1) gives a flagged level-1 block `c''` of a cluster off the route, more than `a1`
from the entry's level-1 component `K`, which then contains all route roots and exits (case β). -/
theorem fam_witness {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (Z : Solver G) {E : G.Ed → ZMod 2}
    {e x : G.Block} (he : e ∈ S.lev1 a0 E)
    (hodd : ¬ G.resolved (S.resid E) ((a1 + 1) / 2) (S.lev1comp a0 a1 E e))
    (hx1 : x ∈ S.lev1 a0 E)
    (hint : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny)
    {n : ℕ} {f : ℕ → G.Block × G.Block} (hfch : S.FChain a0 a1 E e x n f)
    {Sel : ℕ → Finset G.Block} {sEnd : ℕ → G.Block}
    (hcov : ∀ j ≤ n, ∀ c ∈ S.cluster E a0 (f j).1, ∃ b ∈ Sel j, G.blockDist c b ≤ G.D - 1)
    (hsEnd : ∀ j ≤ n, sEnd j ∈ Sel j ∧ G.blockDist (f j).2 (sEnd j) ≤ G.D - 1) :
    (∃ j ≤ n, ∃ b' ∈ Sel j, a1 + 2 - G.D ≤ G.blockDist (f j).1 b') ∨
      ((∀ j ≤ n, (f j).1 ∈ S.lev1comp a0 a1 E e ∧ (f j).2 ∈ S.lev1comp a0 a1 E e) ∧
        ∃ c'' ∈ S.lev1 a0 E, (∀ j ≤ n, c'' ∉ S.cluster E a0 (f j).1) ∧
          (∃ k ∈ S.lev1comp a0 a1 E e, c'' ∈ S.cluster E a0 k) ∧
          ∀ k ∈ S.lev1comp a0 a1 E e, a1 < G.blockDist k c'') := by
  obtain ⟨hP, hL, h0, hn⟩ := hfch
  have hebad : S.badD E e := S.badD_of_lev1 he
  -- roots and exits are level-1 blocks
  have hroot1 : ∀ j ≤ n, (f j).1 ∈ S.lev1 a0 E := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, h0]
      exact he
    · have := (hL (j - 1) (by omega)).2.1
      rwa [show j - 1 + 1 = j by omega] at this
  have hexit1 : ∀ j ≤ n, (f j).2 ∈ S.lev1 a0 E := by
    intro j hj
    rcases eq_or_lt_of_le hj with h | h
    · rw [h, hn]
      exact hx1
    · exact (hL j h).1
  by_cases hα : ∃ j ≤ n, S.lev1comp a0 a1 E (f j).1 ≠ S.lev1comp a0 a1 E (f j).2
  · -- case α: the route part of that cluster spans at least `a1 + 2 - D`
    left
    obtain ⟨j, hj, hK⟩ := hα
    obtain ⟨hsS, hxs⟩ := hsEnd j hj
    refine ⟨j, hj, sEnd j, hsS, ?_⟩
    have hfar : a1 < G.blockDist (f j).1 (f j).2 := by
      refine not_le.mp fun hd => hK ?_
      exact (S.lev1comp_eq_of_close (hroot1 j hj) (hexit1 j hj) hd).symm
    have t := G.blockDist_triangle (f j).1 (sEnd j) (f j).2
    rw [G.blockDist_comm (sEnd j)] at t
    omega
  · push Not at hα
    -- all roots and exits lie in the level-1 component of the entry
    have hK : ∀ j ≤ n, S.lev1comp a0 a1 E (f j).1 = S.lev1comp a0 a1 E e ∧
        S.lev1comp a0 a1 E (f j).2 = S.lev1comp a0 a1 E e := by
      intro j
      induction j with
      | zero =>
        intro _
        rw [h0]
        exact ⟨rfl, by rw [← hα 0 (by omega), h0]⟩
      | succ j ih =>
        intro hj
        have h1 : S.lev1comp a0 a1 E (f (j + 1)).1 = S.lev1comp a0 a1 E e := by
          obtain ⟨hx, he', hd⟩ := hL j (by omega)
          rw [S.lev1comp_eq_of_close hx he' hd]
          exact (ih (by omega)).2
        exact ⟨h1, by rw [← hα (j + 1) hj]; exact h1⟩
    have hmemK : ∀ j ≤ n, (f j).1 ∈ S.lev1comp a0 a1 E e ∧ (f j).2 ∈ S.lev1comp a0 a1 E e := by
      intro j hj
      refine ⟨?_, ?_⟩
      · rw [← (hK j hj).1]
        exact S3Geom.mem_comp_self (hroot1 j hj)
      · rw [← (hK j hj).2]
        exact S3Geom.mem_comp_self (hexit1 j hj)
    -- (W1) on the entry's level-1 component
    have hintK : ∀ k ∈ G.comp (S3Geom.level1Set (S.resid E) a0) a1 e, Interior (S.cluster E a0 k) := by
      intro k hk c hc hdecl
      have hk' : k ∈ S.lev1comp a0 a1 E e := hk
      have hsub := S.comp1_subset_family (a0 := a0) (a1 := a1) (E := E) hk'
      have hek : e ∈ S.family a0 a1 E k := hsub (S3Geom.mem_comp_self he)
      have hfk : S.family a0 a1 E k = S.family a0 a1 E e := (S.family_eq_of_mem hek).symm
      have hkk : k ∈ S.family a0 a1 E k := S.mem_family_self (S.badD_of_lev1 (S3Geom.comp_subset hk'))
      have hcf : c ∈ S.family a0 a1 E e := by
        rw [← hfk, ← S.family_eq_of_mem hkk]
        exact S.mem_family_of_cluster (S.badD_of_lev1 (S3Geom.comp_subset hk')) hc
      have h1 := hint c hcf
      have hhs1 : 1 ≤ hs a1 := by simp [hs]
      rcases hdecl with h | h <;> omega
    have hparity : ∑ v, G.restrictTo (G.comp (S3Geom.level1Set (S.resid E) a0) a1 e) (S.resid E) v ≠ 0 :=
      fun h => hodd (Or.inl h)
    obtain ⟨c'', hc''1, ⟨k, hk, hc''k⟩, hfar⟩ := S.W1 ha0 Z hintK hparity
    by_cases hon : ∃ j ≤ n, c'' ∈ S.cluster E a0 (f j).1
    · -- case α': W1's block lies in a route cluster
      left
      obtain ⟨j, hj, hcj⟩ := hon
      obtain ⟨b', hb', hdb⟩ := hcov j hj c'' hcj
      refine ⟨j, hj, b', hb', ?_⟩
      have hf := hfar (f j).1 (hmemK j hj).1
      have t := G.blockDist_triangle (f j).1 b' c''
      rw [G.blockDist_comm b'] at t
      omega
    · -- case β: off the route
      right
      push Not at hon
      exact ⟨hmemK, c'', hc''1, hon, ⟨k, hk, hc''k⟩, hfar⟩

/-! ### Case β: the excursion -/

/-- **A shortest chain keeping its blocks in `T` and its later clusters out of `R`** has distinct clusters. -/
theorem exists_min_fchain_gen {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e x : G.Block} (T : Set G.Block)
    (R : Set (Set G.Block))
    (hex : ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e x n f ∧
      (∀ i ≤ n, (f i).1 ∈ T ∧ (f i).2 ∈ T) ∧ ∀ i, 1 ≤ i → i ≤ n → S.cluster E a0 (f i).1 ∉ R) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e x n f ∧
      (∀ i ≤ n, (f i).1 ∈ T ∧ (f i).2 ∈ T) ∧ (∀ i, 1 ≤ i → i ≤ n → S.cluster E a0 (f i).1 ∉ R) ∧
      ∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1 := by
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → G.Block × G.Block, S.FChain a0 a1 E e x m g ∧
      (∀ i ≤ m, (g i).1 ∈ T ∧ (g i).2 ∈ T) ∧ ∀ i, 1 ≤ i → i ≤ m → S.cluster E a0 (g i).1 ∉ R) →
      Nat.find hex ≤ m := fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨⟨hP, hL, h0, hn⟩, hT, hR⟩ := hf
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, hT, hR, ?_⟩
  intro i j hij hjn hcl
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧
      g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
    ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
      fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
  have hg : S.FChain a0 a1 E e x (n - (j - i)) g := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        exact hP k (by omega)
      · rw [h, hg2]
        obtain ⟨hei, _, _⟩ := hP i (by omega)
        obtain ⟨_, hxj, hclj⟩ := hP j hjn
        exact ⟨hei, hxj, hcl.trans hclj⟩
      · rw [hg3 k h]
        exact hP _ (by omega)
    · rcases lt_trichotomy k i with h | h | h
      · rw [hg1 k h]
        rcases (show k + 1 < i ∨ k + 1 = i by omega) with h' | h'
        · rw [hg1 (k + 1) h']
          exact hL k (by omega)
        · rw [h', hg2]
          have := hL k (by omega)
          rw [h'] at this
          exact this
      · rw [h, hg2, hg3 (i + 1) (by omega), show i + 1 + (j - i) = j + 1 by omega]
        exact hL j (by omega)
      · rw [hg3 k h, hg3 (k + 1) (by omega), show k + 1 + (j - i) = k + (j - i) + 1 by omega]
        exact hL _ (by omega)
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [hg2]
        exact h0
      · rw [hg1 0 h]
        exact h0
    · rcases eq_or_lt_of_le (show i ≤ n - (j - i) by omega) with h | h
      · rw [← h, hg2, show j = n by omega]
        exact hn
      · rw [hg3 _ h, show n - (j - i) + (j - i) = n by omega]
        exact hn
  have hgT : ∀ k ≤ n - (j - i), (g k).1 ∈ T ∧ (g k).2 ∈ T := by
    intro k hk
    rcases lt_trichotomy k i with h | h | h
    · rw [hg1 k h]
      exact hT k (by omega)
    · rw [h, hg2]
      exact ⟨(hT i (by omega)).1, (hT j hjn).2⟩
    · rw [hg3 k h]
      exact hT _ (by omega)
  have hgR : ∀ k, 1 ≤ k → k ≤ n - (j - i) → S.cluster E a0 (g k).1 ∉ R := by
    intro k hk1 hk
    rcases lt_trichotomy k i with h | h | h
    · rw [hg1 k h]
      exact hR k hk1 (by omega)
    · rw [h, hg2]
      exact hR i (by omega) (by omega)
    · rw [hg3 k h]
      exact hR _ (by omega) (by omega)
  have := hmin _ ⟨g, hg, hgT, hgR⟩
  omega

/-- **A chain through a level-1 component**: blocks of one level-1 component are joined by a chain of trivial pairs
`(b, b)` of blocks of the component, consecutive ones at distance at most `a1`. -/
theorem exists_kchain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e k : G.Block} (he : e ∈ S.lev1 a0 E)
    (hk : k ∈ S.lev1comp a0 a1 E e) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.FChain a0 a1 E e k n f ∧
      ∀ i ≤ n, (f i).1 ∈ S.lev1comp a0 a1 E e ∧ (f i).2 ∈ S.lev1comp a0 a1 E e := by
  obtain ⟨_, hpath⟩ := hk
  induction hpath with
  | refl =>
    refine ⟨0, fun _ => (e, e), ⟨fun _ _ => ⟨S.badD_of_lev1 he, S.badD_of_lev1 he, rfl⟩,
      fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩, fun _ _ => ⟨S3Geom.mem_comp_self he,
      S3Geom.mem_comp_self he⟩⟩
  | @tail b b' hb hbb ih =>
    obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hK⟩ := ih
    obtain ⟨hb1, hb'1, hd⟩ := hbb
    have hb'K : b' ∈ S.lev1comp a0 a1 E e := ⟨he, hb.tail ⟨hb1, hb'1, hd⟩⟩
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k, k ≠ n + 1 → g k = f k) ∧ g (n + 1) = (b', b') :=
      ⟨fun k => if k = n + 1 then (b', b') else f k, fun k hk => by simp [hk], by simp⟩
    refine ⟨n + 1, g, ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩, fun i hi => ?_⟩
    · rcases eq_or_ne i (n + 1) with h | h
      · rw [h, hg2]
        exact ⟨S.badD_of_lev1 hb'1, S.badD_of_lev1 hb'1, rfl⟩
      · rw [hg1 i h]
        exact hP i (by omega)
    · rw [hg1 i (by omega)]
      rcases eq_or_ne i n with h | h
      · rw [h, hg2, hn]
        exact ⟨hb1, hb'1, hd⟩
      · rw [hg1 (i + 1) (by omega)]
        exact hL i (by omega)
    · rw [hg1 0 (by omega)]
      exact h0
    · rw [hg2]
    · rcases eq_or_ne i (n + 1) with h | h
      · rw [h, hg2]
        exact ⟨hb'K, hb'K⟩
      · rw [hg1 i h]
        exact hK i (by omega)

/-- **The excursion chain** (case β): from a route cluster `C_x` through the level-1 component `K`
of the entry to the cluster of W1's block `c''`, the clusters after `C_x` off the route and pairwise distinct. -/
theorem exc_chain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e x : G.Block} (he : e ∈ S.lev1 a0 E)
    {n : ℕ} {f : ℕ → G.Block × G.Block} (hfch : S.FChain a0 a1 E e x n f)
    {c'' k : G.Block} (hoff : ∀ j ≤ n, c'' ∉ S.cluster E a0 (f j).1) (hk : k ∈ S.lev1comp a0 a1 E e)
    (hc''k : c'' ∈ S.cluster E a0 k) :
    ∃ (jx p : ℕ) (h : ℕ → G.Block × G.Block), jx ≤ n ∧ 1 ≤ p ∧
      S.FChain a0 a1 E (h 0).1 k p h ∧ (h 0).1 ∈ S.cluster E a0 (f jx).1 ∧
      (∀ t ≤ p, (h t).1 ∈ S.lev1comp a0 a1 E e ∧ (h t).2 ∈ S.lev1comp a0 a1 E e) ∧
      (∀ t, 1 ≤ t → t ≤ p → ∀ j ≤ n, S.cluster E a0 (h t).1 ≠ S.cluster E a0 (f j).1) ∧
      ∀ t t', t < t' → t' ≤ p → S.cluster E a0 (h t).1 ≠ S.cluster E a0 (h t').1 := by
  obtain ⟨hP, hL, h0, hn⟩ := hfch
  obtain ⟨nk, g, ⟨hgP, hgL, hg0, hgn⟩, hgK⟩ := S.exists_kchain he hk
  -- the cluster of `k` is off the route
  have hkoff : ∀ j ≤ n, S.cluster E a0 k ≠ S.cluster E a0 (f j).1 := by
    intro j hj hkj
    apply hoff j hj
    rw [← hkj]
    exact hc''k
  -- the last pair of the chain in a route cluster
  let P : ℕ → Prop := fun t => ∃ j ≤ n, S.cluster E a0 (g t).1 = S.cluster E a0 (f j).1
  obtain ⟨jl, hjl⟩ : ∃ jl, Nat.findGreatest P nk = jl := ⟨_, rfl⟩
  have hjlN : jl ≤ nk := hjl ▸ Nat.findGreatest_le _
  have hjlmax : ∀ t, t ≤ nk → P t → t ≤ jl := fun t ht hPt => hjl ▸ Nat.le_findGreatest ht hPt
  have hP0 : P 0 := ⟨0, Nat.zero_le _, by rw [hg0, h0]⟩
  have hPjl : P jl := by
    by_cases hz : jl = 0
    · rw [hz]
      exact hP0
    · exact Nat.findGreatest_of_ne_zero hjl hz
  have hclk : ∀ t ≤ nk, S.cluster E a0 (g t).1 = S.cluster E a0 (g t).2 := fun t ht => (hgP t ht).2.2
  have hjlt : jl < nk := by
    rcases eq_or_lt_of_le hjlN with h | h
    · exfalso
      obtain ⟨j, hj, hcj⟩ := hPjl
      rw [h, hclk nk le_rfl, hgn] at hcj
      exact hkoff j hj hcj
    · exact h
  -- the sub-chain after it, then a shortest one
  have hsub : ∃ (m : ℕ) (g' : ℕ → G.Block × G.Block), S.FChain a0 a1 E (g jl).1 k m g' ∧
      (∀ t ≤ m, (g' t).1 ∈ S.lev1comp a0 a1 E e ∧ (g' t).2 ∈ S.lev1comp a0 a1 E e) ∧
      ∀ t, 1 ≤ t → t ≤ m → S.cluster E a0 (g' t).1 ∉ {C | ∃ j ≤ n, C = S.cluster E a0 (f j).1} := by
    refine ⟨nk - jl, fun t => g (jl + t), ⟨fun t ht => hgP _ (by omega), fun t ht => ?_, by simp, ?_⟩,
      fun t ht => hgK _ (by omega), fun t ht1 ht => ?_⟩
    · have := hgL (jl + t) (by omega)
      rwa [show jl + t + 1 = jl + (t + 1) by omega] at this
    · simp only
      rw [show jl + (nk - jl) = nk by omega]
      exact hgn
    · rintro ⟨j, hj, hcj⟩
      have := hjlmax (jl + t) (by omega) ⟨j, hj, hcj⟩
      omega
  obtain ⟨p, h, ⟨hhP, hhL, hh0, hhn⟩, hhK, hhR, hhd⟩ :=
    S.exists_min_fchain_gen (S.lev1comp a0 a1 E e) {C | ∃ j ≤ n, C = S.cluster E a0 (f j).1} hsub
  obtain ⟨jx, hjx, hcjx⟩ := hPjl
  have hp1 : 1 ≤ p := by
    by_contra hp
    have hp0 : p = 0 := by omega
    have hc0 := (hhP 0 (by omega)).2.2
    rw [hh0, ← hp0, hhn] at hc0
    exact hkoff jx hjx (hc0.symm.trans hcjx)
  refine ⟨jx, p, h, hjx, hp1, ⟨hhP, hhL, rfl, hhn⟩, ?_, hhK, fun t ht1 ht j hj hcj => hhR t ht1 ht ⟨j, hj, hcj⟩,
    hhd⟩
  rw [hh0, ← hcjx]
  exact S.mem_cluster_self (hgP jl hjlN).1

/-- Blocks of the level-1 component of `e`, and their clusters, lie in the family of `e`. -/
theorem lev1comp_cluster_family {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {e k : G.Block} (he : e ∈ S.lev1 a0 E)
    (hk : k ∈ S.lev1comp a0 a1 E e) : ∀ c ∈ S.cluster E a0 k, c ∈ S.family a0 a1 E e := by
  have hk1 : k ∈ S.lev1 a0 E := S3Geom.comp_subset hk
  have hsub := S.comp1_subset_family (a0 := a0) (a1 := a1) (E := E) hk
  have hek : e ∈ S.family a0 a1 E k := hsub (S3Geom.mem_comp_self he)
  have hfk : S.family a0 a1 E k = S.family a0 a1 E e := (S.family_eq_of_mem hek).symm
  intro c hc
  rw [← hfk]
  exact S.mem_family_of_cluster (S.badD_of_lev1 hk1) hc

/-- **The last common node**: two lists starting with the same element split as a node `x` of the first list,
followed in the second list by a walk avoiding the first list. -/
theorem branch_split {α : Type*} (p q : List α) {r : α} (hr : r ∈ p) (hq : q.head? = some r) :
    ∃ pre x w, q = pre ++ x :: w ∧ x ∈ p ∧ ∀ z ∈ w, z ∉ p := by
  obtain ⟨_ | ⟨r', qs⟩, hq'⟩ : ∃ q', q' = q := ⟨q, rfl⟩
  · subst hq'
    simp at hq
  · subst hq'
    simp only [List.head?_cons, Option.some.injEq] at hq
    subst hq
    obtain ⟨pre, x, w, hsplit, hx, hw⟩ := S3Geom.exists_last_split (· ∈ p) r' qs hr
    exact ⟨pre, x, w, hsplit, hx, hw⟩

/-- **The excursion route** (case β): the route of the off-route part of the excursion chain, its last exit replaced
by W1's block `c''`; its last route part spans at least `a1 + 2 - D` from its root. -/
theorem exc_route {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) {E : G.Ed → ZMod 2}
    {e x : G.Block} (he : e ∈ S.lev1 a0 E)
    (hint : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny)
    {n : ℕ} {f : ℕ → G.Block × G.Block} (hfch : S.FChain a0 a1 E e x n f)
    {c'' k : G.Block} (hc''1 : c'' ∈ S.lev1 a0 E) (hoff : ∀ j ≤ n, c'' ∉ S.cluster E a0 (f j).1)
    (hk : k ∈ S.lev1comp a0 a1 E e) (hc''k : c'' ∈ S.cluster E a0 k)
    (hfar : ∀ k' ∈ S.lev1comp a0 a1 E e, a1 < G.blockDist k' c'') :
    ∃ (jx p : ℕ) (h : ℕ → G.Block × G.Block) (Sel : ℕ → Finset G.Block) (rest : ℕ → List G.Block)
      (sEnd : ℕ → G.Block) (ms : List G.Move),
      jx ≤ n ∧ 1 ≤ p ∧ S.FChain a0 a1 E (h 0).1 k p h ∧ (h 0).1 ∈ S.cluster E a0 (f jx).1 ∧
      (∀ t ≤ p, (h t).1 ∈ S.lev1comp a0 a1 E e ∧ (h t).2 ∈ S.lev1comp a0 a1 E e) ∧
      (∀ t, 1 ≤ t → t ≤ p → ∀ j ≤ n, S.cluster E a0 (h t).1 ≠ S.cluster E a0 (f j).1) ∧
      (∀ t t', t < t' → t' ≤ p → S.cluster E a0 (h t).1 ≠ S.cluster E a0 (h t').1) ∧
      (∀ i ≤ p - 1, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (h (i + 1)).1) ∧
        (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        ((h (i + 1)).1 :: rest i).Nodup ∧ (∀ b ∈ (h (i + 1)).1 :: rest i, b ∈ Sel i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((h (i + 1)).1 :: rest i) ∧
        ((h (i + 1)).1 :: rest i).getLast? = some (sEnd i)) ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (h 1).1 ms ∧
      (∀ m ∈ ms, G.D ≤ G.blockDist (h 1).1 m.blk) ∧ ms ≠ [] ∧
      (∀ m ∈ ms.head?, ¬ m.isLink) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ i ≤ p - 1, m.blk ∈ Sel i) ∧ S3Geom.endBlock (h 1).1 ms = sEnd (p - 1) ∧
      a1 + 2 - G.D ≤ G.blockDist (h p).1 (sEnd (p - 1)) := by
  obtain ⟨jx, p, h, hjx, hp1, ⟨hhP, hhL, hh0, hhn⟩, hjxc, hhK, hhoff, hhd⟩ := S.exc_chain he hfch hoff hk hc''k
  -- the shifted chain, last exit `c''`
  obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ t, t ≠ p - 1 → g t = h (t + 1)) ∧
      g (p - 1) = ((h p).1, c'') :=
    ⟨fun t => if t = p - 1 then ((h p).1, c'') else h (t + 1), fun t ht => by simp [ht], by simp⟩
  have hclp : S.cluster E a0 (h p).1 = S.cluster E a0 k := by
    have := (hhP p le_rfl).2.2
    rwa [hhn] at this
  have hc''bad : S.badD E c'' := S.badD_of_lev1 hc''1
  have hclc : S.cluster E a0 c'' = S.cluster E a0 k := S3Geom.comp_eq_of_mem hc''k
  have hg1st : ∀ t ≤ p - 1, (g t).1 = (h (t + 1)).1 := by
    intro t ht
    rcases eq_or_ne t (p - 1) with h' | h'
    · rw [h', hg2, show p - 1 + 1 = p by omega]
    · rw [hg1 t h']
  have hgP : ∀ t ≤ p - 1, S.PairOK a0 E (g t) := by
    intro t ht
    rcases eq_or_ne t (p - 1) with h' | h'
    · rw [h', hg2]
      exact ⟨(hhP p le_rfl).1, hc''bad, hclp.trans hclc.symm⟩
    · rw [hg1 t h']
      exact hhP _ (by omega)
  have hgL : ∀ t < p - 1, S.LinkOK a0 a1 E (g t).2 (g (t + 1)).1 := by
    intro t ht
    rw [hg1 t (by omega), hg1st (t + 1) (by omega)]
    exact hhL (t + 1) (by omega)
  have hg0 : (g 0).1 = (h 1).1 := hg1st 0 (by omega)
  have hh1lev : (h 1).1 ∈ S.lev1 a0 E := by
    have := (hhL 0 (by omega)).2.1
    simpa using this
  have hgd : ∀ i j, i < j → j ≤ p - 1 → S.cluster E a0 (g i).1 ≠ S.cluster E a0 (g j).1 := by
    intro i j hij hj
    rw [hg1st i (by omega), hg1st j hj]
    exact hhd (i + 1) (j + 1) (by omega) (by omega)
  have hgrow : ∀ i ≤ p - 1, ∀ c ∈ S.cluster E a0 (g i).1, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny := by
    intro i hi c hc
    rw [hg1st i hi] at hc
    exact hint c (S.lev1comp_cluster_family he (hhK (i + 1) (by omega)).1 c hc)
  obtain ⟨Sel, rest, sEnd, ms, hdat, hfrag, hm0, hne, hhead, hlast, hblk, hend⟩ :=
    S.route_of_chain ha0 hD1 hDa hh1lev hgP hgL hg0 hgd hgrow
  refine ⟨jx, p, h, Sel, rest, sEnd, ms, hjx, hp1, ⟨hhP, hhL, hh0, hhn⟩, hjxc, hhK, hhoff, hhd, ?_, hfrag, hm0,
    hne, hhead, hlast, hblk, hend, ?_⟩
  · intro i hi
    obtain ⟨hSK, hsep, -, -, hnd, hmem, hch, hlastP, -⟩ := hdat i hi
    rw [hg1st i hi] at hSK hnd hmem hch hlastP
    exact ⟨hSK, hsep, hnd, hmem, hch, hlastP⟩
  · -- the last route part spans at least `a1 + 2 - D`
    obtain ⟨-, -, -, -, -, -, -, -, hcov⟩ := hdat (p - 1) le_rfl
    rw [hg2] at hcov
    dsimp only at hcov
    have hf := hfar (h p).1 (hhK p le_rfl).1
    have t := G.blockDist_triangle (h p).1 (sEnd (p - 1)) c''
    rw [G.blockDist_comm (sEnd (p - 1))] at t
    omega

/-- A selected walk from a route node, avoiding the route part: from a path of the selection starting at the root,
split at its last common node with the route part. -/
theorem sel_branch {a0 : ℕ} {Sel : Finset G.Block} {r b' : G.Block} {route : List G.Block}
    (hsep : ∀ b ∈ Sel, ∀ b' ∈ Sel, b ≠ b' → G.D ≤ G.blockDist b b')
    (hconn : ∀ b ∈ Sel, Relation.ReflTransGen
      (fun y z => y ∈ Sel ∧ z ∈ Sel ∧ G.blockDist y z ≤ G.D - 1 + a0) r b)
    (hrS : r ∈ Sel) (hb'S : b' ∈ Sel) (hr : r ∈ route) :
    ∃ xb w, xb ∈ route ∧ (∀ b ∈ w, b ∈ Sel ∧ b ∉ route) ∧
      List.IsChain (fun y z => G.D ≤ G.blockDist y z ∧ G.blockDist y z ≤ G.D - 1 + a0) (xb :: w) ∧
      (xb :: w).getLast? = some b' := by
  obtain ⟨q, hqh, hql, hqnd, hqS, hqch⟩ := S3Geom.exists_simple_path hrS (hconn b' hb'S)
  obtain ⟨pre, xb, w, hsplit, hx, hw⟩ := branch_split route q hr hqh
  have hch' : List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) (xb :: w) := by
    rw [hsplit] at hqch
    exact hqch.right_of_append
  have hmemq : ∀ b ∈ xb :: w, b ∈ q := fun b hb => by
    rw [hsplit]
    exact List.mem_append_right pre hb
  refine ⟨xb, w, hx, fun b hb => ⟨hqS b (hmemq b (List.mem_cons_of_mem _ hb)), hw b hb⟩,
    hch'.imp_of_mem_imp fun y z hy hz hyz => ⟨hsep y (hqS y (hmemq y hy)) z (hqS z (hmemq z hz)) hyz.1, hyz.2⟩, ?_⟩
  rw [hsplit, S3Geom.getLast?_append_cons] at hql
  exact hql

/-- **The skeleton of an intermediate family**: the route of `fam_route` and a witness of
span at least `a1 + 2 - D`, in one of three forms: (A) a block of a route part far from its root; (A') a selected walk
branching from a route part, avoiding it, ending far from the root of its cluster; (B) an excursion: a selected walk
branching from a route part of a route cluster, a link to an off-route cluster, and the route of the off-route chain,
whose last route part spans at least `a1 + 2 - D` from its root. -/
theorem fam_skeleton {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) (Z : Solver G)
    {E : G.Ed → ZMod 2} {e x : G.Block} (he : e ∈ S.lev1 a0 E)
    (hodd : ¬ G.resolved (S.resid E) ((a1 + 1) / 2) (S.lev1comp a0 a1 E e))
    (hx : x ∈ S.family a0 a1 E e) (hx1 : x ∈ S.lev1 a0 E)
    (hint : ∀ c ∈ S.family a0 a1 E e, hs a1 < c.2.val ∧ c.2.val + 1 + hs a1 < G.ny) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block) (Sel : ℕ → Finset G.Block) (rest : ℕ → List G.Block)
      (sEnd : ℕ → G.Block) (ms : List G.Move),
      S.FChain a0 a1 E e x n f ∧
      (∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1) ∧
      (∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
        (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
        ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
        List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
        ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1) ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) e ms ∧
      (∀ m ∈ ms, G.D ≤ G.blockDist e m.blk) ∧ ms ≠ [] ∧
      (∀ m ∈ ms.head?, ¬ m.isLink) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ i ≤ n, m.blk ∈ Sel i) ∧ S3Geom.endBlock e ms = sEnd n ∧
      -- the witness
      ((∃ j ≤ n, ∃ b' ∈ (f j).1 :: rest j, a1 + 2 - G.D ≤ G.blockDist (f j).1 b') ∨
       (∃ j ≤ n, ∃ xb w, xb ∈ (f j).1 :: rest j ∧ w ≠ [] ∧ (∀ b ∈ w, b ∈ Sel j ∧ b ∉ (f j).1 :: rest j) ∧
          List.IsChain (fun y z => G.D ≤ G.blockDist y z ∧ G.blockDist y z ≤ G.D - 1 + a0) (xb :: w) ∧
          ∃ b', (xb :: w).getLast? = some b' ∧ a1 + 2 - G.D ≤ G.blockDist (f j).1 b') ∨
       (∃ jx ≤ n, ∃ xb w, xb ∈ (f jx).1 :: rest jx ∧ (∀ b ∈ w, b ∈ Sel jx ∧ b ∉ (f jx).1 :: rest jx) ∧
          List.IsChain (fun y z => G.D ≤ G.blockDist y z ∧ G.blockDist y z ≤ G.D - 1 + a0) (xb :: w) ∧
          ∃ (sx : G.Block) (p : ℕ) (h : ℕ → G.Block × G.Block) (Sel' : ℕ → Finset G.Block)
            (rest' : ℕ → List G.Block) (sEnd' : ℕ → G.Block) (ems : List G.Move),
            (xb :: w).getLast? = some sx ∧ 1 ≤ p ∧
            G.D ≤ G.blockDist sx (h 1).1 ∧ G.blockDist sx (h 1).1 ≤ G.D - 1 + a1 ∧
            (∀ t, 1 ≤ t → t ≤ p → ∀ j ≤ n, S.cluster E a0 (h t).1 ≠ S.cluster E a0 (f j).1) ∧
            (∀ t t', 1 ≤ t → t < t' → t' ≤ p → S.cluster E a0 (h t).1 ≠ S.cluster E a0 (h t').1) ∧
            (∀ i ≤ p - 1, (∀ b ∈ Sel' i, b ∈ S.cluster E a0 (h (i + 1)).1) ∧
              (∀ b ∈ Sel' i, ∀ b' ∈ Sel' i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
              ((h (i + 1)).1 :: rest' i).Nodup ∧ (∀ b ∈ (h (i + 1)).1 :: rest' i, b ∈ Sel' i) ∧
              List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((h (i + 1)).1 :: rest' i) ∧
              ((h (i + 1)).1 :: rest' i).getLast? = some (sEnd' i)) ∧
            S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) (h 1).1 ems ∧
            (∀ m ∈ ems, G.D ≤ G.blockDist (h 1).1 m.blk) ∧
            (∀ m ∈ ems, ∃ i ≤ p - 1, m.blk ∈ Sel' i) ∧
            S3Geom.endBlock (h 1).1 ems = sEnd' (p - 1) ∧
            a1 + 2 - G.D ≤ G.blockDist (h p).1 (sEnd' (p - 1)))) := by
  obtain ⟨n, f, Sel, rest, sEnd, ms, hfch, hdist, hdat, hfrag, hm0, hne, hhead, hlast, hblk, hend⟩ :=
    S.fam_route ha0 hD1 hDa he hx hint
  have hdat' : ∀ i ≤ n, (∀ b ∈ Sel i, b ∈ S.cluster E a0 (f i).1) ∧
      (∀ b ∈ Sel i, ∀ b' ∈ Sel i, b ≠ b' → G.D ≤ G.blockDist b b') ∧
      ((f i).1 :: rest i).Nodup ∧ (∀ b ∈ (f i).1 :: rest i, b ∈ Sel i) ∧
      List.IsChain (fun y z => y ≠ z ∧ G.blockDist y z ≤ G.D - 1 + a0) ((f i).1 :: rest i) ∧
      ((f i).1 :: rest i).getLast? = some (sEnd i) ∧ G.blockDist (f i).2 (sEnd i) ≤ G.D - 1 := by
    intro i hi
    obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9⟩ := hdat i hi
    exact ⟨h1, h2, h5, h6, h7, h8, h9⟩
  refine ⟨n, f, Sel, rest, sEnd, ms, hfch, hdist, hdat', hfrag, hm0, hne, hhead, hlast, hblk, hend, ?_⟩
  have hcov : ∀ j ≤ n, ∀ c ∈ S.cluster E a0 (f j).1, ∃ b ∈ Sel j, G.blockDist c b ≤ G.D - 1 :=
    fun j hj => (hdat j hj).2.2.2.1
  have hsEnd : ∀ j ≤ n, sEnd j ∈ Sel j ∧ G.blockDist (f j).2 (sEnd j) ≤ G.D - 1 := fun j hj =>
    ⟨(hdat j hj).2.2.2.2.2.1 _ (List.mem_of_getLast? (hdat j hj).2.2.2.2.2.2.2.1), (hdat j hj).2.2.2.2.2.2.2.2⟩
  rcases S.fam_witness ha0 hD1 Z he hodd hx1 hint hfch hcov hsEnd with ⟨j, hj, b', hb', hfar⟩ |
    ⟨hmemK, c'', hc''1, hoff, ⟨k, hk, hc''k⟩, hfarK⟩
  · -- (A) or (A'): split the selected path from the root to `b'` at its last common node with the route part
    obtain ⟨-, hsep, hconn, -, -, hmem, -, -, -⟩ := hdat j hj
    obtain ⟨xb, w, hxb, hw, hch, hlastw⟩ := sel_branch (a0 := a0) hsep hconn (hmem _ List.mem_cons_self) hb'
      (List.mem_cons_self : (f j).1 ∈ (f j).1 :: rest j)
    by_cases hw0 : w = []
    · left
      subst hw0
      simp only [List.getLast?_singleton, Option.some.injEq] at hlastw
      subst hlastw
      exact ⟨j, hj, xb, hxb, hfar⟩
    · right; left
      exact ⟨j, hj, xb, w, hxb, hw0, hw, hch, b', hlastw, hfar⟩
  · -- (B): the excursion
    right; right
    obtain ⟨jx, p, h, Sel', rest', sEnd', ems, hjx, hp1, ⟨hhP, hhL, _, _⟩, hjxc, hhK, hhoff, hhd, hdat'',
      hfrag', hm0', -, -, -, hblk', hend', hspan⟩ :=
      S.exc_route ha0 hD1 hDa he hint hfch hc''1 hoff hk hc''k hfarK
    obtain ⟨hSK, hsep, hconn, hcovx, -, hmem, -, -, -⟩ := hdat jx hjx
    -- the exit of the excursion's first pair lies in the route cluster `C_x`; its cover
    have hh0x : (h 0).2 ∈ S.cluster E a0 (f jx).1 := by
      have hc0 := (hhP 0 (by omega)).2.2
      have h1 : S.cluster E a0 (h 0).1 = S.cluster E a0 (f jx).1 := S3Geom.comp_eq_of_mem hjxc
      rw [← h1, hc0]
      exact S.mem_cluster_self (hhP 0 (by omega)).2.1
    obtain ⟨sx, hsxS, hsxd⟩ := hcovx (h 0).2 hh0x
    obtain ⟨xb, w, hxb, hw, hch, hlastw⟩ := sel_branch (a0 := a0) hsep hconn (hmem _ List.mem_cons_self) hsxS
      (List.mem_cons_self : (f jx).1 ∈ (f jx).1 :: rest jx)
    refine ⟨jx, hjx, xb, w, hxb, hw, hch, sx, p, h, Sel', rest', sEnd', ems, hlastw, hp1, ?_, ?_, hhoff,
      fun t t' _ htt' ht' => hhd t t' htt' ht', hdat'', hfrag', hm0', hblk', hend', hspan⟩
    · -- the link starts in a route cluster and ends off the route: more than `a0` apart
      have hsxK : sx ∈ S.cluster E a0 (f jx).1 := hSK sx hsxS
      have hh1K : (h 1).1 ∈ S.cluster E a0 (h 1).1 := S.mem_cluster_self (hhP 1 hp1).1
      have := S.cluster_sep hsxK hh1K (fun hc => hhoff 1 le_rfl hp1 jx hjx hc.symm)
      omega
    · have t := G.blockDist_triangle sx (h 0).2 (h 1).1
      have t2 : G.blockDist (h 0).2 (h 1).1 ≤ a1 := (hhL 0 (by omega)).2.2
      rw [G.blockDist_comm sx (h 0).2] at t
      omega

/-! ### The ends: routes in the end families -/

/-- Level-1 blocks lie in the sampled rows `2 … n_y - 3` (their level-0 component is unresolved, so its region misses
the rough rows). -/
theorem lev1_rows {a0 : ℕ} (ha0 : 1 ≤ a0) {E : G.Ed → ZMod 2} {c : G.Block} (hc : c ∈ S.lev1 a0 E) :
    2 ≤ c.2.val ∧ c.2.val + 3 ≤ G.ny := by
  obtain ⟨hfl, hunres⟩ := hc
  have hr : 1 ≤ (a0 + 1) / 2 := by omega
  have hcK : c ∈ G.comp (S3Geom.flaggedSet (S3Geom.residD S (psyn G.w G.h E))) a0 c := S3Geom.mem_comp_self hfl
  have hL := G.hL
  have hcol : c.1.val * G.L < G.w + 1 := by
    have := c.1.isLt
    have hw := G.w_succ
    have : c.1.val * G.L + G.L ≤ G.nx * G.L := by nlinarith
    omega
  have hbcol : G.bcol ⟨c.1.val * G.L, hcol⟩ = c.1 := by
    apply Fin.ext
    simp only [S3Geom.bcol]
    exact Nat.mul_div_cancel _ hL
  constructor
  · by_contra hlow
    apply hunres
    refine Or.inr (Or.inl ⟨(⟨c.1.val * G.L, hcol⟩, 0), ⟨c, hcK, ?_⟩, Or.inl rfl⟩)
    simp only [S3Geom.blockDist, S3Geom.blockOf, hbcol, S3Geom.brow, ndist]
    simp only [Fin.val_zero, Nat.zero_div]
    omega
  · by_contra hhigh
    apply hunres
    refine Or.inr (Or.inl ⟨(⟨c.1.val * G.L, hcol⟩, Fin.last _), ⟨c, hcK, ?_⟩, Or.inr rfl⟩)
    have htop := top_row (G := G) ⟨c.1.val * G.L, hcol⟩
    have hlt : (G.blockOf ((⟨c.1.val * G.L, hcol⟩, Fin.last G.h) : G.V)).2.val < G.ny :=
      (G.blockOf ((⟨c.1.val * G.L, hcol⟩, Fin.last G.h) : G.V)).2.isLt
    have hc2 := c.2.isLt
    simp only [S3Geom.blockDist, ndist]
    have hb1 : (G.blockOf ((⟨c.1.val * G.L, hcol⟩, Fin.last G.h) : G.V)).1 = c.1 := hbcol
    rw [hb1]
    omega

/-- A cluster chain whose first entry satisfies `Pst` and whose last exit satisfies `Pen`. -/
def GChain (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (Pst Pen : G.Block → Prop) (n : ℕ) (f : ℕ → G.Block × G.Block) :
    Prop :=
  (∀ i ≤ n, S.PairOK a0 E (f i)) ∧ (∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1) ∧ Pst (f 0).1 ∧ Pen (f n).2

/-- **A shortest chain between block properties** has distinct clusters, no `Pst`-block after its first cluster, and
no `Pen`-block before its last cluster. -/
theorem exists_min_gchain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {Pst Pen : G.Block → Prop}
    (hex : ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.GChain a0 a1 E Pst Pen n f) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.GChain a0 a1 E Pst Pen n f ∧
      (∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ c ∈ S.cluster E a0 (f i).1, ¬ Pst c) ∧
      (∀ i, i < n → ∀ c ∈ S.cluster E a0 (f i).1, ¬ Pen c) := by
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → G.Block × G.Block, S.GChain a0 a1 E Pst Pen m g) → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨hP, hL, h0, hn⟩ := hf
  have hmemcl : ∀ i, ∀ c ∈ S.cluster E a0 (f i).1,
      S.badD E c ∧ S.cluster E a0 c = S.cluster E a0 (f i).1 := fun i c hc =>
    ⟨S3Geom.comp_subset hc, S3Geom.comp_eq_of_mem hc⟩
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, ?_, ?_, ?_⟩
  · intro i j hij hjn hcl
    obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧
        g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
      ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
        fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
    have hg : S.GChain a0 a1 E Pst Pen (n - (j - i)) g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases lt_trichotomy k i with h | h | h
        · rw [hg1 k h]
          exact hP k (by omega)
        · rw [h, hg2]
          obtain ⟨hei, _, _⟩ := hP i (by omega)
          obtain ⟨_, hxj, hclj⟩ := hP j hjn
          exact ⟨hei, hxj, hcl.trans hclj⟩
        · rw [hg3 k h]
          exact hP _ (by omega)
      · rcases lt_trichotomy k i with h | h | h
        · rw [hg1 k h]
          rcases (show k + 1 < i ∨ k + 1 = i by omega) with h' | h'
          · rw [hg1 (k + 1) h']
            exact hL k (by omega)
          · rw [h', hg2]
            have := hL k (by omega)
            rw [h'] at this
            exact this
        · rw [h, hg2, hg3 (i + 1) (by omega), show i + 1 + (j - i) = j + 1 by omega]
          exact hL j (by omega)
        · rw [hg3 k h, hg3 (k + 1) (by omega), show k + 1 + (j - i) = k + (j - i) + 1 by omega]
          exact hL _ (by omega)
      · rcases Nat.eq_zero_or_pos i with h | h
        · subst h
          rw [hg2]
          exact h0
        · rw [hg1 0 h]
          exact h0
      · rcases eq_or_lt_of_le (show i ≤ n - (j - i) by omega) with h | h
        · rw [← h, hg2, show j = n by omega]
          exact hn
        · rw [hg3 _ h, show n - (j - i) + (j - i) = n by omega]
          exact hn
    have := hmin _ ⟨g, hg⟩
    omega
  · intro i hi1 hin c hc hpc
    obtain ⟨hcbad, hccl⟩ := hmemcl i c hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, g 0 = (c, (f i).2) ∧ ∀ k, 0 < k → g k = f (i + k) :=
      ⟨fun k => if k = 0 then (c, (f i).2) else f (i + k), by simp, fun k hk => by simp [show k ≠ 0 by omega]⟩
    have hg : S.GChain a0 a1 E Pst Pen (n - i) g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, hg1]
          obtain ⟨_, hxi, hcli⟩ := hP i hin
          exact ⟨hcbad, hxi, hccl.trans hcli⟩
        · rw [hg2 k h]
          exact hP _ (by omega)
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          rw [hg1, Nat.zero_add, hg2 1 Nat.one_pos]
          exact hL i (by omega)
        · rw [hg2 k h, hg2 (k + 1) (by omega), show i + (k + 1) = i + k + 1 by omega]
          exact hL _ (by omega)
      · rw [hg1]
        exact hpc
      · rcases Nat.eq_zero_or_pos (n - i) with h | h
        · rw [h, hg1, show i = n by omega]
          exact hn
        · rw [hg2 _ h, show i + (n - i) = n by omega]
          exact hn
    have := hmin _ ⟨g, hg⟩
    omega
  · intro i hin c hc hpc
    obtain ⟨hcbad, hccl⟩ := hmemcl i c hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧ g i = ((f i).1, c) :=
      ⟨fun k => if k < i then f k else ((f i).1, c), fun k hk => by simp [hk], by simp⟩
    have hg : S.GChain a0 a1 E Pst Pen i g := by
      refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
      · rcases eq_or_lt_of_le hk with h | h
        · rw [h, hg2]
          exact ⟨(hP i hin.le).1, hcbad, hccl.symm⟩
        · rw [hg1 k h]
          exact hP k (by omega)
      · rw [hg1 k hk]
        rcases (show k + 1 = i ∨ k + 1 < i by omega) with h | h
        · rw [h, hg2]
          have := hL k (by omega)
          rw [h] at this
          exact this
        · rw [hg1 (k + 1) h]
          exact hL k (by omega)
      · rcases Nat.eq_zero_or_pos i with h | h
        · subst h
          rw [hg2]
          exact h0
        · rw [hg1 0 h]
          exact h0
      · rw [hg2]
        exact hpc
    have := hmin _ ⟨g, hg⟩
    omega

end Stage1

end QECML
