import QECD1.FamWitness3
import QECD1.RouteWord3

/-!
# Case β: the excursion (2D `exc_chain`, `exc_route`, 3D, dimension-free)

In case β of the witness dichotomy (`fam_witness3`), W1's block `c` lies in the cluster of a block `k` of the family
but in no route cluster. The excursion goes from a route cluster through the level-1 component of `e` to the cluster
of `c`:

* `exists_kchain3`: blocks of one level-1 component are joined by a chain of trivial pairs `(b, b)`, consecutive ones
  within `a1`;
* `exists_min_fchain3_gen`: a shortest chain keeping its blocks in a set `T` and its later roots out of a set `R` has
  pairwise different clusters;
* `exc_chain3`: the excursion chain. Its first pair lies in a route cluster `C_jx`, its later clusters are off the
  route and pairwise different, and it ends at `k`.
* `exc_route3`: the segments of the excursion. They come from the chain without its first pair, with the last exit
  replaced by `c`. Their properties:
  * they are valid (`SegOK`), with pairwise different clusters, and linked within `a1`;
  * they are off the route;
  * the first root is within `a1` of a level-1 block `x0` of `C_jx`;
  * the last part spans at least `Sw` from its root, which is an actual block of the family (R0, `witness_span`).

With `exc_word_asp` (RouteWord3), the excursion word ends in `Asp` along some axis. The departure is a selected walk
from the route to the cover of `x0`, then a link to the first root (`link_mem_S1`).
-/

namespace QECD1

/-- **A shortest chain whose blocks satisfy `T` and whose later roots avoid `R`** has pairwise different clusters. -/
theorem exists_min_fchain3_gen (F L : Finset V3) {e x : V3} (T R : V3 → Prop)
    (hex : ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f ∧ (∀ i ≤ n, T (f i).1 ∧ T (f i).2) ∧
      ∀ i, 1 ≤ i → i ≤ n → ¬ R (f i).1) :
    ∃ (n : ℕ) (f : ℕ → V3 × V3), FChain3 F L e x n f ∧ (∀ i ≤ n, T (f i).1 ∧ T (f i).2) ∧
      (∀ i, 1 ≤ i → i ≤ n → ¬ R (f i).1) ∧ ∀ i j, i < j → j ≤ n → ¬ SameComp F Const.a0 (f i).1 (f j).1 := by
  classical
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → V3 × V3, FChain3 F L e x m g ∧ (∀ i ≤ m, T (g i).1 ∧ T (g i).2) ∧
      ∀ i, 1 ≤ i → i ≤ m → ¬ R (g i).1) → Nat.find hex ≤ m := fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨⟨hP, hL, h0, hn⟩, hT, hR⟩ := hf
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, hT, hR, ?_⟩
  intro i j hij hjn hcl
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → V3 × V3, (∀ k < i, g k = f k) ∧
      g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
    ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
      fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
  have hg : FChain3 F L e x (n - (j - i)) g := by
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
  have hgT : ∀ k ≤ n - (j - i), T (g k).1 ∧ T (g k).2 := by
    intro k hk
    rcases lt_trichotomy k i with h | h | h
    · rw [hg1 k h]
      exact hT k (by omega)
    · rw [h, hg2]
      exact ⟨(hT i (by omega)).1, (hT j hjn).2⟩
    · rw [hg3 k h]
      exact hT _ (by omega)
  have hgR : ∀ k, 1 ≤ k → k ≤ n - (j - i) → ¬ R (g k).1 := by
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
`(b, b)` of blocks of the component, consecutive ones within `a1`. -/
theorem exists_kchain3 (F L : Finset V3) (hLF : L ⊆ F) {e k : V3} (he : e ∈ L) (hk : SameComp L Const.a1 e k) :
    ∃ (n : ℕ) (g : ℕ → V3 × V3), FChain3 F L e k n g ∧
      ∀ i ≤ n, SameComp L Const.a1 e (g i).1 ∧ SameComp L Const.a1 e (g i).2 := by
  induction hk with
  | refl =>
    exact ⟨0, fun _ => (e, e), ⟨fun _ _ => ⟨hLF he, hLF he, .refl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      rfl, rfl⟩, fun _ _ => ⟨.refl, .refl⟩⟩
  | @tail b b' hb hbb ih =>
    obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hK⟩ := ih
    obtain ⟨hb1, hb'1, hd⟩ := hbb
    have hb'K : SameComp L Const.a1 e b' := hb.tail ⟨hb1, hb'1, hd⟩
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → V3 × V3, (∀ k, k ≠ n + 1 → g k = f k) ∧ g (n + 1) = (b', b') :=
      ⟨fun k => if k = n + 1 then (b', b') else f k, fun k hk => by simp [hk], by simp⟩
    refine ⟨n + 1, g, ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩, fun i hi => ?_⟩
    · rcases eq_or_ne i (n + 1) with h | h
      · rw [h, hg2]
        exact ⟨hLF hb'1, hLF hb'1, .refl⟩
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

/-- **The excursion chain** (case β): from a route cluster `C_jx` through the level-1 component of `e` to `k`, whose
cluster holds W1's block `c`. The clusters after `C_jx` are off the route and pairwise different. -/
theorem exc_chain3 (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} {n : ℕ} {f : ℕ → V3 × V3}
    (hf : FChain3 F L e x n f) (he : e ∈ L) {c k : V3}
    (hoff : ∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 c) (hk : SameComp L Const.a1 e k)
    (hck : SameComp F Const.a0 k c) :
    ∃ (jx p : ℕ) (h : ℕ → V3 × V3), jx ≤ n ∧ 1 ≤ p ∧ FChain3 F L (h 0).1 k p h ∧
      SameComp F Const.a0 (f jx).1 (h 0).1 ∧
      (∀ t ≤ p, SameComp L Const.a1 e (h t).1 ∧ SameComp L Const.a1 e (h t).2) ∧
      (∀ t, 1 ≤ t → t ≤ p → ∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 (h t).1) ∧
      ∀ t t', t < t' → t' ≤ p → ¬ SameComp F Const.a0 (h t).1 (h t').1 := by
  classical
  obtain ⟨hP, hL, h0, hn⟩ := hf
  obtain ⟨nk, g, ⟨hgP, hgL, hg0, hgn⟩, hgK⟩ := exists_kchain3 F L hLF he hk
  -- the cluster of `k` is off the route
  have hkoff : ∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 k := fun j hj hkj => hoff j hj (hkj.trans hck)
  -- the last pair of the chain in a route cluster
  let P : ℕ → Prop := fun t => ∃ j ≤ n, SameComp F Const.a0 (f j).1 (g t).1
  obtain ⟨jl, hjl⟩ : ∃ jl, Nat.findGreatest P nk = jl := ⟨_, rfl⟩
  have hjlN : jl ≤ nk := hjl ▸ Nat.findGreatest_le _
  have hjlmax : ∀ t, t ≤ nk → P t → t ≤ jl := fun t ht hPt => hjl ▸ Nat.le_findGreatest ht hPt
  have hP0 : P 0 := ⟨0, Nat.zero_le _, by rw [hg0, h0]; exact .refl⟩
  have hPjl : P jl := by
    by_cases hz : jl = 0
    · rw [hz]
      exact hP0
    · exact Nat.findGreatest_of_ne_zero hjl hz
  have hjlt : jl < nk := by
    rcases eq_or_lt_of_le hjlN with h | h
    · exfalso
      obtain ⟨j, hj, hcj⟩ := hPjl
      rw [h] at hcj
      have hcl := (hgP nk le_rfl).2.2
      rw [hgn] at hcl
      exact hkoff j hj (hcj.trans hcl)
    · exact h
  -- the sub-chain after it, then a shortest one
  have hsub : ∃ (m : ℕ) (g' : ℕ → V3 × V3), FChain3 F L (g jl).1 k m g' ∧
      (∀ t ≤ m, SameComp L Const.a1 e (g' t).1 ∧ SameComp L Const.a1 e (g' t).2) ∧
      ∀ t, 1 ≤ t → t ≤ m → ¬ (∃ j ≤ n, SameComp F Const.a0 (f j).1 (g' t).1) := by
    refine ⟨nk - jl, fun t => g (jl + t), ⟨fun t ht => hgP _ (by omega), fun t ht => ?_, by simp, ?_⟩,
      fun t ht => hgK _ (by omega), fun t ht1 ht hPt => ?_⟩
    · have := hgL (jl + t) (by omega)
      rwa [show jl + t + 1 = jl + (t + 1) by omega] at this
    · simp only
      rw [show jl + (nk - jl) = nk by omega]
      exact hgn
    · have := hjlmax (jl + t) (by omega) hPt
      omega
  obtain ⟨p, h, ⟨hhP, hhL, hh0, hhn⟩, hhK, hhR, hhd⟩ :=
    exists_min_fchain3_gen F L (fun b => SameComp L Const.a1 e b)
      (fun b => ∃ j ≤ n, SameComp F Const.a0 (f j).1 b) hsub
  obtain ⟨jx, hjx, hcjx⟩ := hPjl
  have hp1 : 1 ≤ p := by
    by_contra hp
    have hp0 : p = 0 := by omega
    subst hp0
    have hc0 := (hhP 0 le_rfl).2.2
    rw [hh0, hhn] at hc0
    exact hkoff jx hjx (hcjx.trans hc0)
  refine ⟨jx, p, h, hjx, hp1, ⟨hhP, hhL, rfl, hhn⟩, ?_, hhK, fun t ht1 ht j hj hcj => hhR t ht1 ht ⟨j, hj, hcj⟩,
    hhd⟩
  rw [hh0]
  exact hcjx

/-- **The excursion route** (case β): the segments of the off-route part of the excursion chain, the last exit
replaced by W1's block `c`. The last part spans at least `Sw` from its root. -/
theorem exc_route3 (F L : Finset V3) (hLF : L ⊆ F) {e x : V3} {n : ℕ} {f : ℕ → V3 × V3}
    (hf : FChain3 F L e x n f) (he : e ∈ L) {c k : V3} (hcL : c ∈ L)
    (hoff : ∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 c) (hk : SameComp L Const.a1 e k)
    (hck : SameComp F Const.a0 k c) (hfar : ¬ SameComp L Const.a1 e c)
    (hW0 : ∀ r ∈ L, ∃ b, SameComp F Const.a0 r b ∧ Const.D ≤ dist3 r b) :
    ∃ (jx : ℕ) (x0 : V3) (esegs : List Seg), jx ≤ n ∧ x0 ∈ L ∧ SameComp F Const.a0 (f jx).1 x0 ∧
      (∀ s ∈ esegs.head?, dist3 x0 s.root ≤ Const.a1 ∧ s.root ∈ L) ∧
      (∀ s ∈ esegs, SegOK F s) ∧
      esegs.Pairwise (fun s s' => ∀ p ∈ s.sel, ∀ q ∈ s'.sel, ¬ SameComp F Const.a0 p q) ∧
      esegs.IsChain (fun s s' => dist3 s.exit s'.root ≤ Const.a1) ∧
      (∀ s ∈ esegs, ∀ q ∈ s.sel, ∀ j ≤ n, ¬ SameComp F Const.a0 (f j).1 q) ∧
      ∃ sl, esegs.getLast? = some sl ∧ Const.Sw ≤ linf (segEnd sl - sl.root) := by
  obtain ⟨jx, p, h, hjx, hp1, ⟨hhP, hhL, _, hhn⟩, hjxc, hhK, hhoff, hhd⟩ :=
    exc_chain3 F L hLF hf he hoff hk hck
  -- the shifted chain, last exit `c`
  obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → V3 × V3, (∀ t, t ≠ p - 1 → g t = h (t + 1)) ∧ g (p - 1) = ((h p).1, c) :=
    ⟨fun t => if t = p - 1 then ((h p).1, c) else h (t + 1), fun t ht => by simp [ht], by simp⟩
  have hg1st : ∀ t ≤ p - 1, (g t).1 = (h (t + 1)).1 := by
    intro t ht
    rcases eq_or_ne t (p - 1) with h' | h'
    · rw [h', hg2, show p - 1 + 1 = p by omega]
    · rw [hg1 t h']
  have hcF : c ∈ F := hLF hcL
  have hgch : FChain3 F L (h 1).1 c (p - 1) g := by
    refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩
    · rcases eq_or_ne t (p - 1) with h' | h'
      · rw [h', hg2]
        obtain ⟨hpF, _, hpc⟩ := hhP p le_rfl
        rw [hhn] at hpc
        exact ⟨hpF, hcF, hpc.trans hck⟩
      · rw [hg1 t h']
        exact hhP _ (by omega)
    · rw [hg1 t (by omega), hg1st (t + 1) (by omega)]
      exact hhL (t + 1) (by omega)
    · exact hg1st 0 (by omega)
    · rw [hg2]
  have hgd : ∀ i j, i < j → j ≤ p - 1 → ¬ SameComp F Const.a0 (g i).1 (g j).1 := by
    intro i j hij hj
    rw [hg1st i (by omega), hg1st j hj]
    exact hhd (i + 1) (j + 1) (by omega) (by omega)
  have hgL : ∀ t ≤ p - 1, (g t).1 ∈ L := by
    intro t ht
    rw [hg1st t ht]
    exact (hhL t (by omega)).2.1
  obtain ⟨seg, hseg, -, hok, hpw, hch⟩ := fam_segs_data F L hgch hgd (fun t ht => hW0 _ (hgL t ht))
  refine ⟨jx, (h 0).2, (List.range (p - 1 + 1)).map seg, hjx, (hhL 0 (by omega)).1,
    hjxc.trans (hhP 0 (by omega)).2.2, ?_, hok, hpw, hch, ?_, ?_⟩
  · -- the first link
    intro s hs
    rw [List.range_succ_eq_map, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hs
    subst hs
    obtain ⟨hroot, -⟩ := hseg 0 (Nat.zero_le _)
    rw [hroot, hg1st 0 (Nat.zero_le _)]
    exact ⟨(hhL 0 (by omega)).2.2, (hhL 0 (by omega)).2.1⟩
  · -- off the route
    intro s hs q hq j hj hjq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    have ht' : t ≤ p - 1 := by
      have := List.mem_range.1 ht
      omega
    obtain ⟨-, -, hsub, -⟩ := hseg t ht'
    have hqK := (mem_clusterOf.1 (hsub hq)).2
    rw [hg1st t ht'] at hqK
    exact hhoff (t + 1) (by omega) (by omega) j hj (hjq.trans (sameComp_symm F _ hqK))
  · -- the last part spans at least `Sw`
    refine ⟨seg (p - 1), by simp [List.range_succ], ?_⟩
    obtain ⟨hroot, hexit, -, hsok, -⟩ := hseg (p - 1) le_rfl
    have hcov := hsok.exit_cov
    rw [hexit, hg2] at hcov
    rw [hroot, hg2]
    have hpL : (h p).1 ∈ L := by
      have := (hhL (p - 1) (by omega)).2.1
      rwa [show p - 1 + 1 = p by omega] at this
    have hdiff : ¬ SameComp L Const.a1 (h p).1 c := fun hpc => hfar ((hhK p le_rfl).1.trans hpc)
    exact witness_span L hpL hcL hdiff hcov

end QECD1
