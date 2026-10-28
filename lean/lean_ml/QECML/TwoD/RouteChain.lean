import QECML.TwoD.RoutePaths

/-!
# Cluster chains for the T1 route

A *cluster chain* is a sequence of pairs `(e i, x i)`, `i = 0, …, n`, of bad blocks (convention (i)) with `e i` and
`x i` in one analysis cluster, consecutive pairs joined by a level-1 link (`x i` and `e (i+1)` are level-1 blocks
at block distance at most `a1`), starting in the bottom strip (`e 0`) and ending in the top strip (`x n`).

* `exists_cchain`: every T1 event has a cluster chain (follow the family's links).
* `exists_min_cchain`: a chain with the fewest pairs has pairwise distinct clusters, no bottom-strip block in the
  clusters `1, …, n`, and no top-strip block in the clusters `0, …, n - 1` (each failure gives a shorter chain).
-/

open Finset Classical

namespace QECML

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- `(e, x)` is an entry/exit pair of bad blocks in one analysis cluster. -/
def PairOK (a0 : ℕ) (E : G.Ed → ZMod 2) (p : G.Block × G.Block) : Prop :=
  S.badD E p.1 ∧ S.badD E p.2 ∧ S.cluster E a0 p.1 = S.cluster E a0 p.2

/-- A level-1 link from the exit `x` to the next entry `e`. -/
def LinkOK (a0 a1 : ℕ) (E : G.Ed → ZMod 2) (x e : G.Block) : Prop :=
  x ∈ S.lev1 a0 E ∧ e ∈ S.lev1 a0 E ∧ G.blockDist x e ≤ a1

/-- A cluster chain with pairs `f 0, …, f n` from the bottom strip to the top strip. -/
def CChain (a0 a1 hs : ℕ) (E : G.Ed → ZMod 2) (n : ℕ) (f : ℕ → G.Block × G.Block) : Prop :=
  (∀ i ≤ n, S.PairOK a0 E (f i)) ∧ (∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1) ∧
    (f 0).1.2.val ≤ hs ∧ G.ny ≤ (f n).2.2.val + 1 + hs

theorem badD_of_lev1 {a0 : ℕ} {E : G.Ed → ZMod 2} {c : G.Block} (hc : c ∈ S.lev1 a0 E) : S.badD E c := by
  obtain ⟨⟨v, hv, hD⟩, _⟩ := hc
  exact Or.inr (Or.inl ⟨v, hv, hD⟩)

theorem linked_symm {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} (h : S.linked a0 a1 E c c') :
    S.linked a0 a1 E c' c := by
  obtain ⟨h1, h2, h3 | ⟨h4, h5, h6⟩⟩ := h
  · exact ⟨h2, h1, Or.inl h3.symm⟩
  · exact ⟨h2, h1, Or.inr ⟨h5, h4, h6.symm⟩⟩

theorem linked_reach_symm {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block}
    (h : Relation.ReflTransGen (S.linked a0 a1 E) c c') : Relation.ReflTransGen (S.linked a0 a1 E) c' c := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (S.linked_symm hbc) ih

theorem badD_of_linked_reach {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c c' : G.Block} (hc : S.badD E c)
    (h : Relation.ReflTransGen (S.linked a0 a1 E) c c') : S.badD E c' := by
  induction h with
  | refl => exact hc
  | tail _ hbc _ => exact hbc.2.1


/-- Partial chains: from `c1`, following the links of a family. -/
theorem exists_partial_chain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} {c1 : G.Block} (hc1 : S.badD E c1) :
    ∀ b, Relation.ReflTransGen (S.linked a0 a1 E) c1 b → ∃ (n : ℕ) (f : ℕ → G.Block × G.Block),
      (∀ i ≤ n, S.PairOK a0 E (f i)) ∧ (∀ i < n, S.LinkOK a0 a1 E (f i).2 (f (i + 1)).1) ∧
        (f 0).1 = c1 ∧ (f n).2 = b := by
  intro b hb
  induction hb with
  | refl => exact ⟨0, fun _ => (c1, c1), fun _ _ => ⟨hc1, hc1, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      rfl, rfl⟩
  | @tail b b' _ hbb ih =>
    obtain ⟨n, f, hP, hL, h0, hn⟩ := ih
    obtain ⟨hb, hb', hcl | ⟨hl, hl', hcomp⟩⟩ := hbb
    · -- same cluster: move the last exit to `b'`
      obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k, k ≠ n → g k = f k) ∧ g n = ((f n).1, b') :=
        ⟨fun k => if k = n then ((f n).1, b') else f k, fun k hk => by simp [hk], by simp⟩
      refine ⟨n, g, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
      · rcases eq_or_ne i n with h | h
        · rw [h, hg2]
          obtain ⟨he, _, hcl'⟩ := hP n le_rfl
          exact ⟨he, hb', by show S.cluster E a0 (f n).1 = S.cluster E a0 b'; rw [hcl', hn, hcl]⟩
        · rw [hg1 i h]
          exact hP i hi
      · rw [hg1 i (by omega)]
        rcases eq_or_ne (i + 1) n with h | h
        · rw [h, hg2]
          have := hL i hi
          rw [h] at this
          exact this
        · rw [hg1 (i + 1) h]
          exact hL i hi
      · rcases eq_or_ne n 0 with h | h
        · subst h
          rw [hg2]
          exact h0
        · rw [hg1 0 (Ne.symm h)]
          exact h0
      · rw [hg2]
    · -- a level-1 link chain from `b` to `b'`
      obtain ⟨_, hchain⟩ : b' ∈ G.comp (S.lev1 a0 E) a1 b := by
        rw [hcomp]
        exact S3Geom.mem_comp_self hl'
      clear hcomp hb' hl'
      induction hchain with
      | refl => exact ⟨n, f, hP, hL, h0, hn⟩
      | @tail u u' _ huu ih' =>
        obtain ⟨n', f', hP', hL', h0', hn'⟩ := ih'
        obtain ⟨hu, hu', hdist⟩ := huu
        obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block,
            (∀ k, k ≠ n' + 1 → g k = f' k) ∧ g (n' + 1) = (u', u') :=
          ⟨fun k => if k = n' + 1 then (u', u') else f' k, fun k hk => by simp [hk], by simp⟩
        refine ⟨n' + 1, g, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
        · rcases eq_or_ne i (n' + 1) with h | h
          · rw [h, hg2]
            exact ⟨S.badD_of_lev1 hu', S.badD_of_lev1 hu', rfl⟩
          · rw [hg1 i h]
            exact hP' i (by omega)
        · rw [hg1 i (by omega)]
          rcases eq_or_ne i n' with h | h
          · rw [h, hg2, hn']
            exact ⟨hu, hu', hdist⟩
          · rw [hg1 (i + 1) (by omega)]
            exact hL' i (by omega)
        · rw [hg1 0 (by omega)]
          exact h0'
        · rw [hg2]

/-- **Every T1 event has a cluster chain.** -/
theorem exists_cchain {a0 a1 : ℕ} {E : G.Ed → ZMod 2} (hT1 : S.T1 a0 a1 E) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.CChain a0 a1 (hs a1) E n f := by
  obtain ⟨c, hc, ⟨c1, ⟨_, hc1⟩, hrow1⟩, ⟨c2, ⟨_, hc2⟩, hrow2⟩⟩ := hT1
  have hreach : Relation.ReflTransGen (S.linked a0 a1 E) c1 c2 := (S.linked_reach_symm hc1).trans hc2
  obtain ⟨n, f, hP, hL, h0, hn⟩ := S.exists_partial_chain (S.badD_of_linked_reach hc hc1) c2 hreach
  exact ⟨n, f, hP, hL, by rw [h0]; exact hrow1, by rw [hn]; exact hrow2⟩

/-- **A shortest cluster chain** has distinct clusters, no bottom-strip block after the first cluster and no
top-strip block before the last. -/
theorem exists_min_cchain {a0 a1 hs : ℕ} {E : G.Ed → ZMod 2}
    (hex : ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.CChain a0 a1 hs E n f) :
    ∃ (n : ℕ) (f : ℕ → G.Block × G.Block), S.CChain a0 a1 hs E n f ∧
      (∀ i j, i < j → j ≤ n → S.cluster E a0 (f i).1 ≠ S.cluster E a0 (f j).1) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∀ c ∈ S.cluster E a0 (f i).1, hs < c.2.val) ∧
      (∀ i, i < n → ∀ c ∈ S.cluster E a0 (f i).1, c.2.val + 1 + hs < G.ny) := by
  obtain ⟨f, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m, (∃ g : ℕ → G.Block × G.Block, S.CChain a0 a1 hs E m g) → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  generalize Nat.find hex = n at hf hmin
  obtain ⟨hP, hL, h0, hn⟩ := hf
  -- a member of a cluster is bad and has the same cluster
  have hmemcl : ∀ i, ∀ c ∈ S.cluster E a0 (f i).1,
      S.badD E c ∧ S.cluster E a0 c = S.cluster E a0 (f i).1 := fun i c hc =>
    ⟨S3Geom.comp_subset hc, S3Geom.comp_eq_of_mem hc⟩
  refine ⟨n, f, ⟨hP, hL, h0, hn⟩, ?_, ?_, ?_⟩
  · -- distinct clusters: otherwise cut out the loop
    intro i j hij hjn hcl
    obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧
        g i = ((f i).1, (f j).2) ∧ ∀ k, i < k → g k = f (k + (j - i)) :=
      ⟨fun k => if k < i then f k else if k = i then ((f i).1, (f j).2) else f (k + (j - i)),
        fun k hk => by simp [hk], by simp, fun k hk => by simp [show ¬ k < i by omega, show k ≠ i by omega]⟩
    have hg : S.CChain a0 a1 hs E (n - (j - i)) g := by
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
  · -- no bottom-strip block after the first cluster: otherwise start there
    intro i hi1 hin c hc
    refine not_le.mp fun hrow => ?_
    obtain ⟨hcbad, hccl⟩ := hmemcl i c hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, g 0 = (c, (f i).2) ∧ ∀ k, 0 < k → g k = f (i + k) :=
      ⟨fun k => if k = 0 then (c, (f i).2) else f (i + k), by simp, fun k hk => by simp [show k ≠ 0 by omega]⟩
    have hg : S.CChain a0 a1 hs E (n - i) g := by
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
        exact hrow
      · rcases Nat.eq_zero_or_pos (n - i) with h | h
        · rw [h, hg1, show i = n by omega]
          exact hn
        · rw [hg2 _ h, show i + (n - i) = n by omega]
          exact hn
    have := hmin _ ⟨g, hg⟩
    omega
  · -- no top-strip block before the last cluster: otherwise stop there
    intro i hin c hc
    refine not_le.mp fun hrow => ?_
    obtain ⟨hcbad, hccl⟩ := hmemcl i c hc
    obtain ⟨g, hg1, hg2⟩ : ∃ g : ℕ → G.Block × G.Block, (∀ k < i, g k = f k) ∧ g i = ((f i).1, c) :=
      ⟨fun k => if k < i then f k else ((f i).1, c), fun k hk => by simp [hk], by simp⟩
    have hg : S.CChain a0 a1 hs E i g := by
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
        exact hrow
    have := hmin _ ⟨g, hg⟩
    omega

end Stage1

end QECML
