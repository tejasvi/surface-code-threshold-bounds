import QECML.TwoD.RouteChain

/-!
# T1 route existence (the deterministic part of the T1 term)

Every T1 event has a valid route (`ValidRoute`) whose counted blocks are all bad. From a shortest cluster chain
(`exists_min_cchain`): in each cluster a selection rooted at the entry block and a simple path in it from the entry
to a selected block covering the exit; consecutive clusters joined by level-1 links; after a link into a middle
cluster whose path is trivial, a leaf (a second selected block next to the entry, from (W0)); the route starts at
the last bottom-strip block of the first path and stops before the first top-strip block of the last one.

* `Frag`: route fragments (offsets, grammar, rows strictly between the strips, separation, a property `P` of the
  blocks), with `Frag.append`, `Frag.steps`, and the two cuts (`exists_last_split`, `exists_first_split`).
* `Stage1.t1RouteExistsOn`: the route existence on one code, for `a0 ≥ 2`, `1 ≤ D ≤ a0 + 1` and `a0 ≤ a1`.
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

theorem row_le_add_blockDist (c c' : G.Block) : c'.2.val ≤ c.2.val + G.blockDist c c' := by
  have h : ndist c.2.val c'.2.val ≤ G.blockDist c c' := le_max_right _ _
  unfold ndist at h
  omega

theorem endBlock_append (cur : G.Block) (ms1 ms2 : List G.Move) :
    endBlock cur (ms1 ++ ms2) = endBlock (endBlock cur ms1) ms2 := by
  induction ms1 generalizing cur with
  | nil => rfl
  | cons m ms ih =>
    cases m with
    | step b => exact ih b
    | link b => exact ih b
    | leaf b => exact ih cur

theorem movesOK_append {D A0 A1 : ℕ} (cur : G.Block) (ms1 ms2 : List G.Move) :
    MovesOK D A0 A1 cur (ms1 ++ ms2) ↔ MovesOK D A0 A1 cur ms1 ∧ MovesOK D A0 A1 (endBlock cur ms1) ms2 := by
  induction ms1 generalizing cur with
  | nil => simp [MovesOK, endBlock]
  | cons m ms ih =>
    cases m with
    | step b => simp only [List.cons_append, MovesOK, endBlock, ih, and_assoc]
    | link b => simp only [List.cons_append, MovesOK, endBlock, ih, and_assoc]
    | leaf b => simp only [List.cons_append, MovesOK, endBlock, ih, and_assoc]

/-- In-cluster steps along a chain of blocks. -/
theorem movesOK_steps {D A0 A1 : ℕ} (cur : G.Block) (l : List G.Block)
    (h : List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) (cur :: l)) :
    MovesOK D A0 A1 cur (l.map Move.step) := by
  induction l generalizing cur with
  | nil => simp [MovesOK]
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    simp only [List.map_cons, MovesOK]
    exact ⟨h.1.1, h.1.2, ih b h.2⟩

theorem endBlock_steps (cur : G.Block) (l : List G.Block) {s : G.Block} (hs : (cur :: l).getLast? = some s) :
    endBlock cur (l.map Move.step) = s := by
  induction l generalizing cur with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hs
    subst hs
    rfl
  | cons b l ih =>
    rw [List.getLast?_cons_cons] at hs
    exact ih b hs

theorem map_blk_steps (l : List G.Block) : (l.map Move.step).map Move.blk = l := by
  induction l with
  | nil => rfl
  | cons b l ih => exact congrArg (b :: ·) ih

theorem gram_step_step (a b : G.Block) : GramOK (Move.step a) (Move.step b) :=
  ⟨fun h => False.elim h, fun h => False.elim h, fun h => False.elim h⟩

theorem gram_to_link {m : G.Move} (hm : ¬ m.isLink) (e : G.Block) : GramOK m (Move.link e) :=
  ⟨fun h => False.elim h, fun _ => trivial, fun h => (hm h).elim⟩

theorem gram_link_step (e b : G.Block) : GramOK (Move.link e) (Move.step b) :=
  ⟨fun h => False.elim h, fun h => False.elim h, fun _ => Or.inr trivial⟩

theorem gram_link_leaf (e b : G.Block) : GramOK (Move.link e) (Move.leaf b) :=
  ⟨fun _ => trivial, fun h => False.elim h, fun _ => Or.inl trivial⟩

theorem isChain_gram_steps (l : List G.Block) : List.IsChain GramOK (l.map Move.step) := by
  rw [List.isChain_map]
  induction l with
  | nil => exact List.isChain_nil
  | cons b l ih =>
    rw [List.isChain_cons]
    exact ⟨fun y _ => gram_step_step b y, ih⟩

theorem head?_append_forall {α : Type*} {p : α → Prop} {l l' : List α} (h : ∀ x ∈ l.head?, p x)
    (h' : ∀ x ∈ l'.head?, p x) : ∀ x ∈ (l ++ l').head?, p x := by
  cases l with
  | nil => simpa using h'
  | cons a l => simpa using h

theorem getLast?_append_forall {α : Type*} {p : α → Prop} {l l' : List α} (h : ∀ x ∈ l.getLast?, p x)
    (h' : ∀ x ∈ l'.getLast?, p x) : ∀ x ∈ (l ++ l').getLast?, p x := by
  intro x hx
  rw [List.getLast?_append] at hx
  cases hl' : l'.getLast? with
  | none =>
    rw [hl'] at hx
    exact h x hx
  | some y =>
    rw [hl'] at hx h'
    exact h' x hx

theorem getLast?_append_cons {α : Type*} (pre suf : List α) (b : α) :
    (pre ++ b :: suf).getLast? = (b :: suf).getLast? := by
  rw [List.getLast?_append, List.getLast?_cons]
  rfl

/-- A route fragment from `cur`: offsets, grammar, rows strictly between the strips, `D`-separation, and `P` on
its blocks. -/
def Frag (D A0 A1 hs : ℕ) (P : G.Block → Prop) (cur : G.Block) (ms : List G.Move) : Prop :=
  MovesOK D A0 A1 cur ms ∧ List.IsChain GramOK ms ∧
    (∀ m ∈ ms, hs + 1 ≤ m.blk.2.val ∧ m.blk.2.val + 2 + hs ≤ G.ny ∧ P m.blk) ∧
    (ms.map Move.blk).Pairwise (fun b b' => D ≤ G.blockDist b b')

theorem Frag.append {D A0 A1 hs : ℕ} {P : G.Block → Prop} {cur : G.Block} {ms1 ms2 : List G.Move}
    (h1 : Frag D A0 A1 hs P cur ms1) (h2 : Frag D A0 A1 hs P (endBlock cur ms1) ms2)
    (hj : ∀ m ∈ ms1.getLast?, ∀ m' ∈ ms2.head?, GramOK m m')
    (hsep : ∀ m ∈ ms1, ∀ m' ∈ ms2, D ≤ G.blockDist m.blk m'.blk) : Frag D A0 A1 hs P cur (ms1 ++ ms2) := by
  obtain ⟨hm1, hc1, hr1, hp1⟩ := h1
  obtain ⟨hm2, hc2, hr2, hp2⟩ := h2
  refine ⟨(movesOK_append cur ms1 ms2).2 ⟨hm1, hm2⟩, List.isChain_append.2 ⟨hc1, hc2, hj⟩, fun m hm => ?_, ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · exact hr1 m hm
    · exact hr2 m hm
  · rw [List.map_append, List.pairwise_append]
    refine ⟨hp1, hp2, fun b hb b' hb' => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hb'
    exact hsep m hm m' hm'

/-- Steps along a chain of blocks form a fragment. -/
theorem Frag.steps {D A0 A1 hs : ℕ} {P : G.Block → Prop} (cur : G.Block) (l : List G.Block)
    (hch : List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) (cur :: l))
    (hrow : ∀ b ∈ l, hs + 1 ≤ b.2.val ∧ b.2.val + 2 + hs ≤ G.ny ∧ P b)
    (hsep : l.Pairwise (fun b b' => D ≤ G.blockDist b b')) : Frag D A0 A1 hs P cur (l.map Move.step) := by
  refine ⟨movesOK_steps cur l hch, isChain_gram_steps l, fun m hm => ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hm
    exact hrow b hb
  · rw [map_blk_steps]
    exact hsep

/-- A link followed by steps along a chain. -/
theorem Frag.link_steps {D A0 A1 hs : ℕ} {P : G.Block → Prop} (cur e : G.Block) (l : List G.Block)
    (hlo : D ≤ G.blockDist cur e) (hhi : G.blockDist cur e ≤ A1)
    (hch : List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) (e :: l))
    (hrow : ∀ b ∈ e :: l, hs + 1 ≤ b.2.val ∧ b.2.val + 2 + hs ≤ G.ny ∧ P b)
    (hsep : (e :: l).Pairwise (fun b b' => D ≤ G.blockDist b b')) :
    Frag D A0 A1 hs P cur (Move.link e :: l.map Move.step) := by
  have h1 : Frag D A0 A1 hs P cur [Move.link e] :=
    ⟨⟨hlo, hhi, trivial⟩, List.isChain_singleton _, fun m hm => by
      rw [List.mem_singleton.1 hm]; exact hrow e List.mem_cons_self, List.pairwise_singleton _ _⟩
  rw [List.pairwise_cons] at hsep
  have h2 := Frag.steps (A1 := A1) (P := P) e l hch (fun b hb => hrow b (List.mem_cons_of_mem e hb)) hsep.2
  refine Frag.append (ms1 := [Move.link e]) h1 h2 (fun m hm m' hm' => ?_) (fun m hm m' hm' => ?_)
  · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hm
    subst hm
    cases l with
    | nil => simp at hm'
    | cons b l =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hm'
      subst hm'
      exact gram_link_step e b
  · rw [List.mem_singleton.1 hm]
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hm'
    exact hsep.1 b hb

/-- A link followed by a leaf. -/
theorem Frag.link_leaf {D A0 A1 hs : ℕ} {P : G.Block → Prop} (cur e l : G.Block)
    (hlo : D ≤ G.blockDist cur e) (hhi : G.blockDist cur e ≤ A1)
    (hlo' : D ≤ G.blockDist e l) (hhi' : G.blockDist e l ≤ A0)
    (hre : hs + 1 ≤ e.2.val ∧ e.2.val + 2 + hs ≤ G.ny ∧ P e)
    (hrl : hs + 1 ≤ l.2.val ∧ l.2.val + 2 + hs ≤ G.ny ∧ P l) :
    Frag D A0 A1 hs P cur [Move.link e, Move.leaf l] := by
  refine ⟨⟨hlo, hhi, hlo', hhi', trivial⟩, List.isChain_pair.2 (gram_link_leaf e l), fun m hm => ?_, ?_⟩
  · rcases List.mem_pair.1 hm with rfl | rfl
    · exact hre
    · exact hrl
  · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton, forall_eq,
      List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, and_true]
    exact hlo'

/-- Last element with a property: `a :: l = pre ++ b :: suf` with `P b` and no element of `suf` satisfying `P`. -/
theorem exists_last_split {α : Type*} (P : α → Prop) (a : α) (l : List α) (ha : P a) :
    ∃ pre b suf, a :: l = pre ++ b :: suf ∧ P b ∧ ∀ x ∈ suf, ¬ P x := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], a, [], rfl, ha, fun x hx => absurd hx (by simp)⟩
  | append_singleton l c ih =>
    by_cases hc : P c
    · exact ⟨a :: l, c, [], by simp, hc, fun x hx => absurd hx (by simp)⟩
    · obtain ⟨pre, b, suf, he, hb, hsuf⟩ := ih
      refine ⟨pre, b, suf ++ [c], ?_, hb, fun x hx => ?_⟩
      · rw [← List.cons_append, he, List.append_assoc, List.cons_append]
      · rcases List.mem_append.1 hx with hx | hx
        · exact hsuf x hx
        · rw [List.mem_singleton.1 hx]
          exact hc

/-- First element with a property: `l = l1 ++ l2` with no element of `l1` satisfying `P` and `P` at the head of
`l2`. -/
theorem exists_first_split {α : Type*} (P : α → Prop) (l : List α) :
    ∃ l1 l2, l = l1 ++ l2 ∧ (∀ x ∈ l1, ¬ P x) ∧ ∀ y ∈ l2.head?, P y := by
  induction l with
  | nil => exact ⟨[], [], rfl, fun x hx => absurd hx (by simp), fun y hy => absurd hy (by simp)⟩
  | cons a l ih =>
    by_cases ha : P a
    · refine ⟨[], a :: l, rfl, fun x hx => absurd hx (by simp), fun y hy => ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hy]
      exact ha
    · obtain ⟨l1, l2, he, h1, h2⟩ := ih
      refine ⟨a :: l1, l2, by rw [he, List.cons_append], fun x hx => ?_, h2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact h1 x hx

/-- **The final cut.** Steps along a chain from `cur`, stopped before the first block in the top strip; the stop
point is high enough if the end of the chain is. -/
theorem final_cut {D A0 A1 hs : ℕ} {P : G.Block → Prop} (hA : A0 ≤ A1) (cur : G.Block) (l : List G.Block)
    (hch : List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) (cur :: l))
    (hrow : ∀ b ∈ l, hs + 1 ≤ b.2.val ∧ P b)
    (hsep : l.Pairwise (fun b b' => D ≤ G.blockDist b b'))
    (hend : ∀ s, (cur :: l).getLast? = some s → G.ny ≤ s.2.val + 1 + hs + A1) :
    ∃ l1 : List G.Block, Frag D A0 A1 hs P cur (l1.map Move.step) ∧
      G.ny ≤ (endBlock cur (l1.map Move.step)).2.val + 1 + hs + A1 ∧ ∀ b ∈ l1, b ∈ l := by
  obtain ⟨l1, l2, he, h1, h2⟩ := exists_first_split (fun b : G.Block => G.ny ≤ b.2.val + 1 + hs) l
  subst he
  have hch' : List.IsChain (fun x y => D ≤ G.blockDist x y ∧ G.blockDist x y ≤ A0) ((cur :: l1) ++ l2) := hch
  rw [List.isChain_append] at hch'
  obtain ⟨t, ht⟩ : ∃ t, (cur :: l1).getLast? = some t := by
    cases h : (cur :: l1).getLast? with
    | none => simp at h
    | some t => exact ⟨t, rfl⟩
  have hendt : endBlock cur (l1.map Move.step) = t := endBlock_steps cur l1 ht
  refine ⟨l1, Frag.steps cur l1 hch'.1 (fun b hb => ?_) (List.pairwise_append.1 hsep).1, ?_,
    fun b hb => List.mem_append_left l2 hb⟩
  · obtain ⟨hr, hp⟩ := hrow b (List.mem_append_left l2 hb)
    have := h1 b hb
    exact ⟨hr, by omega, hp⟩
  · rw [hendt]
    cases l2 with
    | nil =>
      rw [List.append_nil] at hend
      exact hend t ht
    | cons y l2 =>
      have hy := h2 y (by simp)
      have hty := (hch'.2.2 t ht y (by simp)).2
      have := row_le_add_blockDist t y
      omega

theorem steps_head (l : List G.Block) : ∀ m ∈ (l.map Move.step).head?, ¬ m.isLeaf := by
  intro m hm
  cases l with
  | nil => simp at hm
  | cons b l =>
    simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hm
    subst hm
    exact fun h => False.elim h

theorem steps_last (l : List G.Block) : ∀ m ∈ (l.map Move.step).getLast?, ¬ m.isLink := by
  intro m hm
  rw [List.getLast?_map] at hm
  cases h : l.getLast? with
  | none =>
    rw [h] at hm
    simp at hm
  | some b =>
    rw [h] at hm
    have e : Option.map Move.step (some b) = some (Move.step b) := rfl
    rw [e, Option.mem_def, Option.some.injEq] at hm
    subst hm
    exact fun h => False.elim h

theorem validRoute_of_frag {D A0 A1 hs : ℕ} {P : G.Block → Prop} {b0 : G.Block} {ms : List G.Move}
    (hb0 : b0.2.val ≤ hs) (hf : Frag D A0 A1 hs P b0 ms) (hhead : ∀ m ∈ ms.head?, ¬ m.isLeaf)
    (htop : G.ny ≤ (endBlock b0 ms).2.val + 1 + hs + A1) : ValidRoute D A0 A1 hs b0 ms :=
  ⟨hb0, hf.1, hf.2.1, hhead, fun m hm => ⟨(hf.2.2.1 m hm).1, (hf.2.2.1 m hm).2.1⟩, hf.2.2.2, htop⟩

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

theorem mem_cluster_self {E : G.Ed → ZMod 2} {a0 : ℕ} {c : G.Block} (hc : S.badD E c) :
    c ∈ S.cluster E a0 c :=
  S3Geom.mem_comp_self hc

/-- Blocks of distinct analysis clusters are more than `a0` apart. -/
theorem cluster_sep {E : G.Ed → ZMod 2} {a0 : ℕ} {c c' x y : G.Block} (hx : x ∈ S.cluster E a0 c)
    (hy : y ∈ S.cluster E a0 c') (hne : S.cluster E a0 c ≠ S.cluster E a0 c') : a0 < G.blockDist x y := by
  refine not_le.mp fun h => hne ?_
  have hxb : S.badD E x := S3Geom.comp_subset hx
  have hyb : S.badD E y := S3Geom.comp_subset hy
  have hyx : y ∈ S.cluster E a0 x := ⟨hxb, Relation.ReflTransGen.single ⟨hxb, hyb, h⟩⟩
  calc S.cluster E a0 c = S.cluster E a0 x := (S3Geom.comp_eq_of_mem hx).symm
    _ = S.cluster E a0 y := (S3Geom.comp_eq_of_mem hyx).symm
    _ = S.cluster E a0 c' := S3Geom.comp_eq_of_mem hy

/-- A bad block (convention (i)) strictly between the strips is bad. -/
theorem bad_of_badD_rows {E : G.Ed → ZMod 2} {hs : ℕ} (hhs : 1 ≤ hs) {c : G.Block} (hc : S.badD E c)
    (h1 : hs + 1 ≤ c.2.val) (h2 : c.2.val + 2 + hs ≤ G.ny) : S.bad E c := by
  rcases hc with hdecl | hbad
  · exfalso
    rcases hdecl with h | h <;> omega
  · exact hbad

/-- **T1 route existence** on one code: for `a0 ≥ 2`, `1 ≤ D ≤ a0 + 1` and `a0 ≤ a1`, every T1 event has a valid
route whose counted blocks are all bad. -/
theorem t1RouteExistsOn {a0 a1 : ℕ} (ha0 : 2 ≤ a0) (hD1 : 1 ≤ G.D) (hDa : G.D ≤ a0 + 1) (ha01 : a0 ≤ a1) :
    S.T1RouteExistsOn a0 a1 := by
  intro E hT1
  obtain ⟨n, f, ⟨hP, hL, h0, hn⟩, hdist, hbot, htop⟩ := S.exists_min_cchain (S.exists_cchain hT1)
  have hhs1 : 1 ≤ hs a1 := by simp [hs]
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
      | cons e rest =>
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
      have h1 := hbot i hi1 hin.le c hc
      have h2 := htop i hin c hc
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
    rcases l with _ | ⟨e, _ | ⟨y, l⟩⟩
    · simp at hhead
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd (hlast.symm.trans hhead) hsne
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rw [List.isChain_cons_cons] at hch
      exact ⟨y, hmemL y (by simp), fun h => hch.1.1 h.symm, hch.1.2⟩
  -- every block of a route fragment built here is bad
  have hconv : ∀ {cur : G.Block} {ms : List G.Move},
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) cur ms → ∀ m ∈ ms, S.bad E m.blk :=
    fun hf m hm => S.bad_of_badD_rows hhs1 (hf.2.2.1 m hm).2.2 (hf.2.2.1 m hm).1 (hf.2.2.1 m hm).2.1
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
  -- the prefix through cluster i < n
  have hinv : ∀ i, i < n → ∃ (b0 : G.Block) (ms : List G.Move), b0.2.val ≤ hs a1 ∧
      S3Geom.Frag G.D (G.D - 1 + a0) (G.D - 1 + a1) (hs a1) (S.badD E) b0 ms ∧
      (∀ m ∈ ms.head?, ¬ m.isLeaf) ∧ (∀ m ∈ ms.getLast?, ¬ m.isLink) ∧
      (∀ m ∈ ms, ∃ j ≤ i, m.blk ∈ S.cluster E a0 (f j).1) ∧ S3Geom.endBlock b0 ms = sEnd i := by
    intro i
    induction i with
    | zero =>
      intro hn0
      -- start at the last bottom-strip block of the first path
      obtain ⟨pre, b, suf, hsplit, hb, hsuf⟩ :=
        S3Geom.exists_last_split (fun c : G.Block => c.2.val ≤ hs a1) (f 0).1 (rest 0) h0
      have hch := hpath 0 (by omega)
      have hpw0 := hpw 0 (by omega)
      have hK0 := hpK 0 (by omega)
      obtain ⟨-, -, -, -, -, -, -, hlastP, -⟩ := hdat 0 (by omega)
      rw [hsplit] at hch hpw0 hK0 hlastP
      rw [S3Geom.getLast?_append_cons] at hlastP
      have hpw' := (List.pairwise_append.1 hpw0).2.1
      rw [List.pairwise_cons] at hpw'
      have hsufK : ∀ c ∈ suf, c ∈ S.cluster E a0 (f 0).1 :=
        fun c hc => hK0 c (List.mem_append_right pre (List.mem_cons_of_mem b hc))
      refine ⟨b, suf.map S3Geom.Move.step, hb,
        S3Geom.Frag.steps b suf hch.right_of_append (fun c hc => ?_) hpw'.2,
        S3Geom.steps_head suf, S3Geom.steps_last suf, fun m hm => ?_, S3Geom.endBlock_steps b suf hlastP⟩
      · have h1 : ¬ c.2.val ≤ hs a1 := hsuf c hc
        have h2 := htop 0 hn0 c (hsufK c hc)
        exact ⟨by omega, by omega, hbadK 0 c (hsufK c hc)⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
        exact ⟨0, le_rfl, hsufK c hc⟩
    | succ i ih =>
      intro hin
      obtain ⟨b0, ms, hb0, hfrag, hhead, hlast, hblk, hend⟩ := ih (by omega)
      obtain ⟨hSK, hsep, -, -, -, hmem, -, hlastP, -⟩ := hdat (i + 1) hin.le
      obtain ⟨hlo, hhi⟩ := hlink i (by omega)
      have hmid : ∀ c ∈ S.cluster E a0 (f (i + 1)).1,
          hs a1 + 1 ≤ c.2.val ∧ c.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E c := fun c hc => by
        have h1 := hbot (i + 1) (by omega) hin.le c hc
        have h2 := htop (i + 1) hin c hc
        exact ⟨by omega, by omega, hbadK _ c hc⟩
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
              (hmid _ (heK _ hin.le)) (hmid _ (hSK l hlS)), by simp, fun m hm => ?_, fun m hm => ?_, ?_⟩
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
            S3Geom.Frag.link_steps _ _ _ hlo hhi (hpath _ hin.le) (fun c hc => hmid c (hpK _ hin.le c hc))
              (hpw _ hin.le), by simp, fun m hm => ?_, fun m hm => ?_, S3Geom.endBlock_steps _ _ hlastP⟩
          · obtain ⟨c, rest', hcr⟩ := List.exists_cons_of_ne_nil hr
            rw [hcr, List.map_cons, List.getLast?_cons_cons, ← List.map_cons] at hm
            exact S3Geom.steps_last _ m hm
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact heK _ hin.le
            · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
              exact hpK _ hin.le c (List.mem_cons_of_mem _ hc)
      refine ⟨b0, ms ++ unit, hb0, S3Geom.Frag.append hfrag (by rw [hend]; exact hufrag) (fun m hm m' hm' => ?_)
        (fun m hm m' hm' => ?_), S3Geom.head?_append_forall hhead (fun m hm => ?_),
        S3Geom.getLast?_append_forall hlast hulast, fun m hm => ?_, ?_⟩
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
      · rw [S3Geom.endBlock_append, hend, huend]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- one cluster: both cuts on its path
    subst hn0
    obtain ⟨pre, b, suf, hsplit, hb, hsuf⟩ :=
      S3Geom.exists_last_split (fun c : G.Block => c.2.val ≤ hs a1) (f 0).1 (rest 0) h0
    have hch := hpath 0 le_rfl
    have hpw0 := hpw 0 le_rfl
    have hK0 := hpK 0 le_rfl
    have hend0 := hendN
    rw [hsplit] at hch hpw0 hK0 hend0
    have hpw' := (List.pairwise_append.1 hpw0).2.1
    rw [List.pairwise_cons] at hpw'
    have hrow0 : ∀ c ∈ suf, hs a1 + 1 ≤ c.2.val ∧ S.badD E c := fun c hc => by
      have h1 : ¬ c.2.val ≤ hs a1 := hsuf c hc
      exact ⟨by omega, hbadK 0 c (hK0 c (List.mem_append_right pre (List.mem_cons_of_mem b hc)))⟩
    have hend0' : ∀ s', (b :: suf).getLast? = some s' → G.ny ≤ s'.2.val + 1 + hs a1 + (G.D - 1 + a1) :=
      fun s' hs' => hend0 s' (by rw [S3Geom.getLast?_append_cons]; exact hs')
    obtain ⟨l1, hfrag, htop1, -⟩ := S3Geom.final_cut (by omega : G.D - 1 + a0 ≤ G.D - 1 + a1) b suf
      hch.right_of_append hrow0 hpw'.2 hend0'
    exact ⟨b, l1.map S3Geom.Move.step, S3Geom.validRoute_of_frag hb hfrag (S3Geom.steps_head l1) htop1,
      hconv hfrag⟩
  · -- several clusters: the prefix through cluster n - 1, then the last cluster
    obtain ⟨b0, ms, hb0, hfrag, hhead, hlast, hblk, hend⟩ := hinv (n - 1) (by omega)
    obtain ⟨hlo, hhi⟩ := hlink (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at hlo hhi
    by_cases htopn : G.ny ≤ (f n).1.2.val + 1 + hs a1
    · -- the entry of the last cluster is in the top strip: the prefix is the route
      refine ⟨b0, ms, S3Geom.validRoute_of_frag hb0 hfrag hhead ?_, hconv hfrag⟩
      rw [hend]
      have := S3Geom.row_le_add_blockDist (sEnd (n - 1)) (f n).1
      omega
    · -- link into the last cluster, then steps until the top strip
      have hrowN : ∀ c ∈ rest n, hs a1 + 1 ≤ c.2.val ∧ S.badD E c := fun c hc => by
        have hcK := hpK n le_rfl c (List.mem_cons_of_mem _ hc)
        have := hbot n (by omega) le_rfl c hcK
        exact ⟨by omega, hbadK n c hcK⟩
      have hpwN := hpw n le_rfl
      rw [List.pairwise_cons] at hpwN
      obtain ⟨l1, hfrag1, htop1, hl1⟩ := S3Geom.final_cut (by omega : G.D - 1 + a0 ≤ G.D - 1 + a1) (f n).1
        (rest n) (hpath n le_rfl) hrowN hpwN.2 hendN
      have herow : hs a1 + 1 ≤ (f n).1.2.val ∧ (f n).1.2.val + 2 + hs a1 ≤ G.ny ∧ S.badD E (f n).1 := by
        have := hbot n (by omega) le_rfl _ (heK n le_rfl)
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
      refine ⟨b0, ms ++ ([S3Geom.Move.link (f n).1] ++ l1.map S3Geom.Move.step),
        S3Geom.validRoute_of_frag hb0 hfull (S3Geom.head?_append_forall hhead hhead2) ?_, hconv hfull⟩
      rw [S3Geom.endBlock_append, hend]
      exact htop1

end Stage1

namespace S3Fam

variable (fam : S3Fam)

/-- **T1RouteExists is a theorem** (no longer a hypothesis) whenever `a0 ≥ 2`, `a0 ≤ a1` and the separation
`D = 4 + ⌊2R/L⌋` is at most `a0 + 1`. -/
theorem t1RouteExists {a0 a1 : ℕ} (K : BoundConsts) (ha0 : 2 ≤ a0) (hD : 4 + 2 * fam.R / fam.L ≤ a0 + 1)
    (ha01 : a0 ≤ a1) : fam.T1RouteExists a0 a1 K :=
  fun nx ny _ _ hny1 => (fam.stage1 nx ny (by omega) hny1).t1RouteExistsOn ha0
    (show 1 ≤ 4 + 2 * fam.R / fam.L from le_add_right (by norm_num)) hD ha01

end S3Fam

/-- **Theorem B (a1 = 12 constants), T1 term by counting only.** The T1 route existence is proved
(`S3Fam.t1RouteExists`, needs `R < L`, which gives `D = 5 ≤ a0 + 1`); the T1 term is left as the pure counting
bound `H2D_T1count` on block geometry. -/
theorem theoremB_a12_count (sp : S3Prog) (hV6 : sp.V6) (hRL : sp.R < sp.L)
    (Z : ∀ (nx ny : ℕ) (hnx : 1 ≤ nx) (hny : 1 ≤ ny), Solver ((sp.toFam hV6).geom nx ny hnx hny))
    (hcount : (sp.toFam hV6).H2D_T1count 4 12 constsA12 5e-4)
    (hT2 : (sp.toFam hV6).H2D_T2 4 12 Z constsA12 0.100 5e-4)
    (htype : (sp.toFam hV6).Htype 0.100) (hstat : (sp.toFam hV6).Hstat 0.100 5e-4)
    {q : ℝ} (hq : q ≤ 0.100) {W H : ℕ} (hW : 1 ≤ W) (hH : 32 * sp.L ≤ H) :
    pMLPlanar (W - 1) (H - 1) q ≤
      4.22e2 * (nxOf sp.L W : ℝ) * Real.exp (-0.2155 * ((nyOf sp.L H : ℝ) - 31)) +
        9.61e4 * (nxOf sp.L W : ℝ) * Real.exp (-0.0351 * ((nyOf sp.L H : ℝ) - 31)) := by
  have hdiv : 2 * sp.R / sp.L < 2 := (Nat.div_lt_iff_lt_mul (by have := sp.hL; omega)).2 (by omega)
  exact S3Fam.theoremB_a12_routes sp hV6 Z
    ((sp.toFam hV6).t1RouteExists constsA12 (by norm_num)
      (show 4 + 2 * sp.R / sp.L ≤ 4 + 1 from Nat.add_le_add_left (Nat.lt_succ_iff.mp hdiv) 4)
      (by norm_num)) hcount hT2 htype hstat hq hW hH

end QECML
