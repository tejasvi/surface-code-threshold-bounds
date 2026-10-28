import QECML.TwoD.T2Count
import QECML.TwoD.T2Fam
import QECML.TwoD.T2Transfer

/-!
# The family bound of the T2 count

A family unit `f = (cr, wt)` of a T2 skeleton (a cluster route with its witness) is encoded by its route word with
the witness mark (a word of the family automaton `famAut`) and its witness word (a word of the witness automaton
`witAut`):

* `CRoute.word`: the moves of a cluster route read from its first root: the steps of each route part, or its leaf,
  then the link to the next root.
* `markAt`: the route word with the mark inserted at the witness branch point (`markPos`): at the root of the witness
  cluster (state `B`), after the step to the branch block (`A1`, `A2`), or after the leaf (`C`).
* `witWord`: the witness walk, then (off-route witness) the link to the excursion and the excursion's route word.
* `famEnc f`: the first root, the counted blocks, the exit cover, the marked word and the witness word.

`fam_bound`: over a finite set of valid family units from a root `r0` on which `famEnc` is injective, the weights
`ε^{(counted) - 1} e^{μ |r0 - exit|_1 + s (exit_y - r0_y)}` sum to at most `famVal (B, false)`. `fam_bound_enc` sums
over encodings, `famB_of` over family keys (the hypothesis `FamB G 0.1935` of `T2Transfer`).
-/

open Finset Classical

namespace QECML

namespace S3Geom

variable {G : S3Geom}

/-! ### Route words -/

/-- The moves of the route part of cluster `i`: its steps, or its leaf. -/
def CRoute.segW (cr : G.CRoute) (i : ℕ) : List G.Move :=
  (cr.a i).map Move.step ++ (cr.lf i).toList.map Move.leaf

/-- The moves before the route part of cluster `j`: the parts of the earlier clusters, each followed by its link. -/
def CRoute.preW (cr : G.CRoute) (j : ℕ) : List G.Move :=
  (List.range j).flatMap fun i => cr.segW i ++ [Move.link (cr.r (i + 1))]

/-- The route word of a cluster route, read from its first root. -/
def CRoute.word (cr : G.CRoute) : List G.Move := cr.preW cr.n ++ cr.segW cr.n

/-- Allowed moves from a grammar state and a block (`St4` runs). -/
def st4Gram (D A0 A1 : ℕ) : St4 → G.Block → List G.Move → Prop
  | _, _, [] => True
  | x, cur, m :: ms => St4.allowed D A0 A1 x cur m ∧ st4Gram D A0 A1 (St4.next x m) (nextBlk cur m) ms

/-- The grammar state after a word. -/
def st4Fin : St4 → List G.Move → St4
  | x, [] => x
  | x, m :: ms => st4Fin (St4.next x m) ms

theorem st4Gram_append (D A0 A1 : ℕ) : ∀ (x : St4) (cur : G.Block) (u v : List G.Move),
    st4Gram D A0 A1 x cur (u ++ v) ↔ st4Gram D A0 A1 x cur u ∧ st4Gram D A0 A1 (st4Fin x u) (endBlock cur u) v
  | x, cur, [], v => by simp [st4Gram, st4Fin, endBlock]
  | x, cur, m :: u, v => by
    rw [List.cons_append, st4Gram, st4Gram, st4Gram_append D A0 A1 (St4.next x m) (nextBlk cur m) u v,
      endBlock_cons]
    simp only [st4Fin, and_assoc]

theorem st4Fin_append : ∀ (x : St4) (u v : List G.Move), st4Fin x (u ++ v) = st4Fin (st4Fin x u) v
  | _, [], _ => rfl
  | x, m :: u, v => st4Fin_append (St4.next x m) u v

theorem gwt_append (g : G.Block → G.Move → ℝ) : ∀ (cur : G.Block) (u v : List G.Move),
    gwt g cur (u ++ v) = gwt g cur u * gwt g (endBlock cur u) v
  | cur, [], v => by simp [gwt, endBlock]
  | cur, m :: u, v => by
    rw [List.cons_append, gwt, gwt, gwt_append g (nextBlk cur m) u v, endBlock_cons]
    ring

/-! ### The family automaton on route words -/

/-- The T2 move weights at the parameters of the T2 summation. -/
noncomputable abbrev tg : G.Block → G.Move → ℝ := t2g 5e-4 0.04305 0.02

theorem famAut_gram_inl (D A0 A1 : ℕ) : ∀ (x : St4) (p : Bool) (cur : G.Block) (ms : List G.Move)
    (rest : List (G.Move ⊕ Unit)),
    (famAut (G := G) D A0 A1).Gram (x, p) cur (ms.map Sum.inl ++ rest) ↔
      st4Gram D A0 A1 x cur ms ∧ (famAut (G := G) D A0 A1).Gram (st4Fin x ms, p) (endBlock cur ms) rest
  | x, p, cur, [], rest => by simp [st4Gram, st4Fin, endBlock]
  | x, p, cur, m :: ms, rest => by
    rw [List.map_cons, List.cons_append, WAut.Gram, st4Gram, endBlock_cons]
    have ih := famAut_gram_inl D A0 A1 (St4.next x m) p (nextBlk cur m) ms rest
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (ih.1 h2).1⟩, (ih.1 h2).2⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, ih.2 ⟨h2, h3⟩⟩⟩

theorem famAut_wt_inl (D A0 A1 : ℕ) : ∀ (x : St4) (p : Bool) (cur : G.Block) (ms : List G.Move)
    (rest : List (G.Move ⊕ Unit)),
    (famAut (G := G) D A0 A1).wt (x, p) cur (ms.map Sum.inl ++ rest) =
      gwt tg cur ms * (famAut (G := G) D A0 A1).wt (st4Fin x ms, p) (endBlock cur ms) rest
  | x, p, cur, [], rest => by simp [gwt, st4Fin, endBlock]
  | x, p, cur, m :: ms, rest => by
    have ih := famAut_wt_inl D A0 A1 (St4.next x m) p (nextBlk cur m) ms rest
    rw [List.map_cons, List.cons_append, endBlock_cons]
    show tg cur m * (famAut (G := G) D A0 A1).wt (St4.next x m, p) (nextBlk cur m) (ms.map Sum.inl ++ rest) =
      tg cur m * gwt tg (nextBlk cur m) ms *
        (famAut (G := G) D A0 A1).wt (st4Fin (St4.next x m) ms, p) (endBlock (nextBlk cur m) ms) rest
    rw [ih]
    ring

/-- A route word with the witness mark inserted after its first `p` moves. -/
def markAt (ms : List G.Move) (p : ℕ) : List (G.Move ⊕ Unit) :=
  (ms.take p).map Sum.inl ++ Sum.inr () :: (ms.drop p).map Sum.inl

theorem famAut_markAt (D A0 A1 : ℕ) (cur : G.Block) (ms : List G.Move) (p : ℕ)
    (hg : st4Gram D A0 A1 .B cur ms) (hfin : st4Fin .B ms ≠ .B) :
    (famAut (G := G) D A0 A1).Gram (.B, false) cur (markAt ms p) ∧
      (famAut (G := G) D A0 A1).wt (.B, false) cur (markAt ms p) = gwt tg cur ms * mkW (st4Fin .B (ms.take p)) := by
  have hsplit : ms = ms.take p ++ ms.drop p := (List.take_append_drop p ms).symm
  rw [hsplit] at hg hfin
  rw [st4Gram_append] at hg
  rw [st4Fin_append] at hfin
  set x := st4Fin .B (ms.take p) with hx
  have hend : (famAut (G := G) D A0 A1).wt (st4Fin x (ms.drop p), true)
      (endBlock (endBlock cur (ms.take p)) (ms.drop p)) [] = 1 := by
    show (famAut (G := G) D A0 A1).e (st4Fin x (ms.drop p), true) = 1
    revert hfin
    cases st4Fin x (ms.drop p) <;> intro hfin <;> first | exact absurd rfl hfin | rfl
  refine ⟨?_, ?_⟩
  · unfold markAt
    rw [famAut_gram_inl]
    refine ⟨hg.1, ?_⟩
    refine ⟨trivial, ?_⟩
    have := (famAut_gram_inl D A0 A1 x true (endBlock cur (ms.take p)) (ms.drop p) []).2 ⟨hg.2, trivial⟩
    rw [List.append_nil] at this
    exact this
  · unfold markAt
    rw [famAut_wt_inl]
    show gwt tg cur (ms.take p) * (mkW x * (famAut (G := G) D A0 A1).wt (x, true) (endBlock cur (ms.take p))
      ((ms.drop p).map Sum.inl)) = _
    have h2 := famAut_wt_inl D A0 A1 x true (endBlock cur (ms.take p)) (ms.drop p) []
    rw [List.append_nil] at h2
    rw [h2, hend]
    conv_rhs => rw [hsplit, gwt_append]
    ring

/-! ### Reading a marked word -/

/-- The moves before and after the first mark of a marked word. -/
def splitMark : List (G.Move ⊕ Unit) → List G.Move × List G.Move
  | [] => ([], [])
  | .inl m :: ts => (m :: (splitMark ts).1, (splitMark ts).2)
  | .inr _ :: ts => ([], ts.filterMap Sum.getLeft?)

theorem splitMark_markAt (ms : List G.Move) (p : ℕ) : splitMark (markAt ms p) = (ms.take p, ms.drop p) := by
  unfold markAt
  generalize ms.take p = u
  generalize ms.drop p = v
  induction u with
  | nil =>
    simp only [List.map_nil, List.nil_append, splitMark, List.filterMap_map]
    congr 1
    induction v with
    | nil => rfl
    | cons a v ih => simp [ih]
  | cons a u ih => simp only [List.map_cons, List.cons_append, splitMark, ih]

/-- The start block of the witness at the mark: the leaf just before the mark, or the current block. -/
def markBlock (r0 : G.Block) (pre : List G.Move) : G.Block :=
  match pre.getLast? with
  | some (.leaf b) => b
  | _ => endBlock r0 pre

/-! ### The witness and the encoding -/

/-- The witness cluster. -/
def Wit.jx : G.Wit → ℕ
  | .on j _ _ => j
  | .off j _ _ _ => j

/-- The branch block of the witness. -/
def Wit.xb : G.Wit → G.Block
  | .on _ xb _ => xb
  | .off _ xb _ _ => xb

/-- The offset of the mark among the moves of cluster `j`: `0` at the root, after the step to `xb`, after the leaf. -/
def markOff (cr : G.CRoute) (j : ℕ) (xb : G.Block) : ℕ :=
  if xb = cr.r j then 0 else if cr.a j = [] then 1 else (cr.a j).idxOf xb + 1

/-- The position of the witness mark in the route word. -/
def markPos (cr : G.CRoute) (wt : G.Wit) : ℕ := (cr.preW wt.jx).length + markOff cr wt.jx wt.xb

/-- The witness word: the walk, then (off-route) the link to the excursion and the excursion's route word. -/
def witWord : G.Wit → List (G.Block ⊕ G.Move)
  | .on _ _ w => w.map Sum.inl
  | .off _ _ w ex => w.map Sum.inl ++ Sum.inr (Move.link (ex.r 0)) :: ex.word.map Sum.inr

/-- **The encoding of a family unit**: first root, counted blocks, exit cover, marked route word, witness word. -/
def famEnc (f : G.CRoute × G.Wit) :
    G.Block × List G.Block × G.Block × List (G.Move ⊕ Unit) × List (G.Block ⊕ G.Move) :=
  (f.1.r 0, f.1.blocks ++ f.2.blocks, f.1.last, markAt f.1.word (markPos f.1 f.2), witWord f.2)

/-! ### The route word of a valid cluster route -/

theorem getLast?_lastOf (r : G.Block) (a : List G.Block) : (r :: a).getLast? = some (lastOf r a) := by
  simp [lastOf, List.getLast?_cons]

theorem segW_blk (cr : G.CRoute) (i : ℕ) : (cr.segW i).map Move.blk = cr.a i ++ (cr.lf i).toList := by
  simp only [CRoute.segW, List.map_append, List.map_map]
  congr 1
  · induction cr.a i with
    | nil => rfl
    | cons b l ih => simp only [List.map_cons, Function.comp_apply, ih]; rfl
  · cases cr.lf i <;> rfl

theorem preW_zero (cr : G.CRoute) : cr.preW 0 = [] := rfl

theorem preW_succ (cr : G.CRoute) (j : ℕ) : cr.preW (j + 1) = cr.preW j ++ (cr.segW j ++ [Move.link (cr.r (j + 1))]) := by
  simp only [CRoute.preW, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The counted blocks of a cluster route are its first root and the blocks of its route word. -/
theorem blocks_eq (cr : G.CRoute) : cr.blocks = cr.r 0 :: cr.word.map Move.blk := by
  have key : ∀ j, cr.r 0 :: ((cr.preW j ++ cr.segW j).map Move.blk) =
      (List.range (j + 1)).flatMap (fun i => cr.r i :: (cr.a i ++ (cr.lf i).toList)) := by
    intro j
    induction j with
    | zero => simp [preW_zero, segW_blk]
    | succ j ih =>
      rw [preW_succ, List.range_succ, List.flatMap_append, ← ih]
      simp only [List.map_append, segW_blk, List.flatMap_singleton, List.map_cons, List.map_nil,
        List.cons_append, List.append_assoc]
      rfl
  rw [CRoute.blocks, CRoute.word, ← key]

theorem blocks_length (cr : G.CRoute) : cr.blocks.length = cr.word.length + 1 := by
  rw [blocks_eq, List.length_cons, List.length_map]

theorem steps_gram (D A0 A1 : ℕ) : ∀ (x : St4) (_ : x ≠ .C) (cur : G.Block) (l : List G.Block),
    S0Chain D A0 (cur :: l) → st4Gram D A0 A1 x cur (l.map Move.step)
  | _, _, _, [], _ => trivial
  | x, hx, cur, b :: l, h => by
    simp only [S0Chain, List.isChain_cons_cons] at h
    refine ⟨?_, steps_gram D A0 A1 (St4.next x (.step b)) ?_ b l h.2⟩
    · cases x
      · exact h.1
      · exact h.1
      · exact h.1
      · exact absurd rfl hx
    · cases x <;> simp [St4.next]

theorem st4Fin_steps_A2 : ∀ (l : List G.Block), st4Fin .A2 (l.map Move.step) = .A2
  | [] => rfl
  | _ :: l => st4Fin_steps_A2 l

theorem st4Fin_steps_ne : ∀ (x : St4) (l : List G.Block), l ≠ [] → st4Fin x (l.map Move.step) ≠ .B
  | x, b :: l, _ => by
    show st4Fin (St4.next x (.step b)) (l.map Move.step) ≠ .B
    cases x
    · cases l with
      | nil => simp [St4.next, st4Fin]
      | cons c l => rw [show St4.next St4.B (Move.step b) = St4.A1 from rfl]; show st4Fin .A2 (l.map Move.step) ≠ .B; rw [st4Fin_steps_A2]; simp
    all_goals (rw [show ∀ y : St4, y ≠ .B → St4.next y (Move.step b) = St4.A2 from fun y hy => by cases y <;> first | exact absurd rfl hy | rfl]; rw [st4Fin_steps_A2]; simp; simp)

theorem st4Fin_steps_two (l : List G.Block) (hl : 2 ≤ l.length) : st4Fin .B (l.map Move.step) = .A2 := by
  match l, hl with
  | _ :: _ :: l, _ => exact st4Fin_steps_A2 l

theorem link_allowed {D A0 A1 : ℕ} {y : St4} (hy : y ≠ .B) {cur b : G.Block} (h1 : D ≤ G.blockDist cur b)
    (h2 : G.blockDist cur b ≤ A1) : St4.allowed D A0 A1 y cur (.link b) := by
  cases y
  · exact absurd rfl hy
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

/-- The route part of a cluster of a valid cluster route, read from its root in state `B`. -/
theorem seg_run {D A0 A1 : ℕ} {cr : G.CRoute} (hok : cr.OK D A0 A1) {i : ℕ} (hi : i ≤ cr.n) :
    st4Gram D A0 A1 .B (cr.r i) (cr.segW i) ∧ st4Fin .B (cr.segW i) ≠ .B ∧
      endBlock (cr.r i) (cr.segW i) = lastOf (cr.r i) (cr.a i) := by
  obtain ⟨hch, hlf, hlo, -⟩ := hok
  by_cases ha : cr.a i = []
  · obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 ((hlf i hi).1 ha)
    have hseg : cr.segW i = [Move.leaf l] := by simp [CRoute.segW, ha, hl]
    rw [hseg, ha]
    refine ⟨⟨hlo i hi l hl, trivial⟩, by simp [st4Fin, St4.next], ?_⟩
    simp [endBlock, lastOf]
  · have hnone : cr.lf i = none := by
      cases h : cr.lf i with
      | none => rfl
      | some l => exact absurd ((hlf i hi).2 (by rw [h]; rfl)) ha
    have hseg : cr.segW i = (cr.a i).map Move.step := by simp [CRoute.segW, hnone]
    rw [hseg]
    exact ⟨steps_gram D A0 A1 .B (by simp) (cr.r i) (cr.a i) (hch i hi), st4Fin_steps_ne .B (cr.a i) ha,
      endBlock_steps (cr.r i) (cr.a i) (getLast?_lastOf _ _)⟩

/-- The moves before cluster `j` of a valid cluster route end at its root in state `B`. -/
theorem preW_run {D A0 A1 : ℕ} {cr : G.CRoute} (hok : cr.OK D A0 A1) : ∀ j ≤ cr.n,
    st4Gram D A0 A1 .B (cr.r 0) (cr.preW j) ∧ st4Fin .B (cr.preW j) = .B ∧
      endBlock (cr.r 0) (cr.preW j) = cr.r j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨trivial, rfl, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hg, hf, he⟩ := ih (by omega)
    obtain ⟨sg, sf, se⟩ := seg_run hok (i := j) (by omega)
    have hlink := hok.2.2.2 j (by omega)
    rw [preW_succ, st4Gram_append, st4Fin_append, endBlock_append, hf, he, st4Gram_append, st4Fin_append,
      endBlock_append, se]
    refine ⟨⟨hg, sg, link_allowed sf hlink.1 hlink.2, trivial⟩, ?_, rfl⟩
    show St4.next (st4Fin St4.B (cr.segW j)) (Move.link (cr.r (j + 1))) = St4.B
    cases st4Fin St4.B (cr.segW j) <;> rfl

/-- **The route word of a valid cluster route** is allowed from its first root in state `B`, does not end right after
a link, and ends at the exit block. -/
theorem word_run {D A0 A1 : ℕ} {cr : G.CRoute} (hok : cr.OK D A0 A1) :
    st4Gram D A0 A1 .B (cr.r 0) cr.word ∧ st4Fin .B cr.word ≠ .B ∧ endBlock (cr.r 0) cr.word = cr.last := by
  obtain ⟨hg, hf, he⟩ := preW_run hok cr.n le_rfl
  obtain ⟨sg, sf, se⟩ := seg_run hok (i := cr.n) le_rfl
  rw [CRoute.word, st4Gram_append, st4Fin_append, endBlock_append, hf, he, se]
  exact ⟨⟨hg, sg⟩, sf, rfl⟩

/-! ### The witness automaton -/

/-- The state after a word of a weighted automaton. -/
def WAut.fq {Q T : Type} (M : WAut G Q T) : Q → List T → Q
  | q, [] => q
  | q, t :: ts => M.fq (M.nq q t) ts

theorem WAut.fq_append {Q T : Type} (M : WAut G Q T) : ∀ (q : Q) (u v : List T), M.fq q (u ++ v) = M.fq (M.fq q u) v
  | _, [], _ => rfl
  | q, t :: u, v => WAut.fq_append M (M.nq q t) u v

/-- With constant token weights `ε`, the weight of a word is `ε^length` times the end weight of its final state. -/
theorem WAut.wt_const {Q T : Type} (M : WAut G Q T) {ε : ℝ} (hg : ∀ q cur t, M.g q cur t = ε) :
    ∀ (q : Q) (cur : G.Block) (r : List T), M.wt q cur r = ε ^ r.length * M.e (M.fq q r)
  | q, _, [] => by simp [WAut.wt, WAut.fq]
  | q, cur, t :: ts => by
    rw [WAut.wt, hg, WAut.wt_const M hg (M.nq q t) (M.nb cur t) ts, List.length_cons, pow_succ]
    simp only [WAut.fq]
    ring

/-- **Witness words**: a walk of `S0` steps (state `inl k`, `k` steps so far, counted up to `c`), then possibly a link
in `S1` to an excursion and the excursion's moves (state `inr x`). Every token weighs `ε`; a word ends after at least
`c` walk steps, or in the excursion state `A2`. -/
noncomputable def witAut (D A0 A1 c : ℕ) (ε : ℝ) : WAut G (ℕ ⊕ St4) (G.Block ⊕ G.Move) where
  allowed := fun q cur t => match q, t with
    | .inl _, .inl b => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A0
    | .inl _, .inr (.link b) => D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ A1
    | .inr x, .inr m => St4.allowed D A0 A1 x cur m
    | _, _ => False
  nq := fun q t => match q, t with
    | .inl k, .inl _ => .inl (min (k + 1) c)
    | .inl _, .inr _ => .inr .B
    | .inr x, .inr m => .inr (St4.next x m)
    | .inr x, .inl _ => .inr x
  nb := fun cur t => match t with
    | .inl b => b
    | .inr m => nextBlk cur m
  g := fun _ _ _ => ε
  e := fun q => match q with
    | .inl k => if c ≤ k then 1 else 0
    | .inr x => if x = .A2 then 1 else 0

/-- Bellman values of the witness automaton: on-route walks of at least `c - k` more steps, or an off-route walk, a
link and an excursion. -/
noncomputable def witVal (c : ℕ) : ℕ ⊕ St4 → ℝ
  | .inl k => ((5e-4 * 208) ^ (c - k) + 5e-4 * 1008 * 0.0136) / (1 - 5e-4 * 208)
  | .inr x => exVal x

theorem witVal_nonneg (c : ℕ) (q : ℕ ⊕ St4) : 0 ≤ witVal c q := by
  rcases q with k | x
  · exact div_nonneg (add_nonneg (pow_nonneg (by norm_num) _) (by norm_num)) (by norm_num)
  · cases x <;> norm_num [witVal, exVal]

/-- **The witness factor**: witness words from any state and block weigh at most `witVal`. -/
theorem witAut_le (hD : G.D = 5) (c N : ℕ) (q : ℕ ⊕ St4) (cur : G.Block) :
    (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).V N q cur ≤ witVal c q := by
  refine WAut.V_le _ (fun _ _ _ => by norm_num [witAut]) (witVal c) (fun q cur => ?_) (witVal_nonneg c) N q cur
  rw [Fintype.sum_sum_type]
  rcases q with k | x
  · -- the walk: steps in `S0`, or the link to an excursion
    have hsteps : ∑ b : G.Block, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
        (.inl b) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur (.inl b) *
          witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k) (.inl b)) else 0) ≤
        5e-4 * 208 * witVal c (.inl (min (k + 1) c)) := by
      refine (sum_ite_bound
        (Q := fun b => (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur (.inl b))
        (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 4) (fun b h => h)
        (g := fun b => (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur (.inl b))
        (w := fun b => witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k) (.inl b)))
        (fun _ => (5e-4 : ℝ)) (fun b => rfl) (fun b => by norm_num) (witVal_nonneg c (.inl (min (k + 1) c)))
        (fun b _ => le_rfl)).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (card_S0_le hD cur) (witVal_nonneg c _)
    have hmoves : ∑ m : G.Move, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
        (.inr m) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur (.inr m) *
          witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k) (.inr m)) else 0) ≤
        5e-4 * 1008 * 0.0136 := by
      rw [sum_move]
      have h1 : ∑ b : G.Block, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
          (.inr (.step b)) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur
            (.inr (.step b)) * witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k)
              (.inr (.step b))) else 0) = 0 :=
        Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
      have h3 : ∑ b : G.Block, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
          (.inr (.leaf b)) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur
            (.inr (.leaf b)) * witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k)
              (.inr (.leaf b))) else 0) = 0 :=
        Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
      have h2 : ∑ b : G.Block, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
          (.inr (.link b)) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur
            (.inr (.link b)) * witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k)
              (.inr (.link b))) else 0) ≤ 5e-4 * 1008 * 0.0136 := by
        refine (sum_ite_bound
          (Q := fun b => (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inl k) cur
            (.inr (.link b)))
          (fun b => G.D ≤ G.blockDist cur b ∧ G.blockDist cur b ≤ G.D - 1 + 12) (fun b h => h)
          (g := fun b => (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inl k) cur (.inr (.link b)))
          (w := fun b => witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inl k)
            (.inr (.link b))))
          (fun _ => (5e-4 : ℝ)) (fun b => rfl) (fun b => by norm_num) (witVal_nonneg c (.inr .B))
          (fun b _ => le_rfl)).trans ?_
        rw [mul_comm]
        have := mul_le_mul_of_nonneg_right (card_S1_le hD cur) (witVal_nonneg c (.inr .B))
        refine this.trans (le_of_eq ?_)
        norm_num [witVal, exVal]
      rw [h1, h3]
      linarith
    have he : (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).e (.inl k) = if c ≤ k then 1 else 0 := rfl
    rw [he]
    refine le_trans (add_le_add le_rfl (add_le_add hsteps hmoves)) ?_
    simp only [witVal]
    by_cases hck : c ≤ k
    · rw [ite_eq_left hck, show min (k + 1) c = c by omega, Nat.sub_self, show c - k = 0 by omega, pow_zero]
      norm_num
    · rw [ite_eq_right hck, show min (k + 1) c = k + 1 by omega]
      have hck' : c - k = (c - (k + 1)) + 1 := by omega
      rw [hck', pow_succ]
      generalize (5e-4 * 208 : ℝ) ^ (c - (k + 1)) = t
      apply le_of_eq
      field_simp
      ring
  · -- the excursion: the Bellman inequality of the excursion automaton
    have hwalk : ∑ b : G.Block, (if (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).allowed (.inr x) cur
        (.inl b) then (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).g (.inr x) cur (.inl b) *
          witVal c ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) c 5e-4).nq (.inr x) (.inl b)) else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => h)
    rw [hwalk, zero_add]
    have hm := st4_moves_le (gm := fun _ _ => (5e-4 : ℝ)) (fun _ _ => by norm_num)
      (fun cur => card_S0_le hD cur) (fun cur => card_S1_le hD cur) (fun cur => card_S0_le hD cur) exVal
      (fun q => by cases q <;> norm_num [exVal]) x cur
    show (if x = .A2 then (1 : ℝ) else 0) +
      ∑ m : G.Move, (if St4.allowed G.D (G.D - 1 + 4) (G.D - 1 + 12) x cur m then (5e-4 : ℝ) * exVal (St4.next x m)
        else 0) ≤ exVal x
    cases x with
    | B =>
      simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
      refine hm.trans ?_
      norm_num [exVal]
    | A1 =>
      simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
      refine hm.trans ?_
      norm_num [exVal]
    | A2 =>
      simp only [↓reduceIte] at hm ⊢
      have e2 : exVal St4.A2 = 1.1238 := rfl
      have e1 : exVal St4.B = 0.0136 := rfl
      rw [e2, e1] at hm
      rw [e2]
      linarith
    | C =>
      simp only [reduceCtorEq, ↓reduceIte, zero_add] at hm ⊢
      refine hm.trans ?_
      norm_num [exVal]

/-! ### The witness mark of a valid family unit -/

theorem word_split {cr : G.CRoute} : ∀ (d j : ℕ), j + d = cr.n → ∃ R, cr.word = cr.preW j ++ (cr.segW j ++ R) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    exact ⟨[], by rw [CRoute.word, show j = cr.n by omega, List.append_nil]⟩
  | succ d ih =>
    intro j hj
    obtain ⟨R, hR⟩ := ih (j + 1) (by omega)
    refine ⟨Move.link (cr.r (j + 1)) :: (cr.segW (j + 1) ++ R), ?_⟩
    rw [hR, preW_succ]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem take_markPos {cr : G.CRoute} {j : ℕ} (hj : j ≤ cr.n) {k : ℕ} (hk : k ≤ (cr.segW j).length) :
    cr.word.take ((cr.preW j).length + k) = cr.preW j ++ (cr.segW j).take k := by
  obtain ⟨R, hR⟩ := word_split (cr := cr) (cr.n - j) j (by omega)
  rw [hR, List.take_length_add_append, List.take_append_of_le_length hk]

theorem markBlock_leaf {r0 b : G.Block} {pre : List G.Move} (h : pre.getLast? = some (.leaf b)) :
    markBlock r0 pre = b := by
  unfold markBlock
  rw [h]

theorem markBlock_not_leaf {r0 : G.Block} {pre : List G.Move} (h : ∀ b, pre.getLast? ≠ some (.leaf b)) :
    markBlock r0 pre = endBlock r0 pre := by
  unfold markBlock
  cases hp : pre.getLast? with
  | none => rfl
  | some m =>
    cases m with
    | step b => rfl
    | link b => rfl
    | leaf b => exact absurd hp (h b)

/-- The minimal length of an on-route witness walk from a mark state (span `Sw > A0`). -/
def cmin : St4 → ℕ
  | .B => 2
  | .A1 => 1
  | .A2 => 0
  | .C => 1

/-- **The mark of a branch block** `xb` of cluster `j` (the root, a block of the route part, or the leaf): the
offset fits in the cluster's moves, the start block read from the word is `xb`, the state is `B` only at the root,
and in the states `A1`, `C` the block `xb` is within `A0` of the root. -/
theorem mark_run {D A0 A1 : ℕ} {cr : G.CRoute} (hok : cr.OK D A0 A1) {j : ℕ} (hj : j ≤ cr.n) {xb : G.Block}
    (hbr0 : cr.a j = [] → cr.lf j = some xb ∨ xb = cr.r j) (hbr1 : cr.a j ≠ [] → xb ∈ cr.r j :: cr.a j) :
    markOff cr j xb ≤ (cr.segW j).length ∧
      markBlock (cr.r 0) (cr.preW j ++ (cr.segW j).take (markOff cr j xb)) = xb ∧
      (st4Fin .B ((cr.segW j).take (markOff cr j xb)) = .B → xb = cr.r j) ∧
      (st4Fin .B ((cr.segW j).take (markOff cr j xb)) = .A1 ∨
        st4Fin .B ((cr.segW j).take (markOff cr j xb)) = .C → G.blockDist (cr.r j) xb ≤ A0) := by
  have hpre := preW_run hok j hj
  obtain ⟨hch, hlf, hlo, -⟩ := hok
  by_cases hxr : xb = cr.r j
  · have hk : markOff cr j xb = 0 := by simp [markOff, hxr]
    rw [hk, List.take_zero, List.append_nil]
    refine ⟨Nat.zero_le _, ?_, fun _ => hxr, fun h => by rcases h with h | h <;> simp [st4Fin] at h⟩
    rcases j with _ | j
    · simp [preW_zero, markBlock, endBlock, hxr]
    · rw [markBlock_not_leaf, hpre.2.2, hxr]
      intro b
      rw [preW_succ]
      simp
  · by_cases ha : cr.a j = []
    · have hl : cr.lf j = some xb := by
        rcases hbr0 ha with h | h
        · exact h
        · exact absurd h hxr
      have hk : markOff cr j xb = 1 := by simp [markOff, hxr, ha]
      have hseg : cr.segW j = [Move.leaf xb] := by simp [CRoute.segW, ha, hl]
      rw [hk, hseg]
      refine ⟨le_rfl, markBlock_leaf (by simp), fun h => by simp [st4Fin, St4.next] at h,
        fun _ => (hlo j hj xb hl).2⟩
    · have hnone : cr.lf j = none := by
        cases h : cr.lf j with
        | none => rfl
        | some l => exact absurd ((hlf j hj).2 (by rw [h]; rfl)) ha
      have hseg : cr.segW j = (cr.a j).map Move.step := by simp [CRoute.segW, hnone]
      have hxa : xb ∈ cr.a j := by
        rcases List.mem_cons.1 (hbr1 ha) with h | h
        · exact absurd h hxr
        · exact h
      have hidx := List.idxOf_lt_length_of_mem hxa
      have hk : markOff cr j xb = (cr.a j).idxOf xb + 1 := by simp [markOff, hxr, ha]
      rw [hk, hseg, ← List.map_take]
      have htake : (cr.a j).take ((cr.a j).idxOf xb + 1) = (cr.a j).take ((cr.a j).idxOf xb) ++ [xb] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hidx, List.getElem_idxOf hidx]
        rfl
      refine ⟨by rw [List.length_map]; omega, ?_, ?_, ?_⟩
      · rw [markBlock_not_leaf, endBlock_append, hpre.2.2, htake]
        · exact endBlock_steps (cr.r j) _ (by rw [← List.cons_append, List.getLast?_append]; simp)
        · intro b
          rw [htake, List.map_append, ← List.append_assoc, List.getLast?_append]
          simp
      · intro h
        exfalso
        have hne : (cr.a j).take ((cr.a j).idxOf xb + 1) ≠ [] := by rw [htake]; simp
        exact st4Fin_steps_ne .B _ hne h
      · intro h
        rcases hidx0 : (cr.a j).idxOf xb with _ | i
        · -- the first step of the part
          obtain ⟨a0, as, has⟩ := List.exists_cons_of_ne_nil ha
          have hx0 : xb = a0 := by
            by_contra hne
            rw [has, List.idxOf_cons_ne as (Ne.symm hne)] at hidx0
            exact Nat.succ_ne_zero _ hidx0
          have hc := hch j hj
          rw [has] at hc
          simp only [S0Chain, List.isChain_cons_cons] at hc
          rw [hx0]
          exact hc.1.2
        · -- a later step: the state is `A2`
          exfalso
          have h2 : st4Fin .B (((cr.a j).take ((cr.a j).idxOf xb + 1)).map Move.step) = .A2 := by
            apply st4Fin_steps_two
            rw [List.length_take]
            omega
          rcases h with h | h <;> rw [h2] at h <;> exact absurd h (by simp)

/-- An on-route walk has at least `cmin` steps in the mark state. -/
theorem walk_cmin {D A0 Sw : ℕ} (hSw : A0 < Sw) {r xb : G.Block} {w : List G.Block} {x : St4}
    (hch : S0Chain D A0 (xb :: w)) (hspan : Sw ≤ G.blockDist r (lastOf xb w))
    (hB : x = .B → xb = r) (hAC : x = .A1 ∨ x = .C → G.blockDist r xb ≤ A0) : cmin x ≤ w.length := by
  rcases w with _ | ⟨w1, _ | ⟨w2, w⟩⟩
  · have h0 : lastOf xb [] = xb := by simp [lastOf]
    rw [h0] at hspan
    cases x
    · rw [hB rfl, G.blockDist_self] at hspan
      omega
    · have := hAC (Or.inl rfl)
      omega
    · simp [cmin]
    · have := hAC (Or.inr rfl)
      omega
  · have h1 : lastOf xb [w1] = w1 := by simp [lastOf]
    rw [h1] at hspan
    simp only [S0Chain, List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    cases x
    · rw [hB rfl] at hch
      omega
    · simp [cmin]
    · simp [cmin]
    · simp [cmin]
  · cases x <;> simp [cmin]

/-! ### Witness words of a valid witness -/

theorem witAut_walk (D A0 A1 c : ℕ) (ε : ℝ) : ∀ (k : ℕ) (_ : k ≤ c) (cur : G.Block) (w : List G.Block)
    (rest : List (G.Block ⊕ G.Move)), S0Chain D A0 (cur :: w) →
    ((witAut (G := G) D A0 A1 c ε).Gram (.inl k) cur (w.map Sum.inl ++ rest) ↔
      (witAut (G := G) D A0 A1 c ε).Gram (.inl (min (k + w.length) c)) (lastOf cur w) rest) ∧
    (witAut (G := G) D A0 A1 c ε).fq (.inl k) (w.map Sum.inl ++ rest) =
      (witAut (G := G) D A0 A1 c ε).fq (.inl (min (k + w.length) c)) rest
  | k, hk, cur, [], rest, _ => by
    have hm : min (k + 0) c = k := by omega
    simp only [List.map_nil, List.nil_append, List.length_nil, hm]
    constructor <;> simp [lastOf]
  | k, hk, cur, b :: w, rest, hch => by
    simp only [S0Chain, List.isChain_cons_cons] at hch
    have ih := witAut_walk D A0 A1 c ε (min (k + 1) c) (Nat.min_le_right _ _) b w rest hch.2
    have hmin : min (min (k + 1) c + w.length) c = min (k + (w.length + 1)) c := by omega
    rw [hmin] at ih
    have hlast : lastOf cur (b :: w) = lastOf b w := Stage1.lastOf_cons cur b w
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.cons_append, WAut.Gram, List.length_cons, hlast]
      exact ⟨fun h => ih.1.1 h.2, fun h => ⟨hch.1, ih.1.2 h⟩⟩
    · rw [List.map_cons, List.cons_append, WAut.fq, List.length_cons]
      exact ih.2

theorem witAut_exc (D A0 A1 c : ℕ) (ε : ℝ) : ∀ (x : St4) (cur : G.Block) (ms : List G.Move),
    ((witAut (G := G) D A0 A1 c ε).Gram (.inr x) cur (ms.map Sum.inr) ↔ st4Gram D A0 A1 x cur ms) ∧
    (witAut (G := G) D A0 A1 c ε).fq (.inr x) (ms.map Sum.inr) = .inr (st4Fin x ms)
  | x, cur, [] => ⟨by simp [st4Gram, WAut.Gram], rfl⟩
  | x, cur, m :: ms => by
    have ih := witAut_exc D A0 A1 c ε (St4.next x m) (nextBlk cur m) ms
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, WAut.Gram, st4Gram]
      exact and_congr Iff.rfl ih.1
    · rw [List.map_cons, WAut.fq]
      exact ih.2

/-- The excursion's route word ends in state `A2` (its last part spans more than `A0`, so it has two or more
steps). -/
theorem word_fin_A2 {D A0 A1 Sw : ℕ} (hSw : A0 < Sw) {ex : G.CRoute} (hok : ex.OK D A0 A1)
    (hspan : Sw ≤ G.blockDist (ex.r ex.n) ex.last) : st4Fin .B ex.word = .A2 := by
  have hpf := (preW_run hok ex.n le_rfl).2.1
  rw [CRoute.word, st4Fin_append, hpf]
  have hlen : 2 ≤ (ex.a ex.n).length := by
    rcases h : ex.a ex.n with _ | ⟨b1, _ | ⟨b2, l⟩⟩
    · have hl : ex.last = ex.r ex.n := by simp [CRoute.last, h, lastOf]
      rw [hl, G.blockDist_self] at hspan
      omega
    · have hl : ex.last = b1 := by simp [CRoute.last, h, lastOf]
      have hc := hok.1 ex.n le_rfl
      rw [h] at hc
      simp only [S0Chain, List.isChain_cons_cons, List.isChain_singleton, and_true] at hc
      rw [hl] at hspan
      omega
    · simp
  have ha : ex.a ex.n ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hnone : ex.lf ex.n = none := by
    cases h : ex.lf ex.n with
    | none => rfl
    | some l => exact absurd ((hok.2.1 ex.n le_rfl).2 (by rw [h]; rfl)) ha
  have hseg : ex.segW ex.n = (ex.a ex.n).map Move.step := by simp [CRoute.segW, hnone]
  rw [hseg]
  exact st4Fin_steps_two _ hlen

/-- The block of a witness token. -/
def witBlk : G.Block ⊕ G.Move → G.Block
  | .inl b => b
  | .inr m => m.blk

theorem witWord_blocks (wt : G.Wit) : (witWord wt).map witBlk = wt.blocks := by
  cases wt with
  | on j xb w =>
    simp only [witWord, Wit.blocks, List.map_map]
    induction w with
    | nil => rfl
    | cons b w ih => simp only [List.map_cons, Function.comp_apply, ih]; rfl
  | off jx xb w ex =>
    simp only [witWord, Wit.blocks, List.map_append, List.map_map, List.map_cons, blocks_eq ex]
    congr 1
    induction w with
    | nil => rfl
    | cons b w ih => simp only [List.map_cons, Function.comp_apply, ih]; rfl

theorem witWord_length (wt : G.Wit) : (witWord wt).length = wt.blocks.length := by
  rw [← witWord_blocks, List.length_map]

/-- **The witness word of a valid witness** is a word of the witness automaton from the branch block, accepted at its
end, provided an on-route walk has at least `c` steps. -/
theorem wit_run {D A0 A1 Sw : ℕ} (hSw : A0 < Sw) {cr : G.CRoute} {wt : G.Wit} (hwok : wt.OK D A0 A1 Sw cr) (c : ℕ)
    (ε : ℝ) (hc : ∀ j xb w, wt = .on j xb w → c ≤ w.length) :
    (witAut (G := G) D A0 A1 c ε).Gram (.inl 0) wt.xb (witWord wt) ∧
      (witAut (G := G) D A0 A1 c ε).e ((witAut (G := G) D A0 A1 c ε).fq (.inl 0) (witWord wt)) = 1 := by
  cases wt with
  | on j xb w =>
    obtain ⟨-, -, hch, -⟩ := hwok
    have hcw := hc j xb w rfl
    have h := witAut_walk D A0 A1 c ε 0 (Nat.zero_le _) xb w [] hch
    rw [List.append_nil] at h
    refine ⟨h.1.2 trivial, ?_⟩
    rw [show witWord (.on j xb w) = w.map Sum.inl from rfl, h.2]
    show (if c ≤ min (0 + w.length) c then (1 : ℝ) else 0) = 1
    rw [ite_eq_left (by omega)]
  | off jx xb w ex =>
    obtain ⟨-, -, hch, hexok, hlo, hhi, hspan⟩ := hwok
    have h := witAut_walk D A0 A1 c ε 0 (Nat.zero_le _) xb w (Sum.inr (Move.link (ex.r 0)) :: ex.word.map Sum.inr) hch
    have hl := witAut_link D A0 A1 c ε (min (0 + w.length) c) (lastOf xb w) (ex.r 0) (ex.word.map Sum.inr)
    have hx := witAut_exc (G := G) D A0 A1 c ε .B (ex.r 0) ex.word
    refine ⟨h.1.2 (hl.1.2 ⟨⟨hlo, hhi⟩, hx.1.2 (word_run hexok).1⟩), ?_⟩
    rw [show witWord (.off jx xb w ex) = w.map Sum.inl ++ Sum.inr (Move.link (ex.r 0)) :: ex.word.map Sum.inr from rfl,
      h.2, hl.2, hx.2, word_fin_A2 hSw hexok hspan]
    rfl
where
  witAut_link (D A0 A1 c : ℕ) (ε : ℝ) (k : ℕ) (cur t : G.Block) (rest : List (G.Block ⊕ G.Move)) :
      ((witAut (G := G) D A0 A1 c ε).Gram (.inl k) cur (Sum.inr (Move.link t) :: rest) ↔
        (D ≤ G.blockDist cur t ∧ G.blockDist cur t ≤ A1) ∧ (witAut (G := G) D A0 A1 c ε).Gram (.inr .B) t rest) ∧
      (witAut (G := G) D A0 A1 c ε).fq (.inl k) (Sum.inr (Move.link t) :: rest) =
        (witAut (G := G) D A0 A1 c ε).fq (.inr .B) rest :=
    ⟨Iff.rfl, rfl⟩

/-! ### The family bound -/

theorem witVal_cmin (x : St4) : witVal (cmin x) (.inl 0) = mkW x := by
  cases x <;> norm_num [witVal, cmin, mkW]

theorem famAut_g_nonneg (D A0 A1 : ℕ) (q : St4 × Bool) (cur : G.Block) (t : G.Move ⊕ Unit) :
    0 ≤ (famAut (G := G) D A0 A1).g q cur t := by
  obtain ⟨x, p⟩ := q
  rcases t with m | u
  · exact t2g_nonneg (by norm_num) _ _ _ _
  · exact mkW_nonneg x

theorem famAut_e_nonneg (D A0 A1 : ℕ) (q : St4 × Bool) : 0 ≤ (famAut (G := G) D A0 A1).e q := by
  obtain ⟨x, p⟩ := q
  cases x <;> cases p <;> norm_num [famAut]

theorem witAut_e_nonneg (D A0 A1 c : ℕ) (ε : ℝ) (q : ℕ ⊕ St4) : 0 ≤ (witAut (G := G) D A0 A1 c ε).e q := by
  rcases q with k | x
  · show 0 ≤ (if c ≤ k then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · show 0 ≤ (if x = .A2 then (1 : ℝ) else 0)
    split_ifs <;> norm_num

/-- **The family bound** (at `(D, a0, a1) = (5, 4, 12)`, `ε = 5e-4`, `μ = 0.04305`, `s = 0.02`):
over a finite set of valid family units from a root `r0` on which the encoding `famEnc` is injective, the weights
`ε^{(counted blocks) - 1} e^{μ |r0 - exit|_1 + s (exit_y - r0_y)}` sum to at most `famVal (B, false) = 0.1935`. -/
theorem fam_bound (hD : G.D = 5) (r0 : G.Block) (F : Finset (G.CRoute × G.Wit))
    (hF : ∀ f ∈ F, f.1.r 0 = r0 ∧ f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
      f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1)
    (hinj : Set.InjOn famEnc (F : Set (G.CRoute × G.Wit))) :
    ∑ f ∈ F, (5e-4 : ℝ) ^ ((f.1.blocks ++ f.2.blocks).length - 1) *
      Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) ≤
      famVal (.B, false) := by
  have hSw : G.D - 1 + 4 < 12 + 2 - G.D := by omega
  set mw : G.CRoute × G.Wit → List (G.Move ⊕ Unit) := fun f => markAt f.1.word (markPos f.1 f.2) with hmw
  -- the facts of one family unit
  have hunit : ∀ f ∈ F,
      (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).Gram (.B, false) r0 (mw f) ∧
      (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).wt (.B, false) r0 (mw f) =
        gwt tg r0 f.1.word * mkW (st4Fin .B (splitMark (mw f)).1) ∧
      f.1.word = (splitMark (mw f)).1 ++ (splitMark (mw f)).2 ∧
      endBlock r0 f.1.word = f.1.last ∧
      (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (splitMark (mw f)).1)) 5e-4).Gram (.inl 0)
        (markBlock r0 (splitMark (mw f)).1) (witWord f.2) ∧
      (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (splitMark (mw f)).1)) 5e-4).e
        ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (splitMark (mw f)).1)) 5e-4).fq
          (.inl 0) (witWord f.2)) = 1 := by
    intro f hf
    obtain ⟨cr, wt⟩ := f
    obtain ⟨hr0, hok, hwok⟩ : cr.r 0 = r0 ∧ cr.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
        wt.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) cr := hF (cr, wt) hf
    obtain ⟨hg, hfin, hend⟩ := word_run hok
    rw [hr0] at hg hend
    have hsp : splitMark (mw (cr, wt)) = (cr.word.take (markPos cr wt), cr.word.drop (markPos cr wt)) :=
      splitMark_markAt _ _
    obtain ⟨hgram, hwt⟩ := famAut_markAt G.D (G.D - 1 + 4) (G.D - 1 + 12) r0 cr.word (markPos cr wt) hg hfin
    rw [hsp]
    refine ⟨hgram, hwt, (List.take_append_drop _ _).symm, hend, ?_⟩
    -- the mark: cluster, offset, state and branch block
    have hjb : wt.jx ≤ cr.n ∧ (cr.a wt.jx = [] → cr.lf wt.jx = some wt.xb ∨ wt.xb = cr.r wt.jx) ∧
        (cr.a wt.jx ≠ [] → wt.xb ∈ cr.r wt.jx :: cr.a wt.jx) := by
      cases wt with
      | on j xb w =>
        obtain ⟨hj, hif, -, -⟩ := hwok
        show j ≤ cr.n ∧ (cr.a j = [] → cr.lf j = some xb ∨ xb = cr.r j) ∧ (cr.a j ≠ [] → xb ∈ cr.r j :: cr.a j)
        refine ⟨hj, fun ha => ?_, fun ha => ?_⟩
        · rw [ite_eq_left ha] at hif
          exact Or.inl hif
        · rw [ite_eq_right ha] at hif
          exact hif
      | off jx xb w ex =>
        obtain ⟨hj, hif, -⟩ := hwok
        show jx ≤ cr.n ∧ (cr.a jx = [] → cr.lf jx = some xb ∨ xb = cr.r jx) ∧
          (cr.a jx ≠ [] → xb ∈ cr.r jx :: cr.a jx)
        refine ⟨hj, fun ha => ?_, fun ha => ?_⟩
        · rw [ite_eq_left ha] at hif
          rcases hif with h | h
          · exact Or.inl h
          · exact Or.inr h.1
        · rw [ite_eq_right ha] at hif
          exact hif
    obtain ⟨hj, hbr0, hbr1⟩ := hjb
    obtain ⟨hk, hmb, hstB, hstAC⟩ := mark_run hok hj hbr0 hbr1
    have htake : cr.word.take (markPos cr wt) = cr.preW wt.jx ++ (cr.segW wt.jx).take (markOff cr wt.jx wt.xb) :=
      take_markPos hj hk
    have hst : st4Fin .B (cr.word.take (markPos cr wt)) =
        st4Fin .B ((cr.segW wt.jx).take (markOff cr wt.jx wt.xb)) := by
      rw [htake, st4Fin_append, (preW_run hok wt.jx hj).2.1]
    have hxb : markBlock r0 (cr.word.take (markPos cr wt)) = wt.xb := by
      rw [htake, ← hr0]
      exact hmb
    show (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (cr.word.take (markPos cr wt)))) 5e-4).Gram
        (.inl 0) (markBlock r0 (cr.word.take (markPos cr wt))) (witWord wt) ∧
      (witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (cr.word.take (markPos cr wt)))) 5e-4).e
        ((witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin (st4Fin .B (cr.word.take (markPos cr wt)))) 5e-4).fq
          (.inl 0) (witWord wt)) = 1
    rw [hst, hxb]
    refine wit_run hSw hwok _ 5e-4 (fun j xb w he => ?_)
    subst he
    obtain ⟨-, -, hch, hspan⟩ := hwok
    exact walk_cmin hSw hch hspan hstB hstAC
  -- the weight of a unit against its route word and witness word
  have hW : ∀ f ∈ F, (5e-4 : ℝ) ^ ((f.1.blocks ++ f.2.blocks).length - 1) *
      Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) ≤
      gwt tg r0 f.1.word * (5e-4 : ℝ) ^ (witWord f.2).length := by
    intro f hf
    have hend := (hunit f hf).2.2.2.1
    have hlen : (f.1.blocks ++ f.2.blocks).length - 1 = f.1.word.length + (witWord f.2).length := by
      rw [List.length_append, blocks_length, witWord_length]
      omega
    rw [hlen, pow_add, show (tg : G.Block → G.Move → ℝ) = t2g 5e-4 0.04305 0.02 from rfl, gwt_t2g, hend]
    have hb : (bl1 r0 f.1.last : ℝ) ≤ (rnorm r0 f.1.word : ℝ) := by
      have := bdl1_le_rnorm r0 f.1.word
      rw [hend] at this
      exact_mod_cast this
    have hexp : Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) ≤
        Real.exp (0.04305 * (rnorm r0 f.1.word : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) :=
      Real.exp_le_exp.2 (by linarith)
    have hp1 : (0 : ℝ) ≤ (5e-4 : ℝ) ^ f.1.word.length := pow_nonneg (by norm_num) _
    have hp2 : (0 : ℝ) ≤ (5e-4 : ℝ) ^ (witWord f.2).length := pow_nonneg (by norm_num) _
    calc (5e-4 : ℝ) ^ f.1.word.length * (5e-4 : ℝ) ^ (witWord f.2).length *
          Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val))
        ≤ (5e-4 : ℝ) ^ f.1.word.length * (5e-4 : ℝ) ^ (witWord f.2).length *
          Real.exp (0.04305 * (rnorm r0 f.1.word : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hp1 hp2)
      _ = _ := by ring
  refine (Finset.sum_le_sum hW).trans ?_
  -- group the units by their marked word
  rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := F.image mw) (g := mw)
    (fun f hf => Finset.mem_image_of_mem mw hf)]
  have hfib : ∀ m ∈ F.image mw, ∑ f ∈ F with mw f = m, gwt tg r0 f.1.word * (5e-4 : ℝ) ^ (witWord f.2).length ≤
      (famAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12)).wt (.B, false) r0 m := by
    intro m hm
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨-, hwt0, hword0, -, -, -⟩ := hunit f0 hf0
    have hword : ∀ f ∈ F.filter (fun f => mw f = mw f0), f.1.word = f0.1.word := by
      intro f hfm
      rw [Finset.mem_filter] at hfm
      rw [(hunit f hfm.1).2.2.1, hfm.2, ← hword0]
    -- the witness words of the fiber
    set x0 := st4Fin .B (splitMark (mw f0)).1 with hx0
    set b0 := markBlock r0 (splitMark (mw f0)).1 with hb0
    set M := witAut (G := G) G.D (G.D - 1 + 4) (G.D - 1 + 12) (cmin x0) 5e-4 with hM
    have hwt : ∀ f ∈ F.filter (fun f => mw f = mw f0),
        (5e-4 : ℝ) ^ (witWord f.2).length = M.wt (.inl 0) b0 (witWord f.2) := by
      intro f hfm
      rw [Finset.mem_filter] at hfm
      have he := (hunit f hfm.1).2.2.2.2.2
      rw [hfm.2] at he
      rw [WAut.wt_const M (ε := 5e-4) (fun _ _ _ => rfl),
        show M.e (M.fq (.inl 0) (witWord f.2)) = 1 from he, mul_one]
    have hinjw : Set.InjOn (fun f : G.CRoute × G.Wit => witWord f.2)
        ((F.filter (fun f => mw f = mw f0) : Finset _) : Set (G.CRoute × G.Wit)) := by
      intro f hfm f' hfm' hww
      have hww' : witWord f.2 = witWord f'.2 := hww
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hfm hfm'
      refine hinj hfm.1 hfm'.1 ?_
      have hr := (hF f hfm.1).1
      have hr' := (hF f' hfm'.1).1
      have hw1 : f.1.word = f'.1.word := by
        rw [(hunit f hfm.1).2.2.1, (hunit f' hfm'.1).2.2.1, hfm.2, hfm'.2]
      have hl1 : f.1.last = f'.1.last := by
        rw [← (hunit f hfm.1).2.2.2.1, ← (hunit f' hfm'.1).2.2.2.1, hw1]
      have hb1 : f.1.blocks ++ f.2.blocks = f'.1.blocks ++ f'.2.blocks := by
        rw [blocks_eq, blocks_eq, ← witWord_blocks, ← witWord_blocks, hr, hr', hw1, hww']
      show (f.1.r 0, f.1.blocks ++ f.2.blocks, f.1.last, mw f, witWord f.2) =
        (f'.1.r 0, f'.1.blocks ++ f'.2.blocks, f'.1.last, mw f', witWord f'.2)
      rw [hr, hr', hb1, hl1, hfm.2, hfm'.2, hww']
    have hwfib : ∑ f ∈ F with mw f = mw f0, (5e-4 : ℝ) ^ (witWord f.2).length ≤ mkW x0 := by
      rw [Finset.sum_congr rfl hwt, ← Finset.sum_image hinjw]
      refine (WAut.sum_wt_le M (fun _ _ _ => (show (0 : ℝ) ≤ 5e-4 by norm_num)) (witAut_e_nonneg _ _ _ _ _)
        (((F.filter (fun f => mw f = mw f0)).image (fun f : G.CRoute × G.Wit => witWord f.2)).sup List.length)
        (.inl 0) b0 _ ?_).trans ?_
      · intro u hu
        obtain ⟨f, hfm, rfl⟩ := Finset.mem_image.1 hu
        rw [Finset.mem_filter] at hfm
        have hgw := (hunit f hfm.1).2.2.2.2.1
        rw [hfm.2] at hgw
        exact ⟨hgw, Finset.le_sup (f := List.length) hu⟩
      · exact (witAut_le hD (cmin x0) _ (.inl 0) b0).trans (le_of_eq (witVal_cmin x0))
    rw [hwt0]
    calc ∑ f ∈ F with mw f = mw f0, gwt tg r0 f.1.word * (5e-4 : ℝ) ^ (witWord f.2).length
        = gwt tg r0 f0.1.word * ∑ f ∈ F with mw f = mw f0, (5e-4 : ℝ) ^ (witWord f.2).length := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f hfm => ?_
          rw [hword f hfm]
      _ ≤ gwt tg r0 f0.1.word * mkW x0 :=
          mul_le_mul_of_nonneg_left hwfib (gwt_nonneg (t2g_nonneg (by norm_num) _ _) _ _)
  refine (Finset.sum_le_sum hfib).trans ?_
  -- the family automaton
  refine (WAut.sum_wt_le _ (famAut_g_nonneg _ _ _) (famAut_e_nonneg _ _ _) ((F.image mw).sup List.length)
    (.B, false) r0 (F.image mw) ?_).trans (famAut_le hD _ _ _)
  intro m hm
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hm
  exact ⟨(hunit f hf).1, Finset.le_sup (f := List.length) hm⟩

/-- **The family bound over encodings**: over a finite set of encodings of valid family units from `r0`, the
weights (functions of the encoding: its counted blocks and its exit cover) sum to at most `famVal (B, false)`. -/
theorem fam_bound_enc (hD : G.D = 5) (r0 : G.Block)
    (E : Finset (G.Block × List G.Block × G.Block × List (G.Move ⊕ Unit) × List (G.Block ⊕ G.Move)))
    (hE : ∀ e ∈ E, ∃ f : G.CRoute × G.Wit, f.1.r 0 = r0 ∧ f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
      f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1 ∧ famEnc f = e) :
    ∑ e ∈ E, (5e-4 : ℝ) ^ (e.2.1.length - 1) *
      Real.exp (0.04305 * (bl1 r0 e.2.2.1 : ℝ) + 0.02 * ((e.2.2.1.2.val : ℝ) - r0.2.val)) ≤ famVal (.B, false) := by
  classical
  let P : G.CRoute × G.Wit → Prop := fun f => f.1.r 0 = r0 ∧ f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
    f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1
  let dflt : G.CRoute × G.Wit := (⟨0, fun _ => r0, fun _ => [], fun _ => none⟩, .on 0 r0 [])
  let pick : (G.Block × List G.Block × G.Block × List (G.Move ⊕ Unit) × List (G.Block ⊕ G.Move)) →
      G.CRoute × G.Wit := fun e => if h : ∃ f, P f ∧ famEnc f = e then Classical.choose h else dflt
  have hpick : ∀ e ∈ E, P (pick e) ∧ famEnc (pick e) = e := by
    intro e he
    obtain ⟨f, h1, h2, h3, h4⟩ := hE e he
    have h : ∃ f, P f ∧ famEnc f = e := ⟨f, ⟨h1, h2, h3⟩, h4⟩
    have hp : pick e = Classical.choose h := dite_eq_left h
    rw [hp]
    exact Classical.choose_spec h
  have hinjE : Set.InjOn pick (E : Set _) := fun e he e' he' h => by
    rw [← (hpick e he).2, ← (hpick e' he').2, h]
  have hF := fam_bound hD r0 (E.image pick) (fun f hf => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hf
      exact (hpick e he).1)
    (fun f hf f' hf' h => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf)
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf')
      rw [(hpick e he).2, (hpick e' he').2] at h
      rw [h])
  rw [Finset.sum_image hinjE] at hF
  refine le_of_eq_of_le (Finset.sum_congr rfl fun e he => ?_) hF
  have key : ∀ f : G.CRoute × G.Wit, (5e-4 : ℝ) ^ ((famEnc f).2.1.length - 1) *
      Real.exp (0.04305 * (bl1 r0 (famEnc f).2.2.1 : ℝ) + 0.02 * (((famEnc f).2.2.1.2.val : ℝ) - r0.2.val)) =
      (5e-4 : ℝ) ^ ((f.1.blocks ++ f.2.blocks).length - 1) *
        Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) := fun f => rfl
  rw [← key (pick e), (hpick e he).2]

/-- **The family bound in key form** (`FamB` of `T2Transfer`): the family keys from any landing root weigh at most
`famVal (B, false) = 0.1935`. The key is part of the encoding, so one family per key gives an injective encoding. -/
theorem famB_of (hD : G.D = 5) : FamB G 0.1935 := by
  intro r0 K hK
  classical
  let P : G.CRoute × G.Wit → Prop := fun f => f.1.r 0 = r0 ∧ f.1.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) ∧
    f.2.OK G.D (G.D - 1 + 4) (G.D - 1 + 12) (12 + 2 - G.D) f.1
  let dflt : G.CRoute × G.Wit := (⟨0, fun _ => r0, fun _ => [], fun _ => none⟩, .on 0 r0 [])
  let pick : G.Block × List G.Block × G.Block → G.CRoute × G.Wit :=
    fun k => if h : ∃ f, famKey f = k ∧ P f then Classical.choose h else dflt
  have hpick : ∀ k ∈ K, famKey (pick k) = k ∧ P (pick k) := by
    intro k hk
    obtain ⟨f, h1, h2, h3, h4⟩ := hK k hk
    have h : ∃ f, famKey f = k ∧ P f := ⟨f, h1, h2, h3, h4⟩
    have hp : pick k = Classical.choose h := dite_eq_left h
    rw [hp]
    exact Classical.choose_spec h
  have hinjK : Set.InjOn pick (K : Set _) := fun k hk k' hk' h => by
    rw [← (hpick k hk).1, ← (hpick k' hk').1, h]
  have hF := fam_bound hD r0 (K.image pick) (fun f hf => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hf
      exact (hpick k hk).2)
    (fun f hf f' hf' h => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf)
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf')
      have hkey : famKey (pick k) = famKey (pick k') := congrArg (fun e => (e.1, e.2.1, e.2.2.1)) h
      rw [(hpick k hk).1, (hpick k' hk').1] at hkey
      rw [hkey])
  rw [Finset.sum_image hinjK] at hF
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k hk => ?_) hF
  have key : ∀ f : G.CRoute × G.Wit, (5e-4 : ℝ) ^ ((famKey f).2.1.length - 1) *
      Real.exp (0.04305 * (bl1 r0 (famKey f).2.2 : ℝ) + 0.02 * (((famKey f).2.2.2.val : ℝ) - (r0.2.val : ℝ))) =
      (5e-4 : ℝ) ^ ((f.1.blocks ++ f.2.blocks).length - 1) *
        Real.exp (0.04305 * (bl1 r0 f.1.last : ℝ) + 0.02 * ((f.1.last.2.val : ℝ) - r0.2.val)) := fun f => rfl
  rw [← key (pick k), (hpick k hk).1]

end S3Geom

end QECML
