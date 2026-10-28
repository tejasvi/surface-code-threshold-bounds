import QECML.TwoD.T2MetricB

/-!
# The metric constraint of a T2 path (deterministic part)

Along a Nodup `Γ`-chain `l`, distinct steps carry distinct `C_top` edges (`stepE_inj`), so the `C_top` edges of `l`
weigh exactly the sum of their step edges (`wsum_Pl`). A check-check step is a bulk edge between checks at `ℓ1`
distance `1`. Cut `l` into runs of consecutive check nodes; the `ℓ1` displacement of a run, from its first check (its
anchor) to its last check, is at most its number of steps (`runs_le`). With (X) (`path_X_pairs`) this gives
(`metric_pos`):

  `wmin · Σ_{runs ending before a non-check node} |anchor - last check|_1 ≤ wsum(C_top edges of l)`
  `                                                ≤ Σ_{family nodes k of l} pairCost(neighbouring checks of k)`.

On a T2 path the runs that end before a non-check node are its jumps: from the exit check of a family node (or from
the check next to `b₁`) to the entry check of the next family node (or to the check next to `b₂`); `pot_jump` reads
off their displacements.
-/

open Finset Classical

namespace QECML

/-- The `ℓ1` distance of two checks. -/
def cl1 {w h : ℕ} (u v : PVert w h) : ℕ := ndist u.1.val v.1.val + ndist u.2.val v.2.val

theorem cl1_self {w h : ℕ} (u : PVert w h) : cl1 u u = 0 := by
  simp [cl1, ndist]

theorem cl1_comm {w h : ℕ} (u v : PVert w h) : cl1 u v = cl1 v u := by
  simp only [cl1, ndist]
  omega

theorem cl1_triangle {w h : ℕ} (u v z : PVert w h) : cl1 u z ≤ cl1 u v + cl1 v z := by
  simp only [cl1, ndist]
  omega

/-- An edge with two distinct end checks is a bulk edge, and its end checks are at `ℓ1` distance `1`. -/
theorem cl1_of_ends {w h : ℕ} {e : PEdge w h} {u v : PVert w h} (he : e.ends = {u, v}) (huv : u ≠ v) :
    cl1 u v = 1 ∧ S3Geom.isBulk e := by
  have hu : u ∈ e.ends := by rw [he]; simp
  have hv : v ∈ e.ends := by rw [he]; simp
  cases e with
  | hor x y =>
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, trivial⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · simp only [cl1, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [cl1, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
    · exact absurd rfl huv
  | ver x y =>
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, trivial⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · simp only [cl1, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [cl1, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
    · exact absurd rfl huv
  | bot x =>
    simp only [PEdge.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv
  | top x =>
    simp only [PEdge.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv

/-! ### Weights of sums of distinct edges -/

namespace S3Geom

variable {G : S3Geom}

theorem wsum_single_add (wt : G.Ed → ℝ) (e : G.Ed) (X : G.Ed → ZMod 2) (hX : X e = 0) :
    wsum wt ((Pi.single e 1 : G.Ed → ZMod 2) + X) = wt e + wsum wt X := by
  unfold wsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  have h1 : ∀ e' ∈ Finset.univ.erase e,
      (if ((Pi.single e (1 : ZMod 2) : G.Ed → ZMod 2) + X) e' ≠ 0 then wt e' else 0) =
      (if X e' ≠ 0 then wt e' else 0) := by
    intro e' he'
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase he'), zero_add]
  rw [Finset.sum_congr rfl h1]
  simp [hX]

/-- The weight of a sum of pairwise distinct single edges is the sum of their weights. -/
theorem wsum_sum_single (wt : G.Ed → ℝ) (A : Finset ℕ) (f : ℕ → G.Ed)
    (hf : ∀ i ∈ A, ∀ j ∈ A, f i = f j → i = j) :
    wsum wt (∑ i ∈ A, (Pi.single (f i) (1 : ZMod 2) : G.Ed → ZMod 2)) = ∑ i ∈ A, wt (f i) := by
  induction A using Finset.induction_on with
  | empty => simp [wsum]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hX : (∑ i ∈ A, (Pi.single (f i) (1 : ZMod 2) : G.Ed → ZMod 2)) (f a) = 0 := by
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i hi => Pi.single_eq_of_ne (fun h => ?_) _
      have := hf a (Finset.mem_insert_self a A) i (Finset.mem_insert_of_mem hi) h
      exact ha (this ▸ hi)
    rw [wsum_single_add wt _ _ hX,
      ih fun i hi j hj => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)]

end S3Geom

/-! ### Runs -/

section Runs

variable {w h : ℕ} (c : ℕ → Prop) (pt : ℕ → PVert w h)

/-- The anchor of position `i`: the point of the first position of the run of consecutive `c`-positions through
`i`. -/
noncomputable def anchor : ℕ → PVert w h
  | 0 => pt 0
  | i + 1 => if c i ∧ c (i + 1) then anchor i else pt (i + 1)

/-- The `ℓ1` displacement of position `i` from its anchor (zero off `c`). -/
noncomputable def pot (i : ℕ) : ℕ := if c i then cl1 (anchor c pt i) (pt i) else 0

/-- **Runs**: if consecutive `c`-positions have points at `ℓ1` distance at most `1`, the displacements of the runs
that end before position `j` (plus the displacement at `j`) are at most the number of `c`-`c` steps before `j`. -/
theorem runs_le (N : ℕ) (hstep : ∀ i < N, c i → c (i + 1) → cl1 (pt i) (pt (i + 1)) ≤ 1) :
    ∀ j ≤ N, (∑ i ∈ (range j).filter (fun i => c i ∧ ¬ c (i + 1)), pot c pt i) + pot c pt j ≤
      ((range j).filter (fun i => c i ∧ c (i + 1))).card := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [pot, anchor, cl1_self]
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hnot1 : j ∉ (range j).filter (fun i => c i ∧ ¬ c (i + 1)) := by simp
    have hnot2 : j ∉ (range j).filter (fun i => c i ∧ c (i + 1)) := by simp
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hcj : c j <;> by_cases hcj1 : c (j + 1)
    · rw [ite_eq_right (fun h => h.2 hcj1), ite_eq_left ⟨hcj, hcj1⟩, Finset.card_insert_of_notMem hnot2]
      have hpj : pot c pt j = cl1 (anchor c pt j) (pt j) := ite_eq_left hcj
      have hpj1 : pot c pt (j + 1) = cl1 (anchor c pt j) (pt (j + 1)) := by
        unfold pot
        rw [ite_eq_left hcj1]
        simp only [anchor]
        rw [ite_eq_left ⟨hcj, hcj1⟩]
      have h1 := cl1_triangle (anchor c pt j) (pt j) (pt (j + 1))
      have h2 := hstep j (by omega) hcj hcj1
      omega
    · rw [ite_eq_left ⟨hcj, hcj1⟩, ite_eq_right (fun h => hcj1 h.2), Finset.sum_insert hnot1]
      have hpj1 : pot c pt (j + 1) = 0 := ite_eq_right hcj1
      omega
    · rw [ite_eq_right (fun h => hcj h.1), ite_eq_right (fun h => hcj h.1)]
      have hpj : pot c pt j = 0 := ite_eq_right hcj
      have hpj1 : pot c pt (j + 1) = 0 := by
        unfold pot
        rw [ite_eq_left hcj1]
        simp only [anchor]
        rw [ite_eq_right (fun h => hcj h.1), cl1_self]
      omega
    · rw [ite_eq_right (fun h => hcj h.1), ite_eq_right (fun h => hcj h.1)]
      have hpj : pot c pt j = 0 := ite_eq_right hcj
      have hpj1 : pot c pt (j + 1) = 0 := ite_eq_right hcj1
      omega

/-- The anchor at the end of a run is the point of its first position. -/
theorem anchor_eq {a : ℕ} (ha : a = 0 ∨ ¬ c (a - 1)) :
    ∀ b, a ≤ b → (∀ i, a ≤ i → i ≤ b → c i) → anchor c pt b = pt a := by
  intro b
  induction b with
  | zero =>
    intro hab _
    have : a = 0 := by omega
    subst this
    rfl
  | succ b ih =>
    intro hab hc
    rcases Nat.eq_or_lt_of_le hab with hab' | hab'
    · subst hab'
      simp only [anchor]
      refine ite_eq_right ?_
      rintro ⟨hb, -⟩
      rcases ha with ha | ha
      · omega
      · exact ha (by simpa using hb)
    · simp only [anchor]
      rw [ite_eq_left ⟨hc b (by omega) (by omega), hc (b + 1) (by omega) le_rfl⟩]
      exact ih (by omega) fun i hi1 hi2 => hc i hi1 (by omega)

end Runs

/-! ### The step edges of a `Γ`-chain -/

namespace S3Geom

variable {G : S3Geom}

/-- The nodes of `Γ` joined by a step that carries the edge `e`. -/
def onEdge : G.Ed → G.GNode → Prop
  | .hor x y, z => z = .inl (x.castSucc, y) ∨ z = .inl (x.succ, y)
  | .ver x y, z => z = .inl (x, y.castSucc) ∨ z = .inl (x, y.succ)
  | .bot x, z => z = .inl (x, 0) ∨ z = .inr (.inl false)
  | .top x, z => z = .inl (x, Fin.last _) ∨ z = .inr (.inl true)

end S3Geom

namespace Stage1

variable {G : S3Geom} (S : Stage1 G)

/-- A check node of `Γ`. -/
def isChk (z : G.GNode) : Prop := ∃ u, z = .inl u

/-- The check of a node (a default for the other nodes). -/
def gchk : G.GNode → G.V
  | .inl u => u
  | _ => (0, 0)

theorem onEdge_pair {e : G.Ed} {u w : G.V} (he : e.ends = {u, w}) (huw : u ≠ w) (z : G.GNode) :
    S3Geom.onEdge e z ↔ z = .inl u ∨ z = .inl w := by
  have hu : u ∈ e.ends := by rw [he]; simp
  have hw : w ∈ e.ends := by rw [he]; simp
  cases e with
  | hor x y =>
    have hA : (x.castSucc, y) ∈ ({u, w} : Finset G.V) := by rw [← he]; simp [PEdge.ends]
    have hB : (x.succ, y) ∈ ({u, w} : Finset G.V) := by rw [← he]; simp [PEdge.ends]
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hw hA hB
    simp only [S3Geom.onEdge]
    constructor
    · rintro (rfl | rfl)
      · rcases hA with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      · rcases hB with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
    · rintro (rfl | rfl)
      · rcases hu with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      · rcases hw with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
  | ver x y =>
    have hA : (x, y.castSucc) ∈ ({u, w} : Finset G.V) := by rw [← he]; simp [PEdge.ends]
    have hB : (x, y.succ) ∈ ({u, w} : Finset G.V) := by rw [← he]; simp [PEdge.ends]
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hw hA hB
    simp only [S3Geom.onEdge]
    constructor
    · rintro (rfl | rfl)
      · rcases hA with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      · rcases hB with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
    · rintro (rfl | rfl)
      · rcases hu with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      · rcases hw with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
  | bot x =>
    simp only [PEdge.ends, Finset.mem_singleton] at hu hw
    exact absurd (hu.trans hw.symm) huw
  | top x =>
    simp only [PEdge.ends, Finset.mem_singleton] at hu hw
    exact absurd (hu.trans hw.symm) huw

/-- A step determines the two nodes it joins. -/
theorem stepE_onEdge {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {x y : G.GNode} {e : G.Ed}
    (h : S.stepE a0 a1 Z E x y e) (z : G.GNode) : S3Geom.onEdge e z ↔ z = x ∨ z = y := by
  rcases x with u | b | F <;> rcases y with w | b' | F'
  · obtain ⟨he, huw, -⟩ := h
    exact onEdge_pair he huw z
  · rcases b' with _ | _
    · obtain ⟨x', rfl, rfl, -⟩ := h
      rfl
    · obtain ⟨x', rfl, rfl, -⟩ := h
      rfl
  · exact absurd h (by simp [stepE])
  · rcases b with _ | _
    · obtain ⟨x', rfl, rfl, -⟩ := h
      simp only [S3Geom.onEdge]
      exact Or.comm
    · obtain ⟨x', rfl, rfl, -⟩ := h
      simp only [S3Geom.onEdge]
      exact Or.comm
  · rcases b with _ | _ <;> rcases b' with _ | _ <;> exact absurd h (by simp [stepE])
  · rcases b with _ | _ <;> exact absurd h (by simp [stepE])
  · exact absurd h (by simp [stepE])
  · rcases b' with _ | _ <;> exact absurd h (by simp [stepE])
  · exact absurd h (by simp [stepE])

theorem getElem?_nd {l : List G.GNode} {p : ℕ} (hp : p < l.length) : l[p]? = some (nd l p) := by
  simp [nd, hp]

theorem nd_eq_iff {l : List G.GNode} (hnd : l.Nodup) {p q : ℕ} (hp : p < l.length) (hq : q < l.length) :
    nd l p = nd l q ↔ p = q := by
  constructor
  · intro h
    have hp' : l[p]? = some (nd l p) := by simp [nd, hp]
    have hq' : l[q]? = some (nd l p) := by rw [h]; simp [nd, hq]
    exact nodup_idx hnd hp' hq'
  · rintro rfl
    rfl

/-- **Distinct steps of a Nodup chain carry distinct edges.** -/
theorem stepE_inj {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {l : List G.GNode} (hnd : l.Nodup)
    {k j : ℕ} (hk : k + 1 < l.length) (hj : j + 1 < l.length) {e : G.Ed}
    (hek : S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) e) (hej : S.stepE a0 a1 Z E (nd l j) (nd l (j + 1)) e) :
    k = j := by
  have h1 := (S.stepE_onEdge hej _).1 ((S.stepE_onEdge hek _).2 (Or.inl rfl))
  have h2 := (S.stepE_onEdge hek _).1 ((S.stepE_onEdge hej _).2 (Or.inl rfl))
  rw [nd_eq_iff hnd (by omega) (by omega), nd_eq_iff hnd (by omega) (by omega)] at h1 h2
  omega

/-- The step positions of `l` (steps that carry a `C_top` edge). -/
noncomputable def stepPos (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (l : List G.GNode) : Finset ℕ :=
  (range (l.length - 1)).filter fun k => ∃ e, S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) e

/-- The edge of a step (a default edge at the other positions). -/
noncomputable def stepEdge (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (l : List G.GNode) (k : ℕ) : G.Ed :=
  if h : ∃ e, S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) e then Classical.choose h else .bot 0

theorem stepEdge_spec {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {l : List G.GNode} {k : ℕ}
    (h : ∃ e, S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) e) :
    S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) (S.stepEdge a0 a1 Z E l k) := by
  unfold stepEdge
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem Pl_eq (a0 a1 : ℕ) (Z : Solver G) (E : G.Ed → ZMod 2) (l : List G.GNode) :
    S.Pl a0 a1 Z E l = ∑ k ∈ S.stepPos a0 a1 Z E l, Pi.single (S.stepEdge a0 a1 Z E l k) 1 := by
  unfold Pl stepPos
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : ∃ e, S.stepE a0 a1 Z E (nd l k) (nd l (k + 1)) e
  · rw [ite_eq_left h]
    unfold edgeOf stepEdge
    rw [dite_eq_left h, dite_eq_left h]
  · rw [ite_eq_right h]
    unfold edgeOf
    rw [dite_eq_right h]

/-- **The `C_top` edges of a Nodup chain weigh the sum of its step edges.** -/
theorem wsum_Pl {a0 a1 : ℕ} (Z : Solver G) {E : G.Ed → ZMod 2} {l : List G.GNode} (hnd : l.Nodup)
    (wt : G.Ed → ℝ) :
    S3Geom.wsum wt (S.Pl a0 a1 Z E l) = ∑ k ∈ S.stepPos a0 a1 Z E l, wt (S.stepEdge a0 a1 Z E l k) := by
  rw [S.Pl_eq]
  refine S3Geom.wsum_sum_single wt _ _ fun i hi j hj hij => ?_
  simp only [stepPos, Finset.mem_filter, Finset.mem_range] at hi hj
  have hei := S.stepEdge_spec hi.2
  have hej := S.stepEdge_spec hj.2
  rw [hij] at hei
  exact S.stepE_inj hnd (by omega) (by omega) hei hej

/-! ### The metric constraint -/

/-- A check-check step of a `Γ`-chain carries a bulk edge between checks at `ℓ1` distance `1`. -/
theorem cc_step {a0 a1 : ℕ} {Z : Solver G} {E : G.Ed → ZMod 2} {u w : G.V}
    (h : S.gadj a0 a1 Z E (.inl u) (.inl w)) :
    ∃ e, S.stepE a0 a1 Z E (.inl u) (.inl w) e ∧ cl1 u w = 1 ∧ S3Geom.isBulk e := by
  rcases h with ⟨e, he, huw, hc⟩ | ⟨e, he, huw, hc⟩
  · exact ⟨e, ⟨he, huw, hc⟩, cl1_of_ends he huw⟩
  · have he' : e.ends = {u, w} := by rw [he, Finset.pair_comm]
    exact ⟨e, ⟨he', fun h => huw h.symm, hc⟩, cl1_of_ends he' fun h => huw h.symm⟩

theorem nd_isChk {l : List G.GNode} {i : ℕ} (h : isChk (nd l i)) : nd l i = .inl (gchk (nd l i)) := by
  obtain ⟨u, hu⟩ := h
  rw [hu]
  rfl

/-- **Metric constraint (position form)**: along a Nodup `Γ`-chain `l` whose end nodes are not checks,
`wmin` times the total displacement of the runs of checks that end before a non-check node is at most the sum, over
the family nodes of `l`, of the pair cost of their neighbouring checks. -/
theorem metric_pos {a0 a1 : ℕ} (Z : Solver G) (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin : ℝ} (hmin0 : 0 ≤ wmin)
    (hmin : ∀ e, S3Geom.isBulk e → wmin ≤ Z.wt e) {E : G.Ed → ZMod 2} {l : List G.GNode} (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj a0 a1 Z E) l) (hl : l ≠ []) (h0 : ∀ u, nd l 0 ≠ .inl u)
    (hlast : ∀ u, nd l (l.length - 1) ≠ .inl u) :
    wmin * ((∑ i ∈ (range (l.length - 1)).filter (fun i => isChk (nd l i) ∧ ¬ isChk (nd l (i + 1))),
        pot (fun i => isChk (nd l i)) (fun i => gchk (nd l i)) i : ℕ) : ℝ) ≤
      ∑ k ∈ range l.length, if isFam (nd l k) then S3Geom.pairCost Z.wt (stT l k) else 0 := by
  set c : ℕ → Prop := fun i => isChk (nd l i) with hc
  set pt : ℕ → G.V := fun i => gchk (nd l i) with hpt
  have hlen : 1 ≤ l.length := List.length_pos_of_ne_nil hl
  -- check-check steps
  have hcc : ∀ i, i + 1 < l.length → c i → c (i + 1) →
      ∃ e, S.stepE a0 a1 Z E (nd l i) (nd l (i + 1)) e ∧ cl1 (pt i) (pt (i + 1)) = 1 ∧ S3Geom.isBulk e := by
    intro i hi hci hci1
    have hg : S.gadj a0 a1 Z E (nd l i) (nd l (i + 1)) :=
      chain_step hch (getElem?_nd (by omega)) (getElem?_nd hi)
    rw [nd_isChk hci, nd_isChk hci1] at hg ⊢
    exact S.cc_step hg
  -- runs
  have hruns := runs_le c pt (l.length - 1) (fun i hi hci hci1 => by
      obtain ⟨e, -, h1, -⟩ := hcc i (by omega) hci hci1
      exact h1.le)
    (l.length - 1) le_rfl
  set ccPos := (range (l.length - 1)).filter (fun i => c i ∧ c (i + 1)) with hccPos
  have hsum_le : ((∑ i ∈ (range (l.length - 1)).filter (fun i => c i ∧ ¬ c (i + 1)), pot c pt i : ℕ) : ℝ) ≤
      (ccPos.card : ℝ) := by
    exact_mod_cast (Nat.le_add_right _ _).trans hruns
  -- the step edges of ccPos are bulk
  have hsub : ccPos ⊆ S.stepPos a0 a1 Z E l := by
    intro i hi
    simp only [hccPos, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨e, he, -⟩ := hcc i (by omega) hi.2.1 hi.2.2
    simp only [stepPos, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi.1, e, he⟩
  have hbulk : ∀ i ∈ ccPos, wmin ≤ Z.wt (S.stepEdge a0 a1 Z E l i) := by
    intro i hi
    simp only [hccPos, Finset.mem_filter, Finset.mem_range] at hi
    have hci := hi.2.1
    have hci1 := hi.2.2
    obtain ⟨e, he, -⟩ := hcc i (by omega) hci hci1
    have hs := S.stepEdge_spec ⟨e, he⟩
    rw [nd_isChk hci, nd_isChk hci1] at hs
    obtain ⟨hends, hne, -⟩ := hs
    exact hmin _ (cl1_of_ends hends hne).2
  have hlow : wmin * (ccPos.card : ℝ) ≤ S3Geom.wsum Z.wt (S.Pl a0 a1 Z E l) := by
    rw [S.wsum_Pl Z hnd]
    calc wmin * (ccPos.card : ℝ) = ∑ _i ∈ ccPos, wmin := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ ccPos, Z.wt (S.stepEdge a0 a1 Z E l i) := Finset.sum_le_sum hbulk
      _ ≤ ∑ i ∈ S.stepPos a0 a1 Z E l, Z.wt (S.stepEdge a0 a1 Z E l i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hwt0 _
  have hup := S.path_X_pairs Z hwt0 hch hl h0 hlast
  calc _ ≤ wmin * (ccPos.card : ℝ) := mul_le_mul_of_nonneg_left hsum_le hmin0
    _ ≤ _ := hlow
    _ ≤ _ := hup

/-- **A jump of a T2 path**: if positions `k'` and `k` are non-check nodes with only checks strictly between them
(and at least one), the run ending at `k - 1` is anchored at `k' + 1`. -/
theorem pot_jump {l : List G.GNode} {k' k : ℕ} (hk : k' + 1 < k) (hk' : ¬ isChk (nd l k'))
    (hmid : ∀ i, k' < i → i < k → isChk (nd l i)) :
    pot (fun i => isChk (nd l i)) (fun i => gchk (nd l i)) (k - 1) = cl1 (gchk (nd l (k' + 1))) (gchk (nd l (k - 1))) := by
  unfold pot
  rw [ite_eq_left (hmid (k - 1) (by omega) (by omega))]
  rw [anchor_eq (fun i => isChk (nd l i)) (fun i => gchk (nd l i)) (a := k' + 1) (Or.inr (by simpa using hk'))
    (k - 1) (by omega) fun i hi1 hi2 => hmid i (by omega) (by omega)]

/-! ### The constraint at the stations of a T2 path -/

/-- **Metric constraint at the stations of a T2 path** (check level). Stations: positions
`p 0 = 0 < p 1 < … < p (m+1) = |l| - 1` of `l`, with family nodes at `p 1, …, p m` and at no other inner position;
`u i` is the entry check of station `i` (the node before `p i`, `1 ≤ i ≤ m+1`) and `v i` its exit check (the node
after `p i`, `0 ≤ i ≤ m`). Jump `i` runs from `v i` to `u (i+1)`. Then `wmin` times the total `ℓ1` length of the
jumps is at most `wmax` times the total `ℓ1` span of the intermediate families plus the two boundary legs (the legs
are kept in every variant; they are needed only when the ends are families). -/
theorem metric_stations {a0 a1 : ℕ} (Z : Solver G) (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin wmax wh : ℝ}
    (hmin0 : 0 ≤ wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hmin : ∀ e, S3Geom.isBulk e → wmin ≤ Z.wt e) (hmax : ∀ e, S3Geom.isBulk e → Z.wt e ≤ wmax)
    (hbot : ∀ x, Z.wt (.bot x) ≤ wh) (htop : ∀ x, Z.wt (.top x) ≤ wh)
    {E : G.Ed → ZMod 2} {l : List G.GNode} {x y : G.GNode}
    (hhd : l.head? = some x) (hlst : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj a0 a1 Z E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x) (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → G.V)
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hp0 : p 0 = 0) (hpl : p (m + 1) = l.length - 1)
    (hfam : ∀ i, 1 ≤ i → i ≤ m → isFam (nd l (p i)))
    (hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam (nd l k))
    (hu : ∀ i, 1 ≤ i → i ≤ m + 1 → nd l (p i - 1) = .inl (u i))
    (hv : ∀ i ≤ m, nd l (p i + 1) = .inl (v i)) :
    wmin * ∑ i ∈ range (m + 1), (cl1 (v i) (u (i + 1)) : ℝ) ≤
      wmax * ∑ i ∈ range m, (cl1 (u (i + 1)) (v (i + 1)) : ℝ) + wmax * ((v 0).2.val : ℝ) +
        wmax * ((G.h - (u (m + 1)).2.val : ℕ) : ℝ) + 2 * wh := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hnd0 : nd l 0 = x := nd_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hndl : nd l (l.length - 1) = y := nd_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have h0 : ∀ u, nd l 0 ≠ .inl u := by
    intro u hu
    rw [hnd0] at hu
    subst hu
    rcases hx with h | h
    · cases h
    · exact h
  have hlast : ∀ u, nd l (l.length - 1) ≠ .inl u := by
    intro u hu
    rw [hndl] at hu
    subst hu
    rcases hy with h | h
    · cases h
    · exact h
  -- the stations
  have hmono : ∀ i j, i ≤ j → j ≤ m + 1 → p i ≤ p j := by
    intro i j hij hj
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact le_rfl
    · exact (hp i j h hj).le
  have hpl' : ∀ i ≤ m + 1, p i ≤ l.length - 1 := fun i hi => hpl ▸ hmono i (m + 1) hi le_rfl
  have hlen2 : 2 ≤ l.length := by
    have := hp 0 (m + 1) (by omega) le_rfl
    omega
  have hother : ∀ k, k < l.length → (∀ i ≤ m + 1, k ≠ p i) → isChk (nd l k) := by
    intro k hk hne
    have hk0 : 0 < k := by
      have := hne 0 (by omega)
      rw [hp0] at this
      omega
    have hk1 : k + 1 < l.length := by
      have := hne (m + 1) le_rfl
      rw [hpl] at this
      omega
    obtain ⟨w, hw⟩ := inner_check hhd hlst hnd hbd hk0 hk1 (getElem?_nd hk)
      (fun F hF => hnofam k hne ⟨F, hF⟩)
    exact ⟨w, hw⟩
  have hnc : ∀ i ≤ m + 1, ¬ isChk (nd l (p i)) := by
    rintro i hi ⟨w, hw⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hp0] at hw
      exact h0 w hw
    · rcases Nat.lt_or_ge i (m + 1) with hi1 | hi1
      · obtain ⟨F, hF⟩ := hfam i hi0 (by omega)
        rw [hF] at hw
        cases hw
      · have : i = m + 1 := by omega
        subst this
        rw [hpl] at hw
        exact hlast w hw
  have hbetween : ∀ i ≤ m, ∀ k, p i < k → k < p (i + 1) → isChk (nd l k) := by
    intro i hi k hk1 hk2
    refine hother k (by have := hpl' (i + 1) (by omega); omega) fun j hj hkj => ?_
    subst hkj
    rcases Nat.lt_or_ge i j with h | h
    · have := hmono (i + 1) j (by omega) hj
      omega
    · have := hmono j i h (by omega)
      omega
  have hgap : ∀ i ≤ m, p i + 1 < p (i + 1) := by
    intro i hi
    have h1 := hp i (i + 1) (by omega) (by omega)
    by_contra hcon
    have heq : p i + 1 = p (i + 1) := by omega
    have := hv i hi
    rw [heq] at this
    exact hnc (i + 1) (by omega) ⟨v i, this⟩
  -- the jumps
  have hpot : ∀ i ≤ m, pot (fun k => isChk (nd l k)) (fun k => gchk (nd l k)) (p (i + 1) - 1) =
      cl1 (v i) (u (i + 1)) := by
    intro i hi
    rw [pot_jump (hgap i hi) (hnc i (by omega)) (hbetween i hi), hv i hi, hu (i + 1) (by omega) (by omega)]
    rfl
  have hF : (range (l.length - 1)).filter (fun j => isChk (nd l j) ∧ ¬ isChk (nd l (j + 1))) =
      (range (m + 1)).image (fun i => p (i + 1) - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, -, hncj⟩
      by_contra hno
      push Not at hno
      apply hncj
      refine hother (j + 1) (by omega) fun i hi hji => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hp0] at hji
        omega
      · exact hno (i - 1) (by omega) (by rw [Nat.sub_add_cancel hi0]; omega)
    · rintro ⟨i, hi, rfl⟩
      have h1 := hgap i (by omega)
      have h2 := hpl' (i + 1) (by omega)
      refine ⟨by omega, ⟨u (i + 1), hu (i + 1) (by omega) (by omega)⟩, ?_⟩
      rw [Nat.sub_add_cancel (by omega)]
      exact hnc (i + 1) (by omega)
  have hinj : ∀ i ∈ range (m + 1), ∀ j ∈ range (m + 1), p (i + 1) - 1 = p (j + 1) - 1 → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    have hi1 := hgap i (by omega)
    have hj1 := hgap j (by omega)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hp (i + 1) (j + 1) (by omega) (by omega)
      omega
    · have := hp (j + 1) (i + 1) (by omega) (by omega)
      omega
  have hLHS : (∑ j ∈ (range (l.length - 1)).filter (fun j => isChk (nd l j) ∧ ¬ isChk (nd l (j + 1))),
      pot (fun k => isChk (nd l k)) (fun k => gchk (nd l k)) j) = ∑ i ∈ range (m + 1), cl1 (v i) (u (i + 1)) := by
    rw [hF, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun i hi => hpot i (by simp only [Finset.mem_range] at hi; omega)
  -- the families
  have hpinj : ∀ i ∈ range (m + 2), ∀ j ∈ range (m + 2), p i = p j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hp i j h (by omega)
      omega
    · have := hp j i h (by omega)
      omega
  have hRHS : (∑ k ∈ range l.length, if isFam (nd l k) then S3Geom.pairCost Z.wt (stT l k) else 0) =
      ∑ i ∈ range (m + 2), if isFam (nd l (p i)) then S3Geom.pairCost Z.wt (stT l (p i)) else 0 := by
    have hsub : (range (m + 2)).image p ⊆ range l.length := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
      obtain ⟨i, hi, rfl⟩ := hk
      have := hpl' i (by omega)
      omega
    rw [← Finset.sum_subset hsub, Finset.sum_image hpinj]
    intro k _ hknot
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hknot
    exact ite_eq_right (hnofam k fun i hi hki => hknot i (by omega) hki.symm)
  have hb0 : (if isFam (nd l (p 0)) then S3Geom.pairCost Z.wt (stT l (p 0)) else 0) ≤
      wmax * ((v 0).2.val : ℝ) + wh := by
    by_cases hfx : isFam (nd l (p 0))
    · rw [ite_eq_left hfx]
      have hst : stT l (p 0) = Pi.single (v 0) 1 := by
        unfold stT
        rw [hp0, ite_eq_right (lt_irrefl 0), ite_eq_left (by omega : 0 + 1 < l.length), zero_add]
        have := hv 0 (by omega)
        rw [hp0] at this
        rw [this]
        rfl
      rw [hst]
      have := S3Geom.pairCost_le_bot hwt0 hmax0 hmax hbot (v 0)
      linarith [mul_comm ((v 0).2.val : ℝ) wmax]
    · rw [ite_eq_right hfx]
      positivity
  have hbl : (if isFam (nd l (p (m + 1))) then S3Geom.pairCost Z.wt (stT l (p (m + 1))) else 0) ≤
      wmax * ((G.h - (u (m + 1)).2.val : ℕ) : ℝ) + wh := by
    by_cases hfy : isFam (nd l (p (m + 1)))
    · rw [ite_eq_left hfy]
      have hst : stT l (p (m + 1)) = Pi.single (u (m + 1)) 1 := by
        unfold stT
        rw [hpl, ite_eq_left (by omega : 0 < l.length - 1), ite_eq_right (by omega : ¬ (l.length - 1 + 1 < l.length)),
          add_zero]
        have := hu (m + 1) (by omega) le_rfl
        rw [hpl] at this
        rw [this]
        rfl
      rw [hst]
      have := S3Geom.pairCost_le_top hwt0 hmax0 hmax htop (u (m + 1))
      linarith [mul_comm ((G.h - (u (m + 1)).2.val : ℕ) : ℝ) wmax]
    · rw [ite_eq_right hfy]
      positivity
  have hbi : ∀ i ∈ range m, (if isFam (nd l (p (i + 1))) then S3Geom.pairCost Z.wt (stT l (p (i + 1))) else 0) ≤
      wmax * (cl1 (u (i + 1)) (v (i + 1)) : ℝ) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_left (hfam (i + 1) (by omega) (by omega))]
    have hpos : 0 < p (i + 1) := by
      have := hp 0 (i + 1) (by omega) (by omega)
      omega
    have hlt : p (i + 1) + 1 < l.length := by
      have := hp (i + 1) (m + 1) (by omega) le_rfl
      omega
    have hst : stT l (p (i + 1)) = Pi.single (u (i + 1)) 1 + Pi.single (v (i + 1)) 1 := by
      unfold stT
      rw [ite_eq_left hpos, ite_eq_left hlt, hu (i + 1) (by omega) (by omega), hv (i + 1) (by omega)]
      rfl
    rw [hst]
    have := S3Geom.pairCost_le_l1 hwt0 hmax0 hmax (u (i + 1)) (v (i + 1))
    rw [mul_comm]
    exact this
  -- assemble
  have hsplit : (∑ i ∈ range (m + 2), if isFam (nd l (p i)) then S3Geom.pairCost Z.wt (stT l (p i)) else 0) =
      (if isFam (nd l (p 0)) then S3Geom.pairCost Z.wt (stT l (p 0)) else 0) +
      (∑ i ∈ range m, if isFam (nd l (p (i + 1))) then S3Geom.pairCost Z.wt (stT l (p (i + 1))) else 0) +
      (if isFam (nd l (p (m + 1))) then S3Geom.pairCost Z.wt (stT l (p (m + 1))) else 0) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  have hmain := S.metric_pos Z hwt0 hmin0 hmin hnd hch hl h0 hlast
  rw [hLHS, hRHS, hsplit] at hmain
  have hsum := Finset.sum_le_sum hbi
  rw [← Finset.mul_sum] at hsum
  push_cast at hmain
  linarith

/-- **Metric constraint in block units**: `metric_stations` with each check-level `ℓ1` distance replaced by
`L` times the block `ℓ1` displacement (`l1_ge_block`, `l1_le_block`; each costs `2 (L - 1)`). -/
theorem metric_stations_block {a0 a1 : ℕ} (Z : Solver G) (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin wmax wh : ℝ}
    (hmin0 : 0 ≤ wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hmin : ∀ e, S3Geom.isBulk e → wmin ≤ Z.wt e) (hmax : ∀ e, S3Geom.isBulk e → Z.wt e ≤ wmax)
    (hbot : ∀ x, Z.wt (.bot x) ≤ wh) (htop : ∀ x, Z.wt (.top x) ≤ wh)
    {E : G.Ed → ZMod 2} {l : List G.GNode} {x y : G.GNode}
    (hhd : l.head? = some x) (hlst : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj a0 a1 Z E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam a0 a1 E x) (hy : y = .inr (.inl true) ∨ S.topFam a0 a1 E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : G.GNode) ∈ l → (.inr (.inl b) : G.GNode) = x ∨ (.inr (.inl b) : G.GNode) = y)
    (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → G.V)
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hp0 : p 0 = 0) (hpl : p (m + 1) = l.length - 1)
    (hfam : ∀ i, 1 ≤ i → i ≤ m → isFam (nd l (p i)))
    (hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam (nd l k))
    (hu : ∀ i, 1 ≤ i → i ≤ m + 1 → nd l (p i - 1) = .inl (u i))
    (hv : ∀ i ≤ m, nd l (p i + 1) = .inl (v i)) :
    wmin * ((G.L : ℝ) * ∑ i ∈ range (m + 1), (S3Geom.blockL1 (v i) (u (i + 1)) : ℝ)) ≤
      wmax * ((G.L : ℝ) * ∑ i ∈ range m, (S3Geom.blockL1 (u (i + 1)) (v (i + 1)) : ℝ)) +
        (wmin * (m + 1) + wmax * m) * ((2 * (G.L - 1) : ℕ) : ℝ) + wmax * ((v 0).2.val : ℝ) +
        wmax * ((G.h - (u (m + 1)).2.val : ℕ) : ℝ) + 2 * wh := by
  have hc := S.metric_stations Z hwt0 hmin0 hmax0 hwh0 hmin hmax hbot htop hhd hlst hnd hch hx hy hbd m p u v hp hp0
    hpl hfam hnofam hu hv
  set c : ℝ := ((2 * (G.L - 1) : ℕ) : ℝ) with hcdef
  have hjump : ∀ i ∈ range (m + 1), (G.L : ℝ) * (S3Geom.blockL1 (v i) (u (i + 1)) : ℝ) ≤
      (cl1 (v i) (u (i + 1)) : ℝ) + c := by
    intro i _
    have := S3Geom.l1_ge_block (v i) (u (i + 1))
    rw [hcdef]
    exact_mod_cast this
  have hfamb : ∀ i ∈ range m, (cl1 (u (i + 1)) (v (i + 1)) : ℝ) ≤
      (G.L : ℝ) * (S3Geom.blockL1 (u (i + 1)) (v (i + 1)) : ℝ) + c := by
    intro i _
    have := S3Geom.l1_le_block (u (i + 1)) (v (i + 1))
    rw [hcdef]
    exact_mod_cast this
  have h1 := Finset.sum_le_sum hjump
  have h2 := Finset.sum_le_sum hfamb
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at h1 h2
  have hc0 : 0 ≤ c := by positivity
  have e1 := mul_le_mul_of_nonneg_left h1 hmin0
  have e2 := mul_le_mul_of_nonneg_left h2 hmax0
  push_cast at e1 e2 hc ⊢
  nlinarith

end Stage1

end QECML
