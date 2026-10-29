import QECD1.T2MetricB3

/-!
# The metric constraint of a T2 path (3D): the deterministic part of the λ-trick

The 3D analogue of the 2D `TwoD/T2Lam`. Along a Nodup `Γ`-chain `l`, distinct steps carry distinct `C_top` edges
(`stepE3_inj`), so the `C_top` paths of `l` weigh exactly the sum of their step edges (`wsum3_Pl3`). A check-check
step is a bulk edge between checks at `ℓ1` distance `1` (`cc_step3`). Cut `l` into runs of consecutive check nodes;
the `ℓ1` displacement of a run, from its first check (its anchor) to its last check, is at most its number of steps
(`runs_le3`). With (X) (`path_X_pairs3`) this gives (`metric_pos3`):

  `wmin · Σ_{runs ending before a non-check node} |anchor - last check|_1 ≤ wsum(C_top paths of l)`
  `                                                ≤ Σ_{family nodes k of l} pairCost(neighbouring checks of k)`.

On a T2 path the runs that end before a non-check node are its jumps (`pot_jump3`). `metric_stations3` states the
constraint at the stations of a T2 path, `metric_stations_block3` in block units.
-/

open Finset Classical

namespace QECD1

variable {T w h : ℕ}

theorem cl1_3_self (u : PVert3 T w h) : cl1_3 u u = 0 := by
  simp [cl1_3]

theorem cl1_3_comm (u v : PVert3 T w h) : cl1_3 u v = cl1_3 v u := by
  unfold cl1_3
  omega

theorem cl1_3_triangle (u v z : PVert3 T w h) : cl1_3 u z ≤ cl1_3 u v + cl1_3 v z := by
  unfold cl1_3
  omega

/-- An edge with two distinct end checks is a bulk edge, and its end checks are at `ℓ1` distance `1`. -/
theorem cl1_3_of_ends {e : PEdge3 T w h} {u v : PVert3 T w h} (he : e.ends = {u, v}) (huv : u ≠ v) :
    cl1_3 u v = 1 ∧ ¬ e.isHalf := by
  have hu : u ∈ e.ends := by rw [he]; simp
  have hv : v ∈ e.ends := by rw [he]; simp
  cases e with
  | hor t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, fun hh => hh⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · exact absurd rfl huv
  | ver t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, fun hh => hh⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · exact absurd rfl huv
  | time t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, fun hh => hh⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [cl1_3, Fin.val_castSucc, Fin.val_succ]
      omega
    · exact absurd rfl huv
  | bot t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv
  | top t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv

/-! ### Weights of sums of distinct edges -/

theorem wsum3_single_add (wt : PEdge3 T w h → ℝ) (e : PEdge3 T w h) (X : PEdge3 T w h → ZMod 2) (hX : X e = 0) :
    wsum3 wt ((Pi.single e 1 : PEdge3 T w h → ZMod 2) + X) = wt e + wsum3 wt X := by
  unfold wsum3
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  have h1 : ∀ e' ∈ Finset.univ.erase e,
      (if ((Pi.single e (1 : ZMod 2) : PEdge3 T w h → ZMod 2) + X) e' ≠ 0 then wt e' else 0) =
      (if X e' ≠ 0 then wt e' else 0) := by
    intro e' he'
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase he'), zero_add]
  rw [Finset.sum_congr rfl h1]
  simp [hX]

/-- The weight of a sum of pairwise distinct single edges is the sum of their weights. -/
theorem wsum3_sum_single (wt : PEdge3 T w h → ℝ) (A : Finset ℕ) (f : ℕ → PEdge3 T w h)
    (hf : ∀ i ∈ A, ∀ j ∈ A, f i = f j → i = j) :
    wsum3 wt (∑ i ∈ A, (Pi.single (f i) (1 : ZMod 2) : PEdge3 T w h → ZMod 2)) = ∑ i ∈ A, wt (f i) := by
  induction A using Finset.induction_on with
  | empty => simp [wsum3]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hX : (∑ i ∈ A, (Pi.single (f i) (1 : ZMod 2) : PEdge3 T w h → ZMod 2)) (f a) = 0 := by
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i hi => Pi.single_eq_of_ne (fun hfe => ?_) _
      have := hf a (Finset.mem_insert_self a A) i (Finset.mem_insert_of_mem hi) hfe
      exact ha (this ▸ hi)
    rw [wsum3_single_add wt _ _ hX,
      ih fun i hi j hj => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)]

/-! ### Runs -/

section Runs

variable (c : ℕ → Prop) (pt : ℕ → PVert3 T w h)

/-- The anchor of position `i`: the point of the first position of the run of consecutive `c`-positions through
`i`. -/
noncomputable def anchor3 : ℕ → PVert3 T w h
  | 0 => pt 0
  | i + 1 => if c i ∧ c (i + 1) then anchor3 i else pt (i + 1)

/-- The `ℓ1` displacement of position `i` from its anchor (zero off `c`). -/
noncomputable def pot3 (i : ℕ) : ℕ := if c i then cl1_3 (anchor3 c pt i) (pt i) else 0

/-- **Runs**: if consecutive `c`-positions have points at `ℓ1` distance at most `1`, the displacements of the runs
that end before position `j` (plus the displacement at `j`) are at most the number of `c`-`c` steps before `j`. -/
theorem runs_le3 (N : ℕ) (hstep : ∀ i < N, c i → c (i + 1) → cl1_3 (pt i) (pt (i + 1)) ≤ 1) :
    ∀ j ≤ N, (∑ i ∈ (range j).filter (fun i => c i ∧ ¬ c (i + 1)), pot3 c pt i) + pot3 c pt j ≤
      ((range j).filter (fun i => c i ∧ c (i + 1))).card := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [pot3, anchor3, cl1_3_self]
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hnot1 : j ∉ (range j).filter (fun i => c i ∧ ¬ c (i + 1)) := by simp
    have hnot2 : j ∉ (range j).filter (fun i => c i ∧ c (i + 1)) := by simp
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hcj : c j <;> by_cases hcj1 : c (j + 1)
    · rw [ite_eq_right (fun h1 => h1.2 hcj1), ite_eq_left ⟨hcj, hcj1⟩, Finset.card_insert_of_notMem hnot2]
      have hpj : pot3 c pt j = cl1_3 (anchor3 c pt j) (pt j) := ite_eq_left hcj
      have hpj1 : pot3 c pt (j + 1) = cl1_3 (anchor3 c pt j) (pt (j + 1)) := by
        unfold pot3
        rw [ite_eq_left hcj1]
        simp only [anchor3]
        rw [ite_eq_left ⟨hcj, hcj1⟩]
      have h1 := cl1_3_triangle (anchor3 c pt j) (pt j) (pt (j + 1))
      have h2 := hstep j (by omega) hcj hcj1
      omega
    · rw [ite_eq_left ⟨hcj, hcj1⟩, ite_eq_right (fun h1 => hcj1 h1.2), Finset.sum_insert hnot1]
      have hpj1 : pot3 c pt (j + 1) = 0 := ite_eq_right hcj1
      omega
    · rw [ite_eq_right (fun h1 => hcj h1.1), ite_eq_right (fun h1 => hcj h1.1)]
      have hpj : pot3 c pt j = 0 := ite_eq_right hcj
      have hpj1 : pot3 c pt (j + 1) = 0 := by
        unfold pot3
        rw [ite_eq_left hcj1]
        simp only [anchor3]
        rw [ite_eq_right (fun h1 => hcj h1.1), cl1_3_self]
      omega
    · rw [ite_eq_right (fun h1 => hcj h1.1), ite_eq_right (fun h1 => hcj h1.1)]
      have hpj : pot3 c pt j = 0 := ite_eq_right hcj
      have hpj1 : pot3 c pt (j + 1) = 0 := ite_eq_right hcj1
      omega

/-- The anchor at the end of a run is the point of its first position. -/
theorem anchor3_eq {a : ℕ} (ha : a = 0 ∨ ¬ c (a - 1)) :
    ∀ b, a ≤ b → (∀ i, a ≤ i → i ≤ b → c i) → anchor3 c pt b = pt a := by
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
      simp only [anchor3]
      refine ite_eq_right ?_
      rintro ⟨hb, -⟩
      rcases ha with ha | ha
      · omega
      · exact ha (by simpa using hb)
    · simp only [anchor3]
      rw [ite_eq_left ⟨hc b (by omega) (by omega), hc (b + 1) (by omega) le_rfl⟩]
      exact ih (by omega) fun i hi1 hi2 => hc i hi1 (by omega)

end Runs

/-! ### The step edges of a `Γ`-chain -/

/-- The nodes of `Γ` joined by a step that carries the edge `e`. -/
def onEdge3 : PEdge3 T w h → GNode3 T w h → Prop
  | .hor t x y, z => z = .inl (t, x.castSucc, y) ∨ z = .inl (t, x.succ, y)
  | .ver t x y, z => z = .inl (t, x, y.castSucc) ∨ z = .inl (t, x, y.succ)
  | .time t x y, z => z = .inl (t.castSucc, x, y) ∨ z = .inl (t.succ, x, y)
  | .bot t x, z => z = .inl (t, x, 0) ∨ z = .inr (.inl false)
  | .top t x, z => z = .inl (t, x, Fin.last h) ∨ z = .inr (.inl true)

/-- A check node of `Γ`. -/
def isChk3 (z : GNode3 T w h) : Prop := ∃ u, z = .inl u

/-- The check of a node (a default for the other nodes). -/
def gchk3 : GNode3 T w h → PVert3 T w h
  | .inl u => u
  | _ => (0, 0, 0)

theorem onEdge3_pair {e : PEdge3 T w h} {u v : PVert3 T w h} (he : e.ends = {u, v}) (huv : u ≠ v)
    (z : GNode3 T w h) : onEdge3 e z ↔ z = .inl u ∨ z = .inl v := by
  have hu : u ∈ e.ends := by rw [he]; simp
  have hv : v ∈ e.ends := by rw [he]; simp
  cases e with
  | hor t x y =>
    have hA : (t, x.castSucc, y) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    have hB : (t, x.succ, y) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv hA hB
    simp only [onEdge3]
    constructor
    · rintro (rfl | rfl)
      · rcases hA with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hB with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
    · rintro (rfl | rfl)
      · rcases hu with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hv with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
  | ver t x y =>
    have hA : (t, x, y.castSucc) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    have hB : (t, x, y.succ) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv hA hB
    simp only [onEdge3]
    constructor
    · rintro (rfl | rfl)
      · rcases hA with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hB with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
    · rintro (rfl | rfl)
      · rcases hu with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hv with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
  | time t x y =>
    have hA : (t.castSucc, x, y) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    have hB : (t.succ, x, y) ∈ ({u, v} : Finset (PVert3 T w h)) := by rw [← he]; simp [PEdge3.ends]
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hv hA hB
    simp only [onEdge3]
    constructor
    · rintro (rfl | rfl)
      · rcases hA with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hB with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
    · rintro (rfl | rfl)
      · rcases hu with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
      · rcases hv with h1 | h1
        · exact Or.inl (by rw [h1])
        · exact Or.inr (by rw [h1])
  | bot t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv
  | top t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv

theorem getElem?_nd3 {l : List (GNode3 T w h)} {p : ℕ} (hp : p < l.length) : l[p]? = some (nd3 l p) := by
  simp [nd3, hp]

theorem nd3_eq_iff {l : List (GNode3 T w h)} (hnd : l.Nodup) {p q : ℕ} (hp : p < l.length) (hq : q < l.length) :
    nd3 l p = nd3 l q ↔ p = q := by
  constructor
  · intro hpq
    have hp' : l[p]? = some (nd3 l p) := by simp [nd3, hp]
    have hq' : l[q]? = some (nd3 l p) := by rw [hpq]; simp [nd3, hq]
    exact nodup_idx hnd hp' hq'
  · rintro rfl
    rfl

theorem nd3_isChk {l : List (GNode3 T w h)} {i : ℕ} (hi : isChk3 (nd3 l i)) : nd3 l i = .inl (gchk3 (nd3 l i)) := by
  obtain ⟨u, hu⟩ := hi
  rw [hu]
  rfl

namespace Stage13

variable (S : Stage13 T w h) (Z : Solver3 T w h)

/-- A step determines the two nodes it joins. -/
theorem stepE3_onEdge {E : PEdge3 T w h → ZMod 2} {x y : GNode3 T w h} {e : PEdge3 T w h}
    (hs : S.stepE3 Z E x y e) (z : GNode3 T w h) : onEdge3 e z ↔ z = x ∨ z = y := by
  rcases x with u | (_ | _) | F <;> rcases y with v | (_ | _) | F' <;> simp only [stepE3] at hs
  · exact onEdge3_pair hs.1 hs.2.1 z
  · obtain ⟨t', x', rfl, rfl, -⟩ := hs
    rfl
  · obtain ⟨t', x', rfl, rfl, -⟩ := hs
    rfl
  · obtain ⟨t', x', rfl, rfl, -⟩ := hs
    simp only [onEdge3]
    exact Or.comm
  · obtain ⟨t', x', rfl, rfl, -⟩ := hs
    simp only [onEdge3]
    exact Or.comm

/-- **Distinct steps of a Nodup chain carry distinct edges.** -/
theorem stepE3_inj {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} (hnd : l.Nodup)
    {k j : ℕ} (hk : k + 1 < l.length) (hj : j + 1 < l.length) {e : PEdge3 T w h}
    (hek : S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) e) (hej : S.stepE3 Z E (nd3 l j) (nd3 l (j + 1)) e) :
    k = j := by
  have h1 := (S.stepE3_onEdge Z hej _).1 ((S.stepE3_onEdge Z hek _).2 (Or.inl rfl))
  have h2 := (S.stepE3_onEdge Z hek _).1 ((S.stepE3_onEdge Z hej _).2 (Or.inl rfl))
  rw [nd3_eq_iff hnd (by omega) (by omega), nd3_eq_iff hnd (by omega) (by omega)] at h1 h2
  omega

/-- The step positions of `l` (steps that carry a `C_top` edge). -/
noncomputable def stepPos3 (E : PEdge3 T w h → ZMod 2) (l : List (GNode3 T w h)) : Finset ℕ :=
  (range (l.length - 1)).filter fun k => ∃ e, S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) e

/-- The edge of a step (a default edge at the other positions). -/
noncomputable def stepEdge3 (E : PEdge3 T w h → ZMod 2) (l : List (GNode3 T w h)) (k : ℕ) : PEdge3 T w h :=
  if hk : ∃ e, S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) e then Classical.choose hk else .bot 0 0

theorem stepEdge3_spec {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} {k : ℕ}
    (hk : ∃ e, S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) e) :
    S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) (S.stepEdge3 Z E l k) := by
  unfold stepEdge3
  rw [dite_eq_left hk]
  exact Classical.choose_spec hk

theorem Pl3_eq (E : PEdge3 T w h → ZMod 2) (l : List (GNode3 T w h)) :
    S.Pl3 Z E l = ∑ k ∈ S.stepPos3 Z E l, Pi.single (S.stepEdge3 Z E l k) 1 := by
  unfold Pl3 stepPos3
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ∃ e, S.stepE3 Z E (nd3 l k) (nd3 l (k + 1)) e
  · rw [ite_eq_left hk]
    unfold edgeOf3 stepEdge3
    rw [dite_eq_left hk, dite_eq_left hk]
  · rw [ite_eq_right hk]
    unfold edgeOf3
    rw [dite_eq_right hk]

/-- **The `C_top` paths of a Nodup chain weigh the sum of its step edges.** -/
theorem wsum3_Pl3 {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} (hnd : l.Nodup) (wt : PEdge3 T w h → ℝ) :
    wsum3 wt (S.Pl3 Z E l) = ∑ k ∈ S.stepPos3 Z E l, wt (S.stepEdge3 Z E l k) := by
  rw [S.Pl3_eq Z]
  refine wsum3_sum_single wt _ _ fun i hi j hj hij => ?_
  simp only [stepPos3, Finset.mem_filter, Finset.mem_range] at hi hj
  have hei := S.stepEdge3_spec Z hi.2
  have hej := S.stepEdge3_spec Z hj.2
  rw [hij] at hei
  exact S.stepE3_inj Z hnd (by omega) (by omega) hei hej

/-! ### The metric constraint -/

/-- A check-check step of a `Γ`-chain carries a bulk edge between checks at `ℓ1` distance `1`. -/
theorem cc_step3 {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {u v : PVert3 T w h}
    (hg : S.gadj3 Z ny E (.inl u) (.inl v)) :
    ∃ e, S.stepE3 Z E (.inl u) (.inl v) e ∧ cl1_3 u v = 1 ∧ ¬ e.isHalf := by
  rcases hg with ⟨e, he, huv, hc⟩ | ⟨e, he, huv, hc⟩
  · exact ⟨e, ⟨he, huv, hc⟩, cl1_3_of_ends he huv⟩
  · have he' : e.ends = {u, v} := by rw [he, Finset.pair_comm]
    exact ⟨e, ⟨he', fun h1 => huv h1.symm, hc⟩, cl1_3_of_ends he' fun h1 => huv h1.symm⟩

/-- **The λ-trick, deterministic part (position form)**: along a Nodup `Γ`-chain `l` whose end nodes are not
checks, `wmin` times the total displacement of the runs of checks that end before a non-check node is at most the
sum, over the family nodes of `l`, of the pair cost of their neighbouring checks. -/
theorem metric_pos3 (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin : ℝ} (hmin0 : 0 ≤ wmin)
    (hmin : ∀ e, ¬ e.isHalf → wmin ≤ Z.wt e) {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)}
    (hnd : l.Nodup) (hch : List.IsChain (S.gadj3 Z ny E) l) (hl : l ≠ []) (h0 : ∀ u, nd3 l 0 ≠ .inl u)
    (hlast : ∀ u, nd3 l (l.length - 1) ≠ .inl u) :
    wmin * ((∑ i ∈ (range (l.length - 1)).filter (fun i => isChk3 (nd3 l i) ∧ ¬ isChk3 (nd3 l (i + 1))),
        pot3 (fun i => isChk3 (nd3 l i)) (fun i => gchk3 (nd3 l i)) i : ℕ) : ℝ) ≤
      ∑ k ∈ range l.length, if isFam3 (nd3 l k) then pairCost3 Z.wt (stT3 l k) else 0 := by
  set c : ℕ → Prop := fun i => isChk3 (nd3 l i) with hc
  set pt : ℕ → PVert3 T w h := fun i => gchk3 (nd3 l i) with hpt
  have hlen : 1 ≤ l.length := List.length_pos_of_ne_nil hl
  -- check-check steps
  have hcc : ∀ i, i + 1 < l.length → c i → c (i + 1) →
      ∃ e, S.stepE3 Z E (nd3 l i) (nd3 l (i + 1)) e ∧ cl1_3 (pt i) (pt (i + 1)) = 1 ∧ ¬ e.isHalf := by
    intro i hi hci hci1
    have hg : S.gadj3 Z ny E (nd3 l i) (nd3 l (i + 1)) :=
      chain_step hch (getElem?_nd3 (by omega)) (getElem?_nd3 hi)
    rw [nd3_isChk hci, nd3_isChk hci1] at hg ⊢
    exact S.cc_step3 Z hg
  -- runs
  have hruns := runs_le3 c pt (l.length - 1) (fun i hi hci hci1 => by
      obtain ⟨e, -, h1, -⟩ := hcc i (by omega) hci hci1
      exact h1.le)
    (l.length - 1) le_rfl
  set ccPos := (range (l.length - 1)).filter (fun i => c i ∧ c (i + 1)) with hccPos
  have hsum_le : ((∑ i ∈ (range (l.length - 1)).filter (fun i => c i ∧ ¬ c (i + 1)), pot3 c pt i : ℕ) : ℝ) ≤
      (ccPos.card : ℝ) := by
    exact_mod_cast (Nat.le_add_right _ _).trans hruns
  -- the step edges of ccPos are bulk
  have hsub : ccPos ⊆ S.stepPos3 Z E l := by
    intro i hi
    simp only [hccPos, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨e, he, -⟩ := hcc i (by omega) hi.2.1 hi.2.2
    simp only [stepPos3, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi.1, e, he⟩
  have hbulk : ∀ i ∈ ccPos, wmin ≤ Z.wt (S.stepEdge3 Z E l i) := by
    intro i hi
    simp only [hccPos, Finset.mem_filter, Finset.mem_range] at hi
    have hci := hi.2.1
    have hci1 := hi.2.2
    obtain ⟨e, he, -⟩ := hcc i (by omega) hci hci1
    have hs := S.stepEdge3_spec Z ⟨e, he⟩
    rw [nd3_isChk hci, nd3_isChk hci1] at hs
    obtain ⟨hends, hne, -⟩ := hs
    exact hmin _ (cl1_3_of_ends hends hne).2
  have hlow : wmin * (ccPos.card : ℝ) ≤ wsum3 Z.wt (S.Pl3 Z E l) := by
    rw [S.wsum3_Pl3 Z hnd]
    calc wmin * (ccPos.card : ℝ) = ∑ _i ∈ ccPos, wmin := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ ccPos, Z.wt (S.stepEdge3 Z E l i) := Finset.sum_le_sum hbulk
      _ ≤ ∑ i ∈ S.stepPos3 Z E l, Z.wt (S.stepEdge3 Z E l i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hwt0 _
  have hup := S.path_X_pairs3 Z hwt0 hch hl h0 hlast
  calc _ ≤ wmin * (ccPos.card : ℝ) := mul_le_mul_of_nonneg_left hsum_le hmin0
    _ ≤ _ := hlow
    _ ≤ _ := hup

/-- **A jump of a T2 path**: if positions `k'` and `k` are non-check nodes with only checks strictly between them
(and at least one), the run ending at `k - 1` is anchored at `k' + 1`. -/
theorem pot_jump3 {l : List (GNode3 T w h)} {k' k : ℕ} (hk : k' + 1 < k) (hk' : ¬ isChk3 (nd3 l k'))
    (hmid : ∀ i, k' < i → i < k → isChk3 (nd3 l i)) :
    pot3 (fun i => isChk3 (nd3 l i)) (fun i => gchk3 (nd3 l i)) (k - 1) =
      cl1_3 (gchk3 (nd3 l (k' + 1))) (gchk3 (nd3 l (k - 1))) := by
  unfold pot3
  rw [ite_eq_left (hmid (k - 1) (by omega) (by omega))]
  rw [anchor3_eq (fun i => isChk3 (nd3 l i)) (fun i => gchk3 (nd3 l i)) (a := k' + 1) (Or.inr (by simpa using hk'))
    (k - 1) (by omega) fun i hi1 hi2 => hmid i (by omega) (by omega)]

/-! ### The constraint at the stations of a T2 path -/

/-- **The λ-trick, deterministic part, at the stations of a T2 path** (check level). Stations: positions
`p 0 = 0 < p 1 < … < p (m+1) = |l| - 1` of `l`, with family nodes at `p 1, …, p m` and at no other inner position;
`u i` is the entry check of station `i` (the node before `p i`, `1 ≤ i ≤ m+1`) and `v i` its exit check (the node
after `p i`, `0 ≤ i ≤ m`). Jump `i` runs from `v i` to `u (i+1)`. Then `wmin` times the total `ℓ1` length of the
jumps is at most `wmax` times the total `ℓ1` span of the intermediate families plus the two boundary legs (the legs
are kept in every variant; they are needed only when the ends are families). -/
theorem metric_stations3 (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin wmax wh : ℝ}
    (hmin0 : 0 ≤ wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hmin : ∀ e, ¬ e.isHalf → wmin ≤ Z.wt e) (hmax : ∀ e, ¬ e.isHalf → Z.wt e ≤ wmax)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh)
    {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hhd : l.head? = some x) (hlst : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj3 Z ny E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → PVert3 T w h)
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hp0 : p 0 = 0) (hpl : p (m + 1) = l.length - 1)
    (hfam : ∀ i, 1 ≤ i → i ≤ m → isFam3 (nd3 l (p i)))
    (hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam3 (nd3 l k))
    (hu : ∀ i, 1 ≤ i → i ≤ m + 1 → nd3 l (p i - 1) = .inl (u i))
    (hv : ∀ i ≤ m, nd3 l (p i + 1) = .inl (v i)) :
    wmin * ∑ i ∈ range (m + 1), (cl1_3 (v i) (u (i + 1)) : ℝ) ≤
      wmax * ∑ i ∈ range m, (cl1_3 (u (i + 1)) (v (i + 1)) : ℝ) + wmax * ((v 0).2.2.val : ℝ) +
        wmax * ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) + 2 * wh := by
  have hl : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hnd0 : nd3 l 0 = x := nd3_of_getElem? (by rw [← List.head?_eq_getElem?]; exact hhd)
  have hndl : nd3 l (l.length - 1) = y := nd3_of_getElem? (by rw [← List.getLast?_eq_getElem?]; exact hlst)
  have h0 : ∀ u, nd3 l 0 ≠ .inl u := by
    intro u hu
    rw [hnd0] at hu
    subst hu
    rcases hx with hc | hc
    · cases hc
    · exact hc
  have hlast : ∀ u, nd3 l (l.length - 1) ≠ .inl u := by
    intro u hu
    rw [hndl] at hu
    subst hu
    rcases hy with hc | hc
    · cases hc
    · exact hc
  -- the stations
  have hmono : ∀ i j, i ≤ j → j ≤ m + 1 → p i ≤ p j := by
    intro i j hij hj
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (hp i j hlt hj).le
  have hpl' : ∀ i ≤ m + 1, p i ≤ l.length - 1 := fun i hi => hpl ▸ hmono i (m + 1) hi le_rfl
  have hlen2 : 2 ≤ l.length := by
    have := hp 0 (m + 1) (by omega) le_rfl
    omega
  have hother : ∀ k, k < l.length → (∀ i ≤ m + 1, k ≠ p i) → isChk3 (nd3 l k) := by
    intro k hk hne
    have hk0 : 0 < k := by
      have := hne 0 (by omega)
      rw [hp0] at this
      omega
    have hk1 : k + 1 < l.length := by
      have := hne (m + 1) le_rfl
      rw [hpl] at this
      omega
    obtain ⟨z, hz⟩ := inner_check3 hhd hlst hnd hbd hk0 hk1 (getElem?_nd3 hk)
      (fun F hF => hnofam k hne ⟨F, hF⟩)
    exact ⟨z, hz⟩
  have hnc : ∀ i ≤ m + 1, ¬ isChk3 (nd3 l (p i)) := by
    rintro i hi ⟨z, hz⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hp0] at hz
      exact h0 z hz
    · rcases Nat.lt_or_ge i (m + 1) with hi1 | hi1
      · obtain ⟨F, hF⟩ := hfam i hi0 (by omega)
        rw [hF] at hz
        cases hz
      · have : i = m + 1 := by omega
        subst this
        rw [hpl] at hz
        exact hlast z hz
  have hbetween : ∀ i ≤ m, ∀ k, p i < k → k < p (i + 1) → isChk3 (nd3 l k) := by
    intro i hi k hk1 hk2
    refine hother k (by have := hpl' (i + 1) (by omega); omega) fun j hj hkj => ?_
    subst hkj
    rcases Nat.lt_or_ge i j with hlt | hge
    · have := hmono (i + 1) j (by omega) hj
      omega
    · have := hmono j i hge (by omega)
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
  have hpot : ∀ i ≤ m, pot3 (fun k => isChk3 (nd3 l k)) (fun k => gchk3 (nd3 l k)) (p (i + 1) - 1) =
      cl1_3 (v i) (u (i + 1)) := by
    intro i hi
    rw [pot_jump3 (hgap i hi) (hnc i (by omega)) (hbetween i hi), hv i hi, hu (i + 1) (by omega) (by omega)]
    rfl
  have hF : (range (l.length - 1)).filter (fun j => isChk3 (nd3 l j) ∧ ¬ isChk3 (nd3 l (j + 1))) =
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
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hp (i + 1) (j + 1) (by omega) (by omega)
      omega
    · have := hp (j + 1) (i + 1) (by omega) (by omega)
      omega
  have hLHS : (∑ j ∈ (range (l.length - 1)).filter (fun j => isChk3 (nd3 l j) ∧ ¬ isChk3 (nd3 l (j + 1))),
      pot3 (fun k => isChk3 (nd3 l k)) (fun k => gchk3 (nd3 l k)) j) =
        ∑ i ∈ range (m + 1), cl1_3 (v i) (u (i + 1)) := by
    rw [hF, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun i hi => hpot i (by simp only [Finset.mem_range] at hi; omega)
  -- the families
  have hpinj : ∀ i ∈ range (m + 2), ∀ j ∈ range (m + 2), p i = p j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hp i j hlt (by omega)
      omega
    · have := hp j i hgt (by omega)
      omega
  have hRHS : (∑ k ∈ range l.length, if isFam3 (nd3 l k) then pairCost3 Z.wt (stT3 l k) else 0) =
      ∑ i ∈ range (m + 2), if isFam3 (nd3 l (p i)) then pairCost3 Z.wt (stT3 l (p i)) else 0 := by
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
  have hb0 : (if isFam3 (nd3 l (p 0)) then pairCost3 Z.wt (stT3 l (p 0)) else 0) ≤
      wmax * ((v 0).2.2.val : ℝ) + wh := by
    by_cases hfx : isFam3 (nd3 l (p 0))
    · rw [ite_eq_left hfx]
      have hst : stT3 l (p 0) = Pi.single (v 0) 1 := by
        unfold stT3
        rw [hp0, ite_eq_right (lt_irrefl 0), ite_eq_left (by omega : 0 + 1 < l.length), zero_add]
        have := hv 0 (by omega)
        rw [hp0] at this
        rw [this]
        rfl
      rw [hst]
      have := pairCost3_le_bot hmax hwt0 hwh (v 0)
      linarith [mul_comm ((v 0).2.2.val : ℝ) wmax]
    · rw [ite_eq_right hfx]
      positivity
  have hbl : (if isFam3 (nd3 l (p (m + 1))) then pairCost3 Z.wt (stT3 l (p (m + 1))) else 0) ≤
      wmax * ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) + wh := by
    by_cases hfy : isFam3 (nd3 l (p (m + 1)))
    · rw [ite_eq_left hfy]
      have hst : stT3 l (p (m + 1)) = Pi.single (u (m + 1)) 1 := by
        unfold stT3
        rw [hpl, ite_eq_left (by omega : 0 < l.length - 1),
          ite_eq_right (by omega : ¬ (l.length - 1 + 1 < l.length)), add_zero]
        have := hu (m + 1) (by omega) le_rfl
        rw [hpl] at this
        rw [this]
        rfl
      rw [hst]
      have := pairCost3_le_top hmax hwt0 hwh (u (m + 1))
      linarith [mul_comm ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) wmax]
    · rw [ite_eq_right hfy]
      positivity
  have hbi : ∀ i ∈ range m, (if isFam3 (nd3 l (p (i + 1))) then pairCost3 Z.wt (stT3 l (p (i + 1))) else 0) ≤
      wmax * (cl1_3 (u (i + 1)) (v (i + 1)) : ℝ) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_left (hfam (i + 1) (by omega) (by omega))]
    have hpos : 0 < p (i + 1) := by
      have := hp 0 (i + 1) (by omega) (by omega)
      omega
    have hlt : p (i + 1) + 1 < l.length := by
      have := hp (i + 1) (m + 1) (by omega) le_rfl
      omega
    have hst : stT3 l (p (i + 1)) = Pi.single (u (i + 1)) 1 + Pi.single (v (i + 1)) 1 := by
      unfold stT3
      rw [ite_eq_left hpos, ite_eq_left hlt, hu (i + 1) (by omega) (by omega), hv (i + 1) (by omega)]
      rfl
    rw [hst]
    have := pairCost3_le_l1 hmax hwt0 (u (i + 1)) (v (i + 1))
    rw [mul_comm]
    exact this
  -- assemble
  have hsplit : (∑ i ∈ range (m + 2), if isFam3 (nd3 l (p i)) then pairCost3 Z.wt (stT3 l (p i)) else 0) =
      (if isFam3 (nd3 l (p 0)) then pairCost3 Z.wt (stT3 l (p 0)) else 0) +
      (∑ i ∈ range m, if isFam3 (nd3 l (p (i + 1))) then pairCost3 Z.wt (stT3 l (p (i + 1))) else 0) +
      (if isFam3 (nd3 l (p (m + 1))) then pairCost3 Z.wt (stT3 l (p (m + 1))) else 0) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  have hmain := S.metric_pos3 Z hwt0 hmin0 hmin hnd hch hl h0 hlast
  rw [hLHS, hRHS, hsplit] at hmain
  have hsum := Finset.sum_le_sum hbi
  rw [← Finset.mul_sum] at hsum
  push_cast at hmain
  linarith

/-- **The λ-trick, deterministic part, in block units**: `metric_stations3` with each check-level `ℓ1` distance
replaced by `35` times the block `ℓ1` displacement (`l1_ge_block3`, `l1_le_block3`; each costs `3 · 34`). -/
theorem metric_stations_block3 (hwt0 : ∀ e, 0 ≤ Z.wt e) {wmin wmax wh : ℝ}
    (hmin0 : 0 ≤ wmin) (hmax0 : 0 ≤ wmax) (hwh0 : 0 ≤ wh)
    (hmin : ∀ e, ¬ e.isHalf → wmin ≤ Z.wt e) (hmax : ∀ e, ¬ e.isHalf → Z.wt e ≤ wmax)
    (hwh : ∀ e, e.isHalf → Z.wt e ≤ wh)
    {ny : ℕ} {E : PEdge3 T w h → ZMod 2} {l : List (GNode3 T w h)} {x y : GNode3 T w h}
    (hhd : l.head? = some x) (hlst : l.getLast? = some y) (hnd : l.Nodup)
    (hch : List.IsChain (S.gadj3 Z ny E) l)
    (hx : x = .inr (.inl false) ∨ S.botFam3 ny E x) (hy : y = .inr (.inl true) ∨ S.topFam3 ny E y)
    (hbd : ∀ b : Bool, (.inr (.inl b) : GNode3 T w h) ∈ l →
      (.inr (.inl b) : GNode3 T w h) = x ∨ (.inr (.inl b) : GNode3 T w h) = y)
    (m : ℕ) (p : ℕ → ℕ) (u v : ℕ → PVert3 T w h)
    (hp : ∀ i j, i < j → j ≤ m + 1 → p i < p j) (hp0 : p 0 = 0) (hpl : p (m + 1) = l.length - 1)
    (hfam : ∀ i, 1 ≤ i → i ≤ m → isFam3 (nd3 l (p i)))
    (hnofam : ∀ k, (∀ i ≤ m + 1, k ≠ p i) → ¬ isFam3 (nd3 l k))
    (hu : ∀ i, 1 ≤ i → i ≤ m + 1 → nd3 l (p i - 1) = .inl (u i))
    (hv : ∀ i ≤ m, nd3 l (p i + 1) = .inl (v i)) :
    wmin * ((35 : ℝ) * ∑ i ∈ range (m + 1), (blockL1_3 (v i) (u (i + 1)) : ℝ)) ≤
      wmax * ((35 : ℝ) * ∑ i ∈ range m, (blockL1_3 (u (i + 1)) (v (i + 1)) : ℝ)) +
        (wmin * (m + 1) + wmax * m) * ((3 * 34 : ℕ) : ℝ) + wmax * ((v 0).2.2.val : ℝ) +
        wmax * ((h - (u (m + 1)).2.2.val : ℕ) : ℝ) + 2 * wh := by
  have hc := S.metric_stations3 Z hwt0 hmin0 hmax0 hwh0 hmin hmax hwh hhd hlst hnd hch hx hy hbd m p u v hp hp0
    hpl hfam hnofam hu hv
  set c : ℝ := ((3 * 34 : ℕ) : ℝ) with hcdef
  have hjump : ∀ i ∈ range (m + 1), (35 : ℝ) * (blockL1_3 (v i) (u (i + 1)) : ℝ) ≤
      (cl1_3 (v i) (u (i + 1)) : ℝ) + c := by
    intro i _
    have := l1_ge_block3 (v i) (u (i + 1))
    rw [hcdef]
    exact_mod_cast this
  have hfamb : ∀ i ∈ range m, (cl1_3 (u (i + 1)) (v (i + 1)) : ℝ) ≤
      (35 : ℝ) * (blockL1_3 (u (i + 1)) (v (i + 1)) : ℝ) + c := by
    intro i _
    have := l1_le_block3 (u (i + 1)) (v (i + 1))
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

end Stage13

end QECD1
