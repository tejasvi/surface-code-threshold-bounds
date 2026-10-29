import QECD1.T2PathX3

/-!
# The metric input (M) on the 3D code: weights of edge sets against `ℓ1` distances

The 3D analogue of the 2D `TwoD/T2Metric`, with the time direction added.

* `sum_pedge3`: a sum over the edges by constructor (`PEdge3.equivSum`).
* `sum_psyn3_P`, `pair_count`: the odd checks of `X` in a set `P` count each edge by the number of its ends in `P`.
* `sum_psyn3_tcut`, `sum_psyn3_xcut`, `sum_psyn3_ycut` (cut handshakes): for an edge set without half-edges, the
  parity of its odd checks at `t ≤ k` (`x ≤ k`, `y ≤ k`) is the parity of its time (horizontal, vertical) edges
  crossing the cut.
* `exists_tcross`, `exists_xcross`, `exists_ycross`: an edge set without half-edges whose odd checks are `{u, v}`
  crosses every cut between `u` and `v`.
* `wsum3_ge_l1`: with bulk weights at least `wmin ≥ 0`, such an edge set weighs at least `wmin · |u - v|_1`.
* `exists_stair3`, `pairCost3_le_l1`: with bulk weights at most `wmax`, a staircase (time, then x, then y segment)
  joins `u` and `v` with weight at most `wmax · |u - v|_1`.
* `exists_leg_bot3`, `exists_leg_top3`: a check is joined to a rough side by a vertical segment and a half-edge.
-/

open Finset

namespace QECD1

variable {T w h : ℕ}

/-- `PEdge3` as a sum type, for sums by constructor. -/
def PEdge3.equivSum : PEdge3 T w h ≃
    (Fin (T + 1) × Fin w × Fin (h + 1)) ⊕ (Fin (T + 1) × Fin (w + 1) × Fin h) ⊕ (Fin T × Fin (w + 1) × Fin (h + 1)) ⊕
      (Fin (T + 1) × Fin (w + 1)) ⊕ (Fin (T + 1) × Fin (w + 1)) where
  toFun
    | .hor t x y => .inl (t, x, y)
    | .ver t x y => .inr (.inl (t, x, y))
    | .time t x y => .inr (.inr (.inl (t, x, y)))
    | .bot t x => .inr (.inr (.inr (.inl (t, x))))
    | .top t x => .inr (.inr (.inr (.inr (t, x))))
  invFun
    | .inl (t, x, y) => .hor t x y
    | .inr (.inl (t, x, y)) => .ver t x y
    | .inr (.inr (.inl (t, x, y))) => .time t x y
    | .inr (.inr (.inr (.inl (t, x)))) => .bot t x
    | .inr (.inr (.inr (.inr (t, x)))) => .top t x
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x, y⟩ | ⟨t, x⟩ | ⟨t, x⟩ <;> rfl

/-- A sum over the edges by constructor. -/
theorem sum_pedge3 {M : Type} [AddCommMonoid M] (g : PEdge3 T w h → M) :
    ∑ f, g f = (∑ p : Fin (T + 1) × Fin w × Fin (h + 1), g (.hor p.1 p.2.1 p.2.2)) +
      ((∑ p : Fin (T + 1) × Fin (w + 1) × Fin h, g (.ver p.1 p.2.1 p.2.2)) +
        ((∑ p : Fin T × Fin (w + 1) × Fin (h + 1), g (.time p.1 p.2.1 p.2.2)) +
          ((∑ p : Fin (T + 1) × Fin (w + 1), g (.bot p.1 p.2)) +
            ∑ p : Fin (T + 1) × Fin (w + 1), g (.top p.1 p.2)))) := by
  rw [← PEdge3.equivSum.symm.sum_comp]
  simp only [Fintype.sum_sum_type]
  rfl

theorem sum_psyn3_P (X : PEdge3 T w h → ZMod 2) (P : PVert3 T w h → Prop) [DecidablePred P] :
    ∑ v, (if P v then psyn3 X v else 0) = ∑ f, X f * (((f.ends.filter P).card : ℕ) : ZMod 2) := by
  have hv : ∀ v, (if P v then psyn3 X v else 0) =
      ∑ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => v ∈ e.ends), (if P v then X e else 0) := by
    intro v
    unfold psyn3
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun v _ => hv v]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun e => e.ends) (by intro v e; simp)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mul_comm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem two_eq_zero3 : ((2 : ℕ) : ZMod 2) = 0 := by decide

/-- A bulk edge counts `0` if both or none of its ends are in `P`, and `X f` otherwise. -/
theorem pair_count (X : PEdge3 T w h → ZMod 2) (f : PEdge3 T w h) {a b : PVert3 T w h} (hab : a ≠ b)
    (P : PVert3 T w h → Prop) [DecidablePred P] :
    X f * (((({a, b} : Finset (PVert3 T w h)).filter P).card : ℕ) : ZMod 2) = if (P a ↔ P b) then 0 else X f := by
  by_cases ha : P a <;> by_cases hb : P b
  · rw [Finset.filter_true_of_mem (by simp [ha, hb]), Finset.card_pair hab, two_eq_zero3, mul_zero,
      if_pos (iff_of_true ha hb)]
  · have hf : ({a, b} : Finset (PVert3 T w h)).filter P = {a} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz hb
      · rintro rfl
        exact ⟨Or.inl rfl, ha⟩
    rw [hf, Finset.card_singleton, if_neg (fun hiff => hb (hiff.1 ha))]
    simp
  · have hf : ({a, b} : Finset (PVert3 T w h)).filter P = {b} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · exact absurd hz ha
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, hb⟩
    rw [hf, Finset.card_singleton, if_neg (fun hiff => ha (hiff.2 hb))]
    simp
  · rw [Finset.filter_false_of_mem (by simp [ha, hb]), Finset.card_empty, if_pos (iff_of_false ha hb)]
    simp

/-- **Cut handshake (time cut).** -/
theorem sum_psyn3_tcut (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0) (k : ℕ)
    (hk : k < T) :
    ∑ v : PVert3 T w h, (if v.1.val ≤ k then psyn3 X v else 0) =
      ∑ x : Fin (w + 1), ∑ y : Fin (h + 1), X (.time ⟨k, hk⟩ x y) := by
  rw [sum_psyn3_P, sum_pedge3]
  have hhor : ∀ p : Fin (T + 1) × Fin w × Fin (h + 1), X (.hor p.1 p.2.1 p.2.2) *
      ((((PEdge3.hor p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.1.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have hver : ∀ p : Fin (T + 1) × Fin (w + 1) × Fin h, X (.ver p.1 p.2.1 p.2.2) *
      ((((PEdge3.ver p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.1.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have htime : ∀ p : Fin T × Fin (w + 1) × Fin (h + 1), X (.time p.1 p.2.1 p.2.2) *
      ((((PEdge3.time p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.1.val ≤ k)).card : ℕ) :
        ZMod 2) = if p.1.val = k then X (.time p.1 p.2.1 p.2.2) else 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff])]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hp : p.1.val = k
    · rw [if_neg (by omega), if_pos hp]
    · rw [if_neg hp]
      by_cases hp2 : p.1.val < k
      · rw [if_pos (by omega)]
      · rw [if_pos (by omega)]
  have hb0 : ∀ t x, X (.bot t x) = 0 := fun t x => (hX t x).1
  have ht0 : ∀ t x, X (.top t x) = 0 := fun t x => (hX t x).2
  rw [Finset.sum_eq_zero fun p _ => hhor p, Finset.sum_eq_zero fun p _ => hver p]
  simp only [hb0, ht0, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_congr rfl fun p _ => htime p, Fintype.sum_prod_type, Finset.sum_eq_single (⟨k, hk⟩ : Fin T)]
  · simp [Fintype.sum_prod_type]
  · intro b _ hb
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg (fun hq => hb (Fin.ext hq))]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- **Cut handshake (x cut).** -/
theorem sum_psyn3_xcut (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0) (k : ℕ)
    (hk : k < w) :
    ∑ v : PVert3 T w h, (if v.2.1.val ≤ k then psyn3 X v else 0) =
      ∑ t : Fin (T + 1), ∑ y : Fin (h + 1), X (.hor t ⟨k, hk⟩ y) := by
  rw [sum_psyn3_P, sum_pedge3]
  have hhor : ∀ p : Fin (T + 1) × Fin w × Fin (h + 1), X (.hor p.1 p.2.1 p.2.2) *
      ((((PEdge3.hor p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.1.val ≤ k)).card : ℕ) :
        ZMod 2) = if p.2.1.val = k then X (.hor p.1 p.2.1 p.2.2) else 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff])]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hp : p.2.1.val = k
    · rw [if_neg (by omega), if_pos hp]
    · rw [if_neg hp]
      by_cases hp2 : p.2.1.val < k
      · rw [if_pos (by omega)]
      · rw [if_pos (by omega)]
  have hver : ∀ p : Fin (T + 1) × Fin (w + 1) × Fin h, X (.ver p.1 p.2.1 p.2.2) *
      ((((PEdge3.ver p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.1.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have htime : ∀ p : Fin T × Fin (w + 1) × Fin (h + 1), X (.time p.1 p.2.1 p.2.2) *
      ((((PEdge3.time p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.1.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have hb0 : ∀ t x, X (.bot t x) = 0 := fun t x => (hX t x).1
  have ht0 : ∀ t x, X (.top t x) = 0 := fun t x => (hX t x).2
  rw [Finset.sum_eq_zero fun p _ => hver p, Finset.sum_eq_zero fun p _ => htime p]
  simp only [hb0, ht0, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_congr rfl fun p _ => hhor p, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨k, hk⟩ : Fin w)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg (fun hq => hb (Fin.ext hq))]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- **Cut handshake (y cut).** -/
theorem sum_psyn3_ycut (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0) (k : ℕ)
    (hk : k < h) :
    ∑ v : PVert3 T w h, (if v.2.2.val ≤ k then psyn3 X v else 0) =
      ∑ t : Fin (T + 1), ∑ x : Fin (w + 1), X (.ver t x ⟨k, hk⟩) := by
  rw [sum_psyn3_P, sum_pedge3]
  have hhor : ∀ p : Fin (T + 1) × Fin w × Fin (h + 1), X (.hor p.1 p.2.1 p.2.2) *
      ((((PEdge3.hor p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.2.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have hver : ∀ p : Fin (T + 1) × Fin (w + 1) × Fin h, X (.ver p.1 p.2.1 p.2.2) *
      ((((PEdge3.ver p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.2.val ≤ k)).card : ℕ) :
        ZMod 2) = if p.2.2.val = k then X (.ver p.1 p.2.1 p.2.2) else 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff])]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hp : p.2.2.val = k
    · rw [if_neg (by omega), if_pos hp]
    · rw [if_neg hp]
      by_cases hp2 : p.2.2.val < k
      · rw [if_pos (by omega)]
      · rw [if_pos (by omega)]
  have htime : ∀ p : Fin T × Fin (w + 1) × Fin (h + 1), X (.time p.1 p.2.1 p.2.2) *
      ((((PEdge3.time p.1 p.2.1 p.2.2 : PEdge3 T w h).ends.filter (fun v : PVert3 T w h => v.2.2.val ≤ k)).card : ℕ) :
        ZMod 2) = 0 := by
    intro p
    simp only [PEdge3.ends]
    rw [pair_count X _ (by simp [Prod.ext_iff, Fin.ext_iff]), if_pos Iff.rfl]
  have hb0 : ∀ t x, X (.bot t x) = 0 := fun t x => (hX t x).1
  have ht0 : ∀ t x, X (.top t x) = 0 := fun t x => (hX t x).2
  rw [Finset.sum_eq_zero fun p _ => hhor p, Finset.sum_eq_zero fun p _ => htime p]
  simp only [hb0, ht0, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_congr rfl fun p _ => hver p, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin h)]
  · simp
  · intro b _ hb
    rw [if_neg (fun hq => hb (Fin.ext hq))]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem sum_single_pair_P3 {u v : PVert3 T w h} (P : PVert3 T w h → Prop) [DecidablePred P] :
    ∑ z : PVert3 T w h, (if P z then (Pi.single u 1 + Pi.single v 1 : PVert3 T w h → ZMod 2) z else 0) =
      (if P u then 1 else 0) + (if P v then 1 else 0) := by
  simp only [Pi.add_apply, ite_add_zero, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

theorem cut_one {a b k : ℕ} (hk1 : min a b ≤ k) (hk2 : k < max a b) :
    (if a ≤ k then (1 : ZMod 2) else 0) + (if b ≤ k then 1 else 0) = 1 := by
  by_cases ha : a ≤ k <;> by_cases hb : b ≤ k <;> simp only [ha, hb, if_true, if_false]
  · omega
  · simp
  · simp
  · omega

/-- An edge set without half-edges with odd checks `{u, v}` crosses every time cut between them. -/
theorem exists_tcross (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0)
    {u v : PVert3 T w h} (hpsyn : psyn3 X = Pi.single u 1 + Pi.single v 1) {k : ℕ}
    (hk1 : min u.1.val v.1.val ≤ k) (hk2 : k < max u.1.val v.1.val) :
    ∃ x y, X (.time ⟨k, by have := u.1.isLt; have := v.1.isLt; omega⟩ x y) ≠ 0 := by
  have hk : k < T := by have := u.1.isLt; have := v.1.isLt; omega
  have hsum := sum_psyn3_tcut X hX k hk
  rw [hpsyn, sum_single_pair_P3, cut_one hk1 hk2] at hsum
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero)
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact ⟨x, y, hy⟩

/-- An edge set without half-edges with odd checks `{u, v}` crosses every x cut between them. -/
theorem exists_xcross (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0)
    {u v : PVert3 T w h} (hpsyn : psyn3 X = Pi.single u 1 + Pi.single v 1) {k : ℕ}
    (hk1 : min u.2.1.val v.2.1.val ≤ k) (hk2 : k < max u.2.1.val v.2.1.val) :
    ∃ t y, X (.hor t ⟨k, by have := u.2.1.isLt; have := v.2.1.isLt; omega⟩ y) ≠ 0 := by
  have hk : k < w := by have := u.2.1.isLt; have := v.2.1.isLt; omega
  have hsum := sum_psyn3_xcut X hX k hk
  rw [hpsyn, sum_single_pair_P3, cut_one hk1 hk2] at hsum
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero)
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  exact ⟨t, y, hy⟩

/-- An edge set without half-edges with odd checks `{u, v}` crosses every y cut between them. -/
theorem exists_ycross (X : PEdge3 T w h → ZMod 2) (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0)
    {u v : PVert3 T w h} (hpsyn : psyn3 X = Pi.single u 1 + Pi.single v 1) {k : ℕ}
    (hk1 : min u.2.2.val v.2.2.val ≤ k) (hk2 : k < max u.2.2.val v.2.2.val) :
    ∃ t x, X (.ver t x ⟨k, by have := u.2.2.isLt; have := v.2.2.isLt; omega⟩) ≠ 0 := by
  have hk : k < h := by have := u.2.2.isLt; have := v.2.2.isLt; omega
  have hsum := sum_psyn3_ycut X hX k hk
  rw [hpsyn, sum_single_pair_P3, cut_one hk1 hk2] at hsum
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero)
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  exact ⟨t, x, hx⟩

/-- The `ℓ1` distance of two checks. -/
def cl1_3 (u v : PVert3 T w h) : ℕ :=
  ((u.1.val : ℤ) - v.1.val).natAbs + ((u.2.1.val : ℤ) - v.2.1.val).natAbs + ((u.2.2.val : ℤ) - v.2.2.val).natAbs

/-- The layer of a time edge, the column of a horizontal edge, the row of a vertical edge (0 for the others). -/
def tlay3 : PEdge3 T w h → ℕ
  | .time t _ _ => t.val
  | _ => 0

def hcol3 : PEdge3 T w h → ℕ
  | .hor _ x _ => x.val
  | _ => 0

def vrow3 : PEdge3 T w h → ℕ
  | .ver _ _ y => y.val
  | _ => 0

def isTime3 : PEdge3 T w h → Prop
  | .time _ _ _ => True
  | _ => False

def isHor3 : PEdge3 T w h → Prop
  | .hor _ _ _ => True
  | _ => False

def isVer3 : PEdge3 T w h → Prop
  | .ver _ _ _ => True
  | _ => False

/-- **Weight against `ℓ1` distance**: with bulk weights at least `wmin ≥ 0` (and all weights `≥ 0`), an edge set
without half-edges whose odd checks are `{u, v}` weighs at least `wmin · |u - v|_1`. -/
theorem wsum3_ge_l1 {wt : PEdge3 T w h → ℝ} {wmin : ℝ} (hmin0 : 0 ≤ wmin) (hwt0 : ∀ e, 0 ≤ wt e)
    (hwt : ∀ e, ¬ e.isHalf → wmin ≤ wt e) (X : PEdge3 T w h → ZMod 2)
    (hX : ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0) {u v : PVert3 T w h}
    (hpsyn : psyn3 X = Pi.single u 1 + Pi.single v 1) :
    wmin * (cl1_3 u v : ℝ) ≤ wsum3 wt X := by
  classical
  set St := univ.filter (fun e : PEdge3 T w h => X e ≠ 0 ∧ isTime3 e) with hSt
  set Sh := univ.filter (fun e : PEdge3 T w h => X e ≠ 0 ∧ isHor3 e) with hSh
  set Sv := univ.filter (fun e : PEdge3 T w h => X e ≠ 0 ∧ isVer3 e) with hSv
  have hcardt : ((u.1.val : ℤ) - v.1.val).natAbs ≤ St.card := by
    have hsub : Finset.Ico (min u.1.val v.1.val) (max u.1.val v.1.val) ⊆ St.image tlay3 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨x, y, hxy⟩ := exists_tcross X hX hpsyn hk.1 hk.2
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy, trivial⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := St) (f := tlay3)
    rw [Nat.card_Ico] at h1
    omega
  have hcardh : ((u.2.1.val : ℤ) - v.2.1.val).natAbs ≤ Sh.card := by
    have hsub : Finset.Ico (min u.2.1.val v.2.1.val) (max u.2.1.val v.2.1.val) ⊆ Sh.image hcol3 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨t, y, hty⟩ := exists_xcross X hX hpsyn hk.1 hk.2
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hty, trivial⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := Sh) (f := hcol3)
    rw [Nat.card_Ico] at h1
    omega
  have hcardv : ((u.2.2.val : ℤ) - v.2.2.val).natAbs ≤ Sv.card := by
    have hsub : Finset.Ico (min u.2.2.val v.2.2.val) (max u.2.2.val v.2.2.val) ⊆ Sv.image vrow3 := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨t, x, htx⟩ := exists_ycross X hX hpsyn hk.1 hk.2
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, htx, trivial⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := Sv) (f := vrow3)
    rw [Nat.card_Ico] at h1
    omega
  have hd1 : Disjoint St Sh := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [hSt, Finset.mem_filter] at he
    rw [hSh, Finset.mem_filter] at he'
    cases e <;> simp only [isTime3, isHor3] at he he' <;> first | exact he.2.2 | exact he'.2.2
  have hd2 : Disjoint (St ∪ Sh) Sv := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [hSv, Finset.mem_filter] at he'
    rcases Finset.mem_union.1 he with he | he
    · rw [hSt, Finset.mem_filter] at he
      cases e <;> simp only [isTime3, isVer3] at he he' <;> first | exact he.2.2 | exact he'.2.2
    · rw [hSh, Finset.mem_filter] at he
      cases e <;> simp only [isHor3, isVer3] at he he' <;> first | exact he.2.2 | exact he'.2.2
  have hsupp : St ∪ Sh ∪ Sv ⊆ univ.filter (fun e : PEdge3 T w h => X e ≠ 0) := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2.1⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2.1⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2.1⟩
  have hbulk : ∀ e ∈ St ∪ Sh ∪ Sv, wmin ≤ wt e := by
    intro e he
    refine hwt e ?_
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · have hh := (Finset.mem_filter.1 he).2.2
        cases e <;> simp only [isTime3] at hh <;> exact id
      · have hh := (Finset.mem_filter.1 he).2.2
        cases e <;> simp only [isHor3] at hh <;> exact id
    · have hh := (Finset.mem_filter.1 he).2.2
      cases e <;> simp only [isVer3] at hh <;> exact id
  have hcard : cl1_3 u v ≤ (St ∪ Sh ∪ Sv).card := by
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
    unfold cl1_3
    omega
  calc wmin * (cl1_3 u v : ℝ) ≤ wmin * ((St ∪ Sh ∪ Sv).card : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hmin0
    _ = ((St ∪ Sh ∪ Sv).card : ℝ) * wmin := mul_comm _ _
    _ ≤ ∑ e ∈ St ∪ Sh ∪ Sv, wt e := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ hbulk
    _ ≤ ∑ e ∈ univ.filter (fun e : PEdge3 T w h => X e ≠ 0), wt e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsupp fun e _ _ => hwt0 e
    _ = wsum3 wt X := by rw [Finset.sum_filter]; rfl


/-! ### Upper bounds: staircases and legs -/

theorem wsum3_single (wt : PEdge3 T w h → ℝ) (e : PEdge3 T w h) : wsum3 wt (Pi.single e 1) = wt e := by
  unfold wsum3
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem not_half_of_ends {e : PEdge3 T w h} {u v : PVert3 T w h} (he : e.ends = {u, v}) (huv : u ≠ v) :
    ¬ e.isHalf := by
  intro hh
  have h1 := card_ends_half e hh
  rw [he, Finset.card_pair huv] at h1
  omega

theorem psyn3_single_pair {e : PEdge3 T w h} {u v : PVert3 T w h} (he : e.ends = {u, v}) (huv : u ≠ v) :
    psyn3 (Pi.single e 1) = Pi.single u 1 + Pi.single v 1 := by
  rw [psyn3_single, he]
  funext z
  simp only [Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, Pi.single_apply]
  by_cases h1 : z = u
  · subst h1
    simp [huv]
  · by_cases h2 : z = v
    · subst h2
      simp [h1]
    · simp [h1, h2]

theorem add_add_cancel3 (A B C : PVert3 T w h → ZMod 2) : A + B + (B + C) = A + C := by
  rw [add_assoc, ← add_assoc B, fun_add_self3, zero_add]

/-- Edge sets along a line of adjacent checks, with weight at most `wmax` per step. -/
theorem line_edges {wt : PEdge3 T w h → ℝ} {wmax : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) {n : ℕ} (line : ℕ → PVert3 T w h) (hadj : ∀ j, j < n → adj3 (line j) (line (j + 1)))
    (a : ℕ) : ∀ d, a + d ≤ n → ∃ X : PEdge3 T w h → ZMod 2,
      psyn3 X = Pi.single (line a) 1 + Pi.single (line (a + d)) 1 ∧ wsum3 wt X ≤ d * wmax ∧
        ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨0, ?_, by simp [wsum3], fun _ _ => ⟨rfl, rfl⟩⟩
    rw [psyn3_zero, Nat.add_zero a, fun_add_self3]
  | succ d ih =>
    intro hd
    obtain ⟨X, hX, hw, hhalf⟩ := ih (by omega)
    obtain ⟨e, he, hne⟩ := hadj (a + d) (by omega)
    have hbulk := not_half_of_ends he hne
    refine ⟨X + Pi.single e 1, ?_, ?_, fun t x => ⟨?_, ?_⟩⟩
    · rw [psyn3_add, hX, psyn3_single_pair he hne, add_add_cancel3, show a + (d + 1) = a + d + 1 by omega]
    · calc wsum3 wt (X + Pi.single e 1) ≤ wsum3 wt X + wsum3 wt (Pi.single e 1) := wsum3_add_le hwt0 _ _
        _ ≤ d * wmax + wmax := by rw [wsum3_single]; exact add_le_add hw (hwt e hbulk)
        _ = ((d + 1 : ℕ) : ℝ) * wmax := by push_cast; ring
    · have hne' : (PEdge3.bot t x : PEdge3 T w h) ≠ e := fun hc => hbulk (hc ▸ trivial)
      simp [(hhalf t x).1, Pi.single_apply, hne']
    · have hne' : (PEdge3.top t x : PEdge3 T w h) ≠ e := fun hc => hbulk (hc ▸ trivial)
      simp [(hhalf t x).2, Pi.single_apply, hne']

/-- A segment of a line between positions `a` and `b`, in either order. -/
theorem line_seg {wt : PEdge3 T w h → ℝ} {wmax : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) {n : ℕ} (line : ℕ → PVert3 T w h) (hadj : ∀ j, j < n → adj3 (line j) (line (j + 1)))
    {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) : ∃ X : PEdge3 T w h → ZMod 2,
      psyn3 X = Pi.single (line a) 1 + Pi.single (line b) 1 ∧ wsum3 wt X ≤ ((a : ℤ) - b).natAbs * wmax ∧
        ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0 := by
  rcases le_total a b with hab | hab
  · obtain ⟨X, hX, hw, hh⟩ := line_edges hwt hwt0 line hadj a (b - a) (by omega)
    rw [show a + (b - a) = b by omega] at hX
    refine ⟨X, hX, ?_, hh⟩
    have : ((a : ℤ) - b).natAbs = b - a := by omega
    rw [this]
    exact hw
  · obtain ⟨X, hX, hw, hh⟩ := line_edges hwt hwt0 line hadj b (a - b) (by omega)
    rw [show b + (a - b) = a by omega] at hX
    refine ⟨X, by rw [hX, add_comm], ?_, hh⟩
    have : ((a : ℤ) - b).natAbs = a - b := by omega
    rw [this]
    exact hw

/-- **Staircase**: with bulk weights at most `wmax`, two checks are joined by an edge set without half-edges of
weight at most `wmax · |u - v|_1`. -/
theorem exists_stair3 {wt : PEdge3 T w h → ℝ} {wmax : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) (u v : PVert3 T w h) : ∃ X : PEdge3 T w h → ZMod 2,
      psyn3 X = Pi.single u 1 + Pi.single v 1 ∧ wsum3 wt X ≤ (cl1_3 u v : ℝ) * wmax ∧
        ∀ t x, X (.bot t x) = 0 ∧ X (.top t x) = 0 := by
  obtain ⟨ut, ux, uy⟩ := u
  obtain ⟨vt, vx, vy⟩ := v
  obtain ⟨X1, h1, w1, b1⟩ := line_seg hwt hwt0 (tline (T := T) ux uy) (tline_adj ux uy)
    (a := ut.val) (b := vt.val) (by omega) (by omega)
  obtain ⟨X2, h2, w2, b2⟩ := line_seg hwt hwt0 (xline (w := w) vt uy) (xline_adj vt uy)
    (a := ux.val) (b := vx.val) (by omega) (by omega)
  obtain ⟨X3, h3, w3, b3⟩ := line_seg hwt hwt0 (yline (h := h) vt vx) (yline_adj vt vx)
    (a := uy.val) (b := vy.val) (by omega) (by omega)
  have e1 : tline (T := T) ux uy ut.val = (ut, ux, uy) := Prod.ext (Fin.ext (show min ut.val T = ut.val by omega)) rfl
  have e2 : tline (T := T) ux uy vt.val = (vt, ux, uy) := Prod.ext (Fin.ext (show min vt.val T = vt.val by omega)) rfl
  have e3 : xline (w := w) vt uy ux.val = (vt, ux, uy) :=
    Prod.ext rfl (Prod.ext (Fin.ext (show min ux.val w = ux.val by omega)) rfl)
  have e4 : xline (w := w) vt uy vx.val = (vt, vx, uy) :=
    Prod.ext rfl (Prod.ext (Fin.ext (show min vx.val w = vx.val by omega)) rfl)
  have e5 : yline (h := h) vt vx uy.val = (vt, vx, uy) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min uy.val h = uy.val by omega)))
  have e6 : yline (h := h) vt vx vy.val = (vt, vx, vy) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min vy.val h = vy.val by omega)))
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  refine ⟨X1 + X2 + X3, ?_, ?_, fun t x => ⟨?_, ?_⟩⟩
  · rw [psyn3_add, psyn3_add, h1, h2, h3]
    funext z
    simp only [Pi.add_apply]
    linear_combination CharTwo.add_self_eq_zero ((Pi.single ((vt, ux, uy) : PVert3 T w h) 1 :
      PVert3 T w h → ZMod 2) z) + CharTwo.add_self_eq_zero ((Pi.single ((vt, vx, uy) : PVert3 T w h) 1 :
      PVert3 T w h → ZMod 2) z)
  · calc wsum3 wt (X1 + X2 + X3) ≤ wsum3 wt (X1 + X2) + wsum3 wt X3 := wsum3_add_le hwt0 _ _
      _ ≤ wsum3 wt X1 + wsum3 wt X2 + wsum3 wt X3 := by
          have := wsum3_add_le hwt0 X1 X2
          linarith
      _ ≤ _ := by
          simp only [cl1_3, Nat.cast_add]
          linarith
  · simp [(b1 t x).1, (b2 t x).1, (b3 t x).1]
  · simp [(b1 t x).2, (b2 t x).2, (b3 t x).2]

/-- The pair cost of two checks is at most `wmax · |u - v|_1`. -/
theorem pairCost3_le_l1 {wt : PEdge3 T w h → ℝ} {wmax : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) (u v : PVert3 T w h) :
    pairCost3 wt (Pi.single u 1 + Pi.single v 1) ≤ (cl1_3 u v : ℝ) * wmax := by
  obtain ⟨X, hX, hw, _⟩ := exists_stair3 hwt hwt0 u v
  exact (pairCost3_le hX).trans hw

theorem psyn3_single_bot (t : Fin (T + 1)) (x : Fin (w + 1)) :
    psyn3 (Pi.single (PEdge3.bot t x : PEdge3 T w h) 1) = Pi.single (t, x, 0) 1 := by
  rw [psyn3_single]
  funext z
  simp [PEdge3.ends, Pi.single_apply]

theorem psyn3_single_top (t : Fin (T + 1)) (x : Fin (w + 1)) :
    psyn3 (Pi.single (PEdge3.top t x : PEdge3 T w h) 1) = Pi.single (t, x, Fin.last h) 1 := by
  rw [psyn3_single]
  funext z
  simp [PEdge3.ends, Pi.single_apply]

/-- **A leg to the bottom side**: a vertical segment and a bottom half-edge realize a single check. -/
theorem pairCost3_le_bot {wt : PEdge3 T w h → ℝ} {wmax wh : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) (hwh : ∀ e, e.isHalf → wt e ≤ wh) (u : PVert3 T w h) :
    pairCost3 wt (Pi.single u 1) ≤ (u.2.2.val : ℝ) * wmax + wh := by
  obtain ⟨ut, ux, uy⟩ := u
  obtain ⟨X, hX, hw, _⟩ := line_seg hwt hwt0 (yline (h := h) ut ux) (yline_adj ut ux)
    (a := 0) (b := uy.val) (by omega) (by omega)
  have e0 : yline (h := h) ut ux 0 = (ut, ux, 0) := Prod.ext rfl (Prod.ext rfl (Fin.ext (by simp [yline])))
  have e1 : yline (h := h) ut ux uy.val = (ut, ux, uy) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min uy.val h = uy.val by omega)))
  rw [e0, e1] at hX
  have hpsyn : psyn3 (X + Pi.single (PEdge3.bot ut ux) 1) = Pi.single ((ut, ux, uy) : PVert3 T w h) 1 := by
    rw [psyn3_add, hX, psyn3_single_bot]
    funext z
    simp only [Pi.add_apply]
    linear_combination CharTwo.add_self_eq_zero ((Pi.single ((ut, ux, 0) : PVert3 T w h) 1 :
      PVert3 T w h → ZMod 2) z)
  refine (pairCost3_le hpsyn).trans ?_
  calc wsum3 wt (X + Pi.single (PEdge3.bot ut ux) 1) ≤ wsum3 wt X + wsum3 wt (Pi.single (PEdge3.bot ut ux) 1) :=
        wsum3_add_le hwt0 _ _
    _ ≤ (uy.val : ℝ) * wmax + wh := by
        rw [wsum3_single]
        have hb := hwh (PEdge3.bot ut ux) trivial
        have : (((0 : ℕ) : ℤ) - uy.val).natAbs = uy.val := by omega
        rw [this] at hw
        linarith

/-- **A leg to the top side.** -/
theorem pairCost3_le_top {wt : PEdge3 T w h → ℝ} {wmax wh : ℝ} (hwt : ∀ e, ¬ e.isHalf → wt e ≤ wmax)
    (hwt0 : ∀ e, 0 ≤ wt e) (hwh : ∀ e, e.isHalf → wt e ≤ wh) (u : PVert3 T w h) :
    pairCost3 wt (Pi.single u 1) ≤ ((h - u.2.2.val : ℕ) : ℝ) * wmax + wh := by
  obtain ⟨ut, ux, uy⟩ := u
  obtain ⟨X, hX, hw, _⟩ := line_seg hwt hwt0 (yline (h := h) ut ux) (yline_adj ut ux)
    (a := uy.val) (b := h) (by omega) le_rfl
  have e0 : yline (h := h) ut ux uy.val = (ut, ux, uy) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min uy.val h = uy.val by omega)))
  have e1 : yline (h := h) ut ux h = (ut, ux, Fin.last h) := Prod.ext rfl (Prod.ext rfl (Fin.ext (by simp [yline])))
  rw [e0, e1] at hX
  have hpsyn : psyn3 (X + Pi.single (PEdge3.top ut ux) 1) = Pi.single ((ut, ux, uy) : PVert3 T w h) 1 := by
    rw [psyn3_add, hX, psyn3_single_top]
    funext z
    simp only [Pi.add_apply]
    linear_combination CharTwo.add_self_eq_zero ((Pi.single ((ut, ux, Fin.last h) : PVert3 T w h) 1 :
      PVert3 T w h → ZMod 2) z)
  refine (pairCost3_le hpsyn).trans ?_
  calc wsum3 wt (X + Pi.single (PEdge3.top ut ux) 1) ≤ wsum3 wt X + wsum3 wt (Pi.single (PEdge3.top ut ux) 1) :=
        wsum3_add_le hwt0 _ _
    _ ≤ ((h - uy.val : ℕ) : ℝ) * wmax + wh := by
        rw [wsum3_single]
        have hb := hwh (PEdge3.top ut ux) trivial
        have : ((uy.val : ℤ) - h).natAbs = h - uy.val := by omega
        rw [this] at hw
        linarith

end QECD1
