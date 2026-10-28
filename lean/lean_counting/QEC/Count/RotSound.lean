import QEC.Count.RotGeom
import QEC.Count.RDecoder
import QEC.Count.CertSoundS
import Mathlib.Tactic.IntervalCases

/-!
# Soundness of the SAFE exclusions in the rotated code

Let `C` be a failing minimum-weight correction of least `Φ = phiRot c` for the rotated code (as a region code), and
`v0, …, vm` a self-avoiding path of checks with `m < d` edges, labelled by membership in `C`. Then its pattern is not
SAFE-excluded.

Proof plan (as `BoxSound.lean`, with three changes):
1. Of the two witnesses, one has all its points with `U - V` in `[-1, d - 1]` (the smooth range): the first if the
   window's `x - y` range `[lo, hi]` has `hi + 1 ≤ d - 1`, else the second (`hi = d - 1` and `m < d` force `lo ≥ 0`).
2. Its edges are translated by the position of `v0`; an edge with both ends at checks or with one end at a check and the
   other at an outer point is an edge of `rotEdges d` (a lattice neighbour of a check within the smooth range is a
   check or an outer point); an edge with no end at a check is dropped. Dropping keeps the check degrees, can only
   shorten the alternative, and the alternative keeps an even number of edge ends at side-1 outer points (every point
   with `U + V ≤ -1` has even degree in the alternative, by the parity check, since the window's points have
   `U + V ≥ 0`; so an even number of its edges cross between `U + V = -1` and `U + V = 0`).
3. `exchangeR` gives the contradiction: the strict case directly; the tie case either has a dropped edge (strict) or
   none, and then `Φ` is translation-invariant as in the box.
-/

namespace QEC

open Finset QECComp

namespace RotSound

/-! ## Points with two coordinates -/

/-- The position of a check. -/
def posC {d : ℕ} (v : RChk d) : List ℤ := [v.1.1, v.1.2]

theorem posR_chk {d : ℕ} (v : RChk d) : posR (RVx.chk v : RVx (RChk d) (ROut d)) = posC v := rfl

@[simp] theorem length_posC {d : ℕ} (v : RChk d) : (posC v).length = 2 := rfl

theorem l1_two (a b a' b' : ℤ) : l1 [a, b] [a', b'] = (a - a').natAbs + (b - b').natAbs := by
  simp [l1]

/-- A list with two entries is the list of its entries. -/
theorem eq_two {x : List ℤ} (hx : x.length = 2) : x = [x.getD 0 0, x.getD 1 0] := by
  match x, hx with
  | [a, b], _ => rfl

theorem vecOf_two_0 : vecOf 2 0 = [1, 0] := rfl
theorem vecOf_two_1 : vecOf 2 1 = [-1, 0] := rfl
theorem vecOf_two_2 : vecOf 2 2 = [0, 1] := rfl
theorem vecOf_two_3 : vecOf 2 3 = [0, -1] := rfl

theorem vecOf_two_ge {dd : ℕ} (h : 4 ≤ dd) : vecOf 2 dd = [0, 0] := by
  simp only [vecOf, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  constructor
  · rw [if_neg (by omega)]
  · rw [if_neg (by omega)]

/-- Lattice neighbours differ by a unit vector. -/
theorem unit_of_l1 {a b a' b' : ℤ} (h : l1 [a, b] [a', b'] = 1) :
    ∃ dd < 4, [a', b'] = addP [a, b] (vecOf 2 dd) := by
  rw [l1_two] at h
  have h1 := Int.natAbs_eq (a - a')
  have h2 := Int.natAbs_eq (b - b')
  have hc : ((a - a').natAbs = 1 ∧ (b - b').natAbs = 0) ∨ ((a - a').natAbs = 0 ∧ (b - b').natAbs = 1) := by omega
  rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha] at h1
    rw [hb] at h2
    rcases h1 with h1 | h1
    · refine ⟨1, by norm_num, ?_⟩
      rw [vecOf_two_1]
      simp only [addP, List.cons.injEq, and_true]
      push_cast at h1 h2
      constructor <;> omega
    · refine ⟨0, by norm_num, ?_⟩
      rw [vecOf_two_0]
      simp only [addP, List.cons.injEq, and_true]
      push_cast at h1 h2
      constructor <;> omega
  · rw [ha] at h1
    rw [hb] at h2
    rcases h2 with h2 | h2
    · refine ⟨3, by norm_num, ?_⟩
      rw [vecOf_two_3]
      simp only [addP, List.cons.injEq, and_true]
      push_cast at h1 h2
      constructor <;> omega
    · refine ⟨2, by norm_num, ?_⟩
      rw [vecOf_two_2]
      simp only [addP, List.cons.injEq, and_true]
      push_cast at h1 h2
      constructor <;> omega

/-- A unit step has ℓ¹ length `1`. -/
theorem l1_unit {x : List ℤ} (hx : x.length = 2) {dd : ℕ} (hd : dd < 4) : l1 x (addP x (vecOf 2 dd)) = 1 := by
  rw [eq_two hx]
  interval_cases dd
  · rw [vecOf_two_0]; simp [addP, l1]
  · rw [vecOf_two_1]; simp [addP, l1]
  · rw [vecOf_two_2]; simp [addP, l1]
  · rw [vecOf_two_3]; simp [addP, l1]

theorem dirOfR_spec {d : ℕ} {u v : RChk d} (h : l1 (posC u) (posC v) = 1) :
    dirOfR u v < 4 ∧ posC v = addP (posC u) (vecOf 2 (dirOfR u v)) := by
  have h' := unit_of_l1 h
  simp only [dirOfR, dif_pos h']
  exact Classical.choose_spec h'

theorem walkPts_patOfR {d : ℕ} (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (v0 : RChk d) (rest : List (RChk d)), AdjChainR (v0 :: rest) →
      walkPts 2 (posC v0) ((patOfR S (v0 :: rest)).map Prod.fst) = (v0 :: rest).map posC
  | v0, [], _ => by simp [patOfR]
  | v0, v :: rest, h => by
    simp only [patOfR, List.map_cons, walkPts_cons, List.cons.injEq, true_and]
    rw [← (dirOfR_spec h.1).2]
    exact walkPts_patOfR S v rest h.2

theorem edgesFrom_patOfR {d : ℕ} (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ (v0 : RChk d) (rest : List (RChk d)), AdjChainR (v0 :: rest) →
      edgesFrom 2 (posC v0) (patOfR S (v0 :: rest)) =
        (pairs (v0 :: rest)).map
          (fun uv => ((posC uv.1, posC uv.2), decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S)))
  | v0, [], _ => rfl
  | v0, v :: rest, h => by
    simp only [patOfR, edgesFrom, pairs, List.map_cons, List.cons.injEq]
    rw [← (dirOfR_spec h.1).2]
    exact ⟨rfl, edgesFrom_patOfR S v rest h.2⟩

theorem adj_of_mem_pairsR {d : ℕ} : ∀ {ws : List (RChk d)} {u v : RChk d}, AdjChainR ws → (u, v) ∈ pairs ws →
    l1 (posC u) (posC v) = 1
  | [], _, _, _, h => by simp [pairs] at h
  | [_], _, _, _, h => by simp [pairs] at h
  | a :: b :: rest, u, v, hc, h => by
    simp only [pairs, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hc.1
    · exact adj_of_mem_pairsR hc.2 h

theorem ledges_map_chk {d : ℕ} : ∀ ws : List (RChk d),
    ledges (ws.map (RVx.chk (W := ROut d))) = (pairs ws).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2))
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    simp only [List.map_cons, ledges_cons_cons, pairs, List.cons.injEq, true_and]
    exact ledges_map_chk (v :: rest)

/-! ## The `x - y` profile -/

theorem dxy_two (a b : ℤ) : dxy [a, b] = a - b := rfl

theorem dxy_addP {x y : List ℤ} (hx : x.length = 2) (hy : y.length = 2) : dxy (addP x y) = dxy x + dxy y := by
  rw [eq_two hx, eq_two hy]
  simp only [addP, dxy_two]
  ring

theorem dxy_step {o : List ℤ} (ho : o.length = 2) (dd : ℕ) :
    dxy o - 1 ≤ dxy (addP o (vecOf 2 dd)) ∧ dxy (addP o (vecOf 2 dd)) ≤ dxy o + 1 := by
  rw [dxy_addP ho (length_vecOf 2 dd)]
  rcases Nat.lt_or_ge dd 4 with h | h
  · interval_cases dd <;> simp [vecOf_two_0, vecOf_two_1, vecOf_two_2, vecOf_two_3, dxy_two] <;> omega
  · rw [vecOf_two_ge h]; simp [dxy_two]

/-- Two points of a walk differ in `x - y` by at most the number of steps. -/
theorem dxy_walk_span : ∀ (ds : List ℕ) (o : List ℤ), o.length = 2 → ∀ a ∈ walkPts 2 o ds, ∀ b ∈ walkPts 2 o ds,
    dxy a - dxy b ≤ ds.length
  | [], o, _, a, ha, b, hb => by simp at ha hb; subst ha; subst hb; simp
  | dd :: ds, o, ho, a, ha, b, hb => by
    have ho' : (addP o (vecOf 2 dd)).length = 2 := by simp [ho]
    have ih := dxy_walk_span ds (addP o (vecOf 2 dd)) ho'
    have hhead : addP o (vecOf 2 dd) ∈ walkPts 2 (addP o (vecOf 2 dd)) ds := by
      cases ds <;> simp
    have hst := dxy_step ho dd
    simp only [walkPts_cons, List.mem_cons, List.length_cons] at ha hb ⊢
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · simp only [sub_self]; positivity
    · have := ih _ hhead b hb
      push_cast
      linarith
    · have := ih a ha _ hhead
      push_cast
      linarith
    · have := ih a ha b hb
      push_cast
      linarith

/-! ## Folds of `min` and `max` -/

theorem foldl_min_le : ∀ (L : List ℤ) (x0 : ℤ), ∀ y ∈ x0 :: L, L.foldl min x0 ≤ y
  | [], x0, y, hy => by simp at hy; simp [hy]
  | a :: L, x0, y, hy => by
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact le_trans (foldl_min_le L (min y a) _ (List.mem_cons_self)) (min_le_left _ _)
    · exact le_trans (foldl_min_le L (min x0 y) _ (List.mem_cons_self)) (min_le_right _ _)
    · exact foldl_min_le L (min x0 a) y (List.mem_cons_of_mem _ hy)

theorem foldl_min_mem : ∀ (L : List ℤ) (x0 : ℤ), L.foldl min x0 ∈ x0 :: L
  | [], x0 => by simp
  | a :: L, x0 => by
    simp only [List.foldl_cons]
    have := foldl_min_mem L (min x0 a)
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rw [h]
      rcases min_choice x0 a with h' | h' <;> rw [h'] <;> simp
    · exact Or.inr (Or.inr h)

theorem le_foldl_max : ∀ (L : List ℤ) (x0 : ℤ), ∀ y ∈ x0 :: L, y ≤ L.foldl max x0
  | [], x0, y, hy => by simp at hy; simp [hy]
  | a :: L, x0, y, hy => by
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact le_trans (le_max_left _ _) (le_foldl_max L (max y a) _ (List.mem_cons_self))
    · exact le_trans (le_max_right _ _) (le_foldl_max L (max x0 y) _ (List.mem_cons_self))
    · exact le_foldl_max L (max x0 a) y (List.mem_cons_of_mem _ hy)

theorem foldl_max_mem : ∀ (L : List ℤ) (x0 : ℤ), L.foldl max x0 ∈ x0 :: L
  | [], x0 => by simp
  | a :: L, x0 => by
    simp only [List.foldl_cons]
    have := foldl_max_mem L (max x0 a)
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rw [h]
      rcases max_choice x0 a with h' | h' <;> rw [h'] <;> simp
    · exact Or.inr (Or.inr h)

/-! ## Checks and outer points by position -/

/-- The first two entries of a list. -/
def pr (y : List ℤ) : ℤ × ℤ := (y.getD 0 0, y.getD 1 0)

theorem mem_rotChk_iff {d : ℕ} (x : ℤ × ℤ) :
    x ∈ rotChk d ↔ 0 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d - 2 ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1 := by
  simp only [rotChk, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩

theorem mem_rotOut_iff {d : ℕ} (hd : 1 ≤ d) (x : ℤ × ℤ) :
    x ∈ rotOut d ↔ (x.1 + x.2 = -1 ∨ x.1 + x.2 = d - 1) ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1 := by
  simp only [rotOut, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩

/-- The vertex at a position: the check or outer point there, else `dflt`. -/
def toRV {d : ℕ} (dflt : RVx (RChk d) (ROut d)) (y : List ℤ) : RVx (RChk d) (ROut d) :=
  if h : pr y ∈ rotChk d then RVx.chk ⟨pr y, h⟩ else if h' : pr y ∈ rotOut d then RVx.out ⟨pr y, h'⟩ else dflt

/-- A position of a check or an outer point. -/
def IsRP (d : ℕ) (y : List ℤ) : Prop := y.length = 2 ∧ (pr y ∈ rotChk d ∨ pr y ∈ rotOut d)

theorem posR_toRV {d : ℕ} {dflt : RVx (RChk d) (ROut d)} {y : List ℤ} (hy : IsRP d y) : posR (toRV dflt y) = y := by
  obtain ⟨hl, h⟩ := hy
  rw [eq_two hl]
  unfold toRV
  split_ifs with h1 h2
  · rfl
  · rfl
  · exfalso; rcases h with h | h <;> contradiction

theorem toRV_of_chk {d : ℕ} {dflt : RVx (RChk d) (ROut d)} {y : List ℤ} (h : pr y ∈ rotChk d) :
    toRV dflt y = RVx.chk ⟨pr y, h⟩ := by
  unfold toRV; rw [dif_pos h]

theorem pr_posC {d : ℕ} (v : RChk d) : pr (posC v) = v.1 := rfl

theorem pr_eq_of_two {x y : List ℤ} (hx : x.length = 2) (hy : y.length = 2) (h : pr x = pr y) : x = y := by
  rw [eq_two hx, eq_two hy]
  simp only [pr, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- `toRV` is injective on positions of checks and outer points. -/
theorem toRV_inj {d : ℕ} {dflt : RVx (RChk d) (ROut d)} {y y' : List ℤ} (hy : IsRP d y) (hy' : IsRP d y')
    (h : toRV dflt y = toRV dflt y') : y = y' := by
  have := congrArg posR h
  rwa [posR_toRV hy, posR_toRV hy'] at this

/-- The check `v` is at `y` iff `y` is its position (for positions of checks and outer points). -/
theorem toRV_eq_chk {d : ℕ} {dflt : RVx (RChk d) (ROut d)} {y : List ℤ} (hy : IsRP d y) (v : RChk d) :
    toRV dflt y = RVx.chk v ↔ y = posC v := by
  constructor
  · intro h
    have := congrArg posR h
    rwa [posR_toRV hy, posR_chk] at this
  · intro h
    have hc : pr y ∈ rotChk d := by rw [h, pr_posC]; exact v.2
    rw [toRV_of_chk hc]
    congr 1
    apply Subtype.ext
    show pr y = v.1
    rw [h]
    rfl

theorem dxy_eq_pr {y : List ℤ} : dxy y = (pr y).1 - (pr y).2 := rfl

theorem l1_eq_pr {x y : List ℤ} (hx : x.length = 2) (hy : y.length = 2) :
    l1 x y = ((pr x).1 - (pr y).1).natAbs + ((pr x).2 - (pr y).2).natAbs := by
  rw [eq_two hx, eq_two hy, l1_two]
  rfl

theorem l1_translate {o x y : List ℤ} (ho : o.length = 2) (hx : x.length = 2) (hy : y.length = 2) :
    l1 (addP o x) (addP o y) = l1 x y := by
  rw [eq_two ho, eq_two hx, eq_two hy]
  simp only [addP, l1_two]
  congr 2 <;> ring_nf

/-- A lattice neighbour of a check, inside the smooth range, is a check or an outer point. -/
theorem nbr_of_chk {d : ℕ} {y y' : List ℤ} (hyl : y.length = 2) (hy'l : y'.length = 2) (hc : pr y ∈ rotChk d)
    (hl1 : l1 y y' = 1) (h1 : -1 ≤ dxy y') (h2 : dxy y' ≤ d - 1) : IsRP d y' := by
  refine ⟨hy'l, ?_⟩
  rw [l1_eq_pr hyl hy'l] at hl1
  rw [dxy_eq_pr] at h1 h2
  rw [mem_rotChk_iff] at hc
  have hd : 1 ≤ d := by omega
  rw [mem_rotChk_iff, mem_rotOut_iff hd]
  have ha := Int.natAbs_eq ((pr y).1 - (pr y').1)
  have hb := Int.natAbs_eq ((pr y).2 - (pr y').2)
  have hc2 : (((pr y).1 - (pr y').1).natAbs = 1 ∧ ((pr y).2 - (pr y').2).natAbs = 0) ∨
      (((pr y).1 - (pr y').1).natAbs = 0 ∧ ((pr y).2 - (pr y').2).natAbs = 1) := by omega
  rcases hc2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at ha <;> rw [e2] at hb <;> push_cast at ha hb <;> omega

theorem l1_comm {x y : List ℤ} (hx : x.length = 2) (hy : y.length = 2) : l1 x y = l1 y x := by
  rw [l1_eq_pr hx hy, l1_eq_pr hy hx]
  congr 1
  · rw [← Int.natAbs_neg]; ring_nf
  · rw [← Int.natAbs_neg]; ring_nf

/-! ## Transport of relative edges -/

variable {d : ℕ}

/-- Translation by the position of `v0`. -/
def tr (v0 : RChk d) (x : List ℤ) : List ℤ := addP (posC v0) x

theorem length_tr (v0 : RChk d) {x : List ℤ} (hx : x.length = 2) : (tr v0 x).length = 2 := by
  simp [tr, hx]

theorem tr_eq_iff (v0 : RChk d) {x : List ℤ} (hx : x.length = 2) (v : RChk d) :
    tr v0 x = posC v ↔ x = subP (posC v) (posC v0) := by
  constructor
  · intro h
    apply addP_injOn (length_posC v0) hx (by simp [length_subP])
    rw [addP_subP _ _ (by simp)]
    exact h
  · intro h
    rw [tr, h, addP_subP _ _ (by simp)]

/-- The edge of the code of a relative edge. -/
def trE (v0 : RChk d) (e : Edge) : Sym2 (RVx (RChk d) (ROut d)) :=
  s(toRV (RVx.chk v0) (tr v0 e.1), toRV (RVx.chk v0) (tr v0 e.2))

/-- A relative edge is kept when one of its translated ends is a check. -/
def keep (v0 : RChk d) (e : Edge) : Bool :=
  decide (pr (tr v0 e.1) ∈ rotChk d) || decide (pr (tr v0 e.2) ∈ rotChk d)

/-- Unit edges with two coordinates whose translated ends lie in the smooth range. -/
def GoodR (v0 : RChk d) (L : List Edge) : Prop :=
  ∀ e ∈ L, e.1.length = 2 ∧ e.2.length = 2 ∧ l1 e.1 e.2 = 1 ∧
    (-1 ≤ dxy (tr v0 e.1) ∧ dxy (tr v0 e.1) ≤ d - 1) ∧ (-1 ≤ dxy (tr v0 e.2) ∧ dxy (tr v0 e.2) ≤ d - 1)

theorem goodR_sub {v0 : RChk d} {L L' : List Edge} (h : GoodR v0 L) (hs : ∀ e ∈ L', e ∈ L) : GoodR v0 L' :=
  fun e he => h e (hs e he)

/-- The ends of a kept edge are checks or outer points. -/
theorem kept_rp {v0 : RChk d} {e : Edge} (he : GoodR v0 [e]) (hk : keep v0 e = true) :
    IsRP d (tr v0 e.1) ∧ IsRP d (tr v0 e.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he e (by simp)
  have hl1 : (tr v0 e.1).length = 2 := length_tr v0 h1
  have hl2 : (tr v0 e.2).length = 2 := length_tr v0 h2
  have hl : l1 (tr v0 e.1) (tr v0 e.2) = 1 := by
    show l1 (addP (posC v0) e.1) (addP (posC v0) e.2) = 1
    rw [l1_translate (length_posC v0) h1 h2]; exact h3
  simp only [keep, Bool.or_eq_true, decide_eq_true_eq] at hk
  rcases hk with hk | hk
  · exact ⟨⟨hl1, Or.inl hk⟩, nbr_of_chk hl1 hl2 hk hl h5.1 h5.2⟩
  · exact ⟨nbr_of_chk hl2 hl1 hk (by rw [l1_comm hl2 hl1]; exact hl) h4.1 h4.2, ⟨hl2, Or.inl hk⟩⟩

/-- A kept edge is an edge of the rotated code. -/
theorem kept_mem {v0 : RChk d} {e : Edge} (he : GoodR v0 [e]) (hk : keep v0 e = true) :
    trE v0 e ∈ rotEdges d := by
  obtain ⟨r1, r2⟩ := kept_rp he hk
  obtain ⟨h1, h2, h3, -, -⟩ := he e (by simp)
  have hl : l1 (tr v0 e.1) (tr v0 e.2) = 1 := by
    show l1 (addP (posC v0) e.1) (addP (posC v0) e.2) = 1
    rw [l1_translate (length_posC v0) h1 h2]; exact h3
  simp only [rotEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Prod.exists]
  refine ⟨toRV (RVx.chk v0) (tr v0 e.1), toRV (RVx.chk v0) (tr v0 e.2), ?_, rfl⟩
  have hp1 := posR_toRV (dflt := RVx.chk v0) r1
  have hp2 := posR_toRV (dflt := RVx.chk v0) r2
  have hnot : ¬ ((∃ w, toRV (RVx.chk v0) (tr v0 e.1) = RVx.out w) ∧ ∃ w, toRV (RVx.chk v0) (tr v0 e.2) = RVx.out w) := by
    rintro ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩⟩
    simp only [keep, Bool.or_eq_true, decide_eq_true_eq] at hk
    rcases hk with hk | hk
    · rw [toRV_of_chk hk] at hw1; exact absurd hw1 (by simp)
    · rw [toRV_of_chk hk] at hw2; exact absurd hw2 (by simp)
  revert hp1 hp2 hnot
  generalize toRV (RVx.chk v0) (tr v0 e.1) = a
  generalize toRV (RVx.chk v0) (tr v0 e.2) = b
  intro hp1 hp2 hnot
  cases a with
  | chk v =>
    show l1 (posR (RVx.chk v)) (posR b) = 1
    rw [hp1, hp2]; exact hl
  | out w =>
    cases b with
    | chk v' =>
      show l1 (posR (RVx.out w)) (posR (RVx.chk v')) = 1
      rw [hp1, hp2]; exact hl
    | out w' => exact absurd ⟨⟨w, rfl⟩, ⟨w', rfl⟩⟩ hnot

/-- Degrees at checks of the kept, transported edges. -/
theorem rldeg_kept (v0 : RChk d) {L : List Edge} (hL : GoodR v0 L) (v : RChk d) :
    rldeg ((L.filter (keep v0)).map (trE v0)) (RVx.chk v) = degC L (subP (posC v) (posC v0)) := by
  unfold rldeg degC
  rw [List.countP_map, List.countP_filter]
  apply List.countP_congr
  intro e he
  have hg : GoodR v0 [e] := fun f hf => hL f (by simp at hf; subst hf; exact he)
  obtain ⟨h1, h2, -, -, -⟩ := hL e he
  have key : (RVx.chk v ∈ trE v0 e ∧ keep v0 e = true) ↔
      (e.1 = subP (posC v) (posC v0) ∨ e.2 = subP (posC v) (posC v0)) := by
    constructor
    · rintro ⟨hm, hk⟩
      obtain ⟨r1, r2⟩ := kept_rp hg hk
      rw [trE, Sym2.mem_iff] at hm
      rcases hm with hm | hm
      · left; exact (tr_eq_iff v0 h1 v).mp ((toRV_eq_chk r1 v).mp hm.symm)
      · right; exact (tr_eq_iff v0 h2 v).mp ((toRV_eq_chk r2 v).mp hm.symm)
    · rintro (hm | hm)
      · have ht : tr v0 e.1 = posC v := (tr_eq_iff v0 h1 v).mpr hm
        have hc : pr (tr v0 e.1) ∈ rotChk d := by rw [ht, pr_posC]; exact v.2
        refine ⟨?_, by simp [keep, hc]⟩
        rw [trE, Sym2.mem_iff]
        left
        exact ((toRV_eq_chk ⟨length_tr v0 h1, Or.inl hc⟩ v).mpr ht).symm
      · have ht : tr v0 e.2 = posC v := (tr_eq_iff v0 h2 v).mpr hm
        have hc : pr (tr v0 e.2) ∈ rotChk d := by rw [ht, pr_posC]; exact v.2
        refine ⟨?_, by simp [keep, hc]⟩
        rw [trE, Sym2.mem_iff]
        right
        exact ((toRV_eq_chk ⟨length_tr v0 h2, Or.inl hc⟩ v).mpr ht).symm
  simpa [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] using key

/-! ## Side-1 half-edges: crossings of the line `U + V = -1/2` -/

/-- The point is on the side-1 side of the rough line: `U + V ≤ -1`. -/
def FS (y : List ℤ) : Bool := decide ((pr y).1 + (pr y).2 ≤ -1)

/-- The translated edge crosses the line `U + V = -1/2`. -/
def cross (v0 : RChk d) (e : Edge) : Bool := FS (tr v0 e.1) != FS (tr v0 e.2)

theorem fs_chk {y : List ℤ} (h : pr y ∈ rotChk d) : FS y = false := by
  rw [mem_rotChk_iff] at h
  simp only [FS, decide_eq_false_iff_not, not_le]
  omega

/-- The side-1 outer points at the ends of a kept edge: one if it crosses, none otherwise. -/
theorem side1_edge {v0 : RChk d} {e : Edge} (hg : GoodR v0 [e]) (hk : keep v0 e = true) :
    (∑ w ∈ univ.filter (fun w : ROut d => rotSide w = true), if RVx.out w ∈ trE v0 e then 1 else 0) =
      if cross v0 e = true then 1 else 0 := by
  obtain ⟨r1, r2⟩ := kept_rp hg hk
  have hd : 1 ≤ d := by
    have := v0.2
    rw [mem_rotChk_iff] at this
    omega
  -- an end which is not a check is an outer point
  have hout : ∀ {y : List ℤ}, IsRP d y → pr y ∉ rotChk d →
      ∃ h' : pr y ∈ rotOut d, toRV (RVx.chk v0) y = RVx.out ⟨pr y, h'⟩ := by
    intro y hy hc
    have h' : pr y ∈ rotOut d := hy.2.resolve_left hc
    refine ⟨h', ?_⟩
    unfold toRV
    rw [dif_neg hc, dif_pos h']
  have hside : ∀ {y : List ℤ} (h' : pr y ∈ rotOut d), (rotSide (⟨pr y, h'⟩ : ROut d) = true ↔ FS y = true) := by
    intro y h'
    have := h'
    rw [mem_rotOut_iff hd] at this
    simp only [rotSide, FS, decide_eq_true_eq]
    omega
  have hmem : ∀ (w : ROut d), (RVx.out w ∈ trE v0 e ↔
      (toRV (RVx.chk v0) (tr v0 e.1) = RVx.out w ∨ toRV (RVx.chk v0) (tr v0 e.2) = RVx.out w)) := by
    intro w
    rw [trE, Sym2.mem_iff]
    constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm
  by_cases hc1 : pr (tr v0 e.1) ∈ rotChk d <;> by_cases hc2 : pr (tr v0 e.2) ∈ rotChk d
  · -- both ends checks
    rw [Finset.sum_eq_zero]
    · simp [cross, fs_chk hc1, fs_chk hc2]
    · intro w _
      rw [if_neg]
      rw [hmem, toRV_of_chk hc1, toRV_of_chk hc2]
      simp
  · -- the second end is an outer point
    obtain ⟨h', ho⟩ := hout r2 hc2
    have hsum : ∀ w : ROut d, (if RVx.out w ∈ trE v0 e then 1 else 0) =
        if w = ⟨pr (tr v0 e.2), h'⟩ then 1 else 0 := by
      intro w
      have hiff : RVx.out w ∈ trE v0 e ↔ w = ⟨pr (tr v0 e.2), h'⟩ := by
        rw [hmem, toRV_of_chk hc1, ho]
        simp only [reduceCtorEq, false_or, RVx.out.injEq]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      by_cases hw : w = ⟨pr (tr v0 e.2), h'⟩
      · rw [if_pos (hiff.mpr hw), if_pos hw]
      · rw [if_neg (fun h => hw (hiff.mp h)), if_neg hw]
    rw [Finset.sum_congr rfl (fun w _ => hsum w), Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cross, fs_chk hc1]
    by_cases hs : rotSide (⟨pr (tr v0 e.2), h'⟩ : ROut d) = true
    · rw [if_pos hs, if_pos (by simpa using (hside h').mp hs)]
    · rw [if_neg hs, if_neg]
      intro hx
      apply hs
      exact (hside h').mpr (by simpa using hx)
  · -- the first end is an outer point
    obtain ⟨h', ho⟩ := hout r1 hc1
    have hsum : ∀ w : ROut d, (if RVx.out w ∈ trE v0 e then 1 else 0) =
        if w = ⟨pr (tr v0 e.1), h'⟩ then 1 else 0 := by
      intro w
      have hiff : RVx.out w ∈ trE v0 e ↔ w = ⟨pr (tr v0 e.1), h'⟩ := by
        rw [hmem, toRV_of_chk hc2, ho]
        simp only [reduceCtorEq, or_false, RVx.out.injEq]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      by_cases hw : w = ⟨pr (tr v0 e.1), h'⟩
      · rw [if_pos (hiff.mpr hw), if_pos hw]
      · rw [if_neg (fun h => hw (hiff.mp h)), if_neg hw]
    rw [Finset.sum_congr rfl (fun w _ => hsum w), Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cross, fs_chk hc2]
    by_cases hs : rotSide (⟨pr (tr v0 e.1), h'⟩ : ROut d) = true
    · rw [if_pos hs, if_pos (by simpa using (hside h').mp hs)]
    · rw [if_neg hs, if_neg]
      intro hx
      apply hs
      exact (hside h').mpr (by simpa using hx)
  · exfalso
    simp only [keep, Bool.or_eq_true, decide_eq_true_eq] at hk
    rcases hk with hk | hk <;> contradiction

/-- An edge that is not kept does not cross. -/
theorem not_cross_of_not_keep {v0 : RChk d} {e : Edge} (hg : GoodR v0 [e]) (hk : keep v0 e = false) :
    cross v0 e = false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hg e (by simp)
  have hl1 : (tr v0 e.1).length = 2 := length_tr v0 h1
  have hl2 : (tr v0 e.2).length = 2 := length_tr v0 h2
  have hl : l1 (tr v0 e.1) (tr v0 e.2) = 1 := by
    show l1 (addP (posC v0) e.1) (addP (posC v0) e.2) = 1
    rw [l1_translate (length_posC v0) h1 h2]; exact h3
  rw [l1_eq_pr hl1 hl2] at hl
  have hd : 1 ≤ d := by
    have := v0.2
    rw [mem_rotChk_iff] at this
    omega
  have hd2 : 2 ≤ d := by
    have := v0.2
    rw [mem_rotChk_iff] at this
    omega
  simp only [keep, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hk
  rw [mem_rotChk_iff, mem_rotChk_iff] at hk
  simp only [dxy_eq_pr] at h4 h5
  simp only [cross, FS, bne_eq_false_iff_eq, decide_eq_decide]
  have ha := Int.natAbs_eq ((pr (tr v0 e.1)).1 - (pr (tr v0 e.2)).1)
  have hb := Int.natAbs_eq ((pr (tr v0 e.1)).2 - (pr (tr v0 e.2)).2)
  have hc2 : (((pr (tr v0 e.1)).1 - (pr (tr v0 e.2)).1).natAbs = 1 ∧
      ((pr (tr v0 e.1)).2 - (pr (tr v0 e.2)).2).natAbs = 0) ∨
      (((pr (tr v0 e.1)).1 - (pr (tr v0 e.2)).1).natAbs = 0 ∧
      ((pr (tr v0 e.1)).2 - (pr (tr v0 e.2)).2).natAbs = 1) := by omega
  rcases hc2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at ha <;> rw [e2] at hb <;> push_cast at ha hb <;> omega

/-- The side-1 edge ends of the kept, transported edges are the crossings. -/
theorem side1_count (v0 : RChk d) : ∀ (L : List Edge), GoodR v0 L →
    (∑ w ∈ univ.filter (fun w : ROut d => rotSide w = true), rldeg ((L.filter (keep v0)).map (trE v0)) (RVx.out w)) =
      L.countP (cross v0)
  | [], _ => by simp [rldeg]
  | e :: L, hL => by
    have ih := side1_count v0 L (goodR_sub hL (fun f hf => List.mem_cons_of_mem _ hf))
    have hg : GoodR v0 [e] := goodR_sub hL (fun f hf => by simp at hf; subst hf; exact List.mem_cons_self)
    rw [List.countP_cons]
    by_cases hk : keep v0 e = true
    · rw [List.filter_cons_of_pos hk, List.map_cons]
      have hsplit : ∀ w : ROut d, rldeg (trE v0 e :: (L.filter (keep v0)).map (trE v0)) (RVx.out w) =
          rldeg ((L.filter (keep v0)).map (trE v0)) (RVx.out w) + if RVx.out w ∈ trE v0 e then 1 else 0 := by
        intro w
        simp only [rldeg, List.countP_cons, decide_eq_true_eq]
      rw [Finset.sum_congr rfl (fun w _ => hsplit w), Finset.sum_add_distrib, ih, side1_edge hg hk]
    · have hk' : keep v0 e = false := by simpa using hk
      rw [List.filter_cons_of_neg (by simpa using hk), ih, not_cross_of_not_keep hg hk']
      simp

/-! ## Parity of the crossings -/

/-- The number of crossings of an edge list has the parity of the degrees on the crossing side. -/
theorem cross_parity (F : List ℤ → Bool) (D : Finset (List ℤ)) : ∀ (L : List Edge),
    (∀ e ∈ L, e.1 ≠ e.2 ∧ e.1 ∈ D ∧ e.2 ∈ D) →
    (L.countP (fun e => F e.1 != F e.2)) % 2 = (∑ z ∈ D, if F z = true then degC L z else 0) % 2
  | [], _ => by simp [degC]
  | e :: L, h => by
    have ih := cross_parity F D L (fun f hf => h f (List.mem_cons_of_mem _ hf))
    obtain ⟨hne, h1, h2⟩ := h e List.mem_cons_self
    have hdeg : ∀ z, degC (e :: L) z = degC L z + (if e.1 = z then 1 else 0) + (if e.2 = z then 1 else 0) := by
      intro z
      simp only [degC, List.countP_cons, Bool.or_eq_true, beq_iff_eq]
      by_cases ha : e.1 = z <;> by_cases hb : e.2 = z
      · exact absurd (ha.trans hb.symm) hne
      · simp [ha, hb]
      · simp [ha, hb]
      · simp [ha, hb]
    have hsplit : (∑ z ∈ D, if F z = true then degC (e :: L) z else 0) =
        (∑ z ∈ D, if F z = true then degC L z else 0) +
          (∑ z ∈ D, if e.1 = z then (if F e.1 = true then 1 else 0) else 0) +
          (∑ z ∈ D, if e.2 = z then (if F e.2 = true then 1 else 0) else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hdeg]
      by_cases hz : F z = true
      · by_cases ha : e.1 = z <;> by_cases hb : e.2 = z <;> simp_all
      · by_cases ha : e.1 = z <;> by_cases hb : e.2 = z <;> simp_all
    rw [hsplit, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos h1, if_pos h2, List.countP_cons]
    cases hf1 : F e.1 <;> cases hf2 : F e.2 <;> simp <;> omega

/-- An alternative with the degree parities of edges whose ends are all off the side-1 half-plane crosses an even
number of times. -/
theorem crossings_even (v0 : RChk d) {L M : List Edge} (hL : ∀ e ∈ L, e.1 ≠ e.2)
    (hpar : ∀ z, degC L z % 2 = degC M z % 2)
    (hM : ∀ e ∈ M, FS (tr v0 e.1) = false ∧ FS (tr v0 e.2) = false) :
    Even (L.countP (cross v0)) := by
  classical
  set D : Finset (List ℤ) := (L.map Prod.fst ++ L.map Prod.snd).toFinset with hDdef
  have hD : ∀ e ∈ L, e.1 ≠ e.2 ∧ e.1 ∈ D ∧ e.2 ∈ D := by
    intro e he
    refine ⟨hL e he, ?_, ?_⟩
    · rw [hDdef, List.mem_toFinset, List.mem_append]; exact Or.inl (List.mem_map_of_mem he)
    · rw [hDdef, List.mem_toFinset, List.mem_append]; exact Or.inr (List.mem_map_of_mem he)
  have h := cross_parity (fun z => FS (tr v0 z)) D L hD
  have hzero : ∀ z, FS (tr v0 z) = true → degC M z = 0 := by
    intro z hz
    unfold degC
    rw [List.countP_eq_zero]
    intro e he
    simp only [Bool.or_eq_true, beq_iff_eq, not_or]
    obtain ⟨f1, f2⟩ := hM e he
    constructor
    · intro h'; rw [h'] at f1; rw [f1] at hz; exact absurd hz (by simp)
    · intro h'; rw [h'] at f2; rw [f2] at hz; exact absurd hz (by simp)
  rw [Nat.even_iff]
  change (L.countP (fun e => FS (tr v0 e.1) != FS (tr v0 e.2))) % 2 = 0
  rw [h, Finset.sum_nat_mod, Finset.sum_eq_zero]
  · rfl
  · intro z _
    split_ifs with hz
    · rw [hpar z, hzero z hz]; rfl
    · rfl

theorem phi_trE (c : List ℤ) {v0 : RChk d} {e : Edge} (hg : GoodR v0 [e]) (hk : keep v0 e = true) :
    phiRot c (trE v0 e) = phiP c e.1 + phiP c e.2 + 2 * phiP c (posC v0) := by
  obtain ⟨r1, r2⟩ := kept_rp hg hk
  obtain ⟨h1, h2, -⟩ := hg e (by simp)
  simp only [trE, phiRot, Sym2.lift_mk]
  rw [posR_toRV r1, posR_toRV r2]
  simp only [tr]
  rw [phiP_addP _ _ _ (by simp [h1]), phiP_addP _ _ _ (by simp [h2])]
  ring

theorem phi_map_trE (c : List ℤ) (v0 : RChk d) : ∀ {L : List Edge}, GoodR v0 L → (∀ e ∈ L, keep v0 e = true) →
    ((L.map (trE v0)).map (phiRot c)).sum = phiE c L + 2 * L.length * phiP c (posC v0)
  | [], _, _ => by simp [phiE]
  | e :: L, hL, hk => by
    simp only [List.map_cons, List.sum_cons, phiE, List.length_cons]
    rw [phi_trE c (goodR_sub hL (fun f hf => by simp at hf; subst hf; exact List.mem_cons_self))
      (hk e List.mem_cons_self),
      phi_map_trE c v0 (goodR_sub hL (fun f hf => List.mem_cons_of_mem _ hf))
        (fun f hf => hk f (List.mem_cons_of_mem _ hf))]
    push_cast
    ring

theorem trE_inj_same {v0 : RChk d} {e f : Edge} (he : GoodR v0 [e]) (hf : GoodR v0 [f])
    (hke : keep v0 e = true) (hkf : keep v0 f = true) (h : trE v0 e = trE v0 f) : sameE e f = true := by
  obtain ⟨re1, re2⟩ := kept_rp he hke
  obtain ⟨rf1, rf2⟩ := kept_rp hf hkf
  obtain ⟨e1, e2, -⟩ := he e (by simp)
  obtain ⟨f1, f2, -⟩ := hf f (by simp)
  have key : ∀ {a b : List ℤ}, a.length = 2 → b.length = 2 → IsRP d (tr v0 a) → IsRP d (tr v0 b) →
      toRV (RVx.chk v0) (tr v0 a) = toRV (RVx.chk v0) (tr v0 b) → a = b := by
    intro a b ha hb hra hrb hab
    exact addP_injOn (length_posC v0) ha hb (toRV_inj hra hrb hab)
  simp only [trE, Sym2.eq_iff] at h
  simp only [sameE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key e1 f1 re1 rf1 h1, key e2 f2 re2 rf2 h2⟩
  · exact Or.inr ⟨key e1 f2 re1 rf2 h1, key e2 f1 re2 rf1 h2⟩

theorem nodup_map_trE (v0 : RChk d) : ∀ {L : List Edge}, GoodR v0 L → (∀ e ∈ L, keep v0 e = true) →
    nodupE L = true → (L.map (trE v0)).Nodup
  | [], _, _, _ => List.nodup_nil
  | e :: L, hL, hk, h => by
    simp only [nodupE, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_trE v0 (goodR_sub hL (fun f hf => List.mem_cons_of_mem _ hf))
      (fun f hf => hk f (List.mem_cons_of_mem _ hf)) h.2⟩
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hm
    have := trE_inj_same (goodR_sub hL (fun g hg => by simp at hg; subst hg; exact List.mem_cons_self))
      (goodR_sub hL (fun g hg => by simp at hg; subst hg; exact List.mem_cons_of_mem _ hf))
      (hk e List.mem_cons_self) (hk f (List.mem_cons_of_mem _ hf)) hfe.symm
    rw [h.1 f hf] at this
    exact absurd this (by simp)

theorem length_patOfR (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) :
    ∀ vs : List (RChk d), (patOfR S vs).length = vs.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by simp [patOfR, length_patOfR S (v :: rest)]

theorem rp_posC (u : RChk d) : IsRP d (posC u) := ⟨rfl, Or.inl (by rw [pr_posC]; exact u.2)⟩

theorem toRV_posC (dflt : RVx (RChk d) (ROut d)) (u : RChk d) : toRV dflt (posC u) = RVx.chk u :=
  (toRV_eq_chk (rp_posC u) u).mpr rfl

/-- Facts about the position of a check. -/
theorem chk_facts (u : RChk d) :
    -1 ≤ dxy (posC u) ∧ dxy (posC u) ≤ d - 1 ∧ FS (posC u) = false ∧ pr (posC u) ∈ rotChk d := by
  have h := u.2
  have h' := (mem_rotChk_iff u.1).mp h
  refine ⟨?_, ?_, fs_chk (by rw [pr_posC]; exact h), by rw [pr_posC]; exact h⟩
  · rw [dxy_eq_pr, pr_posC]; exact h'.2.2.1
  · rw [dxy_eq_pr, pr_posC]; exact h'.2.2.2

theorem zeros_mem_walkPts (ds : List ℕ) : zeros 2 ∈ walkPts 2 (zeros 2) ds := by
  cases ds <;> simp

theorem ne_of_l1 {x y : List ℤ} (h : l1 x y = 1) : x ≠ y := by
  rintro rfl
  have : l1 x x = 0 := by simp [l1]
  omega

end RotSound

open RotSound

/-- **Soundness of the SAFE exclusions in the rotated code.** -/
theorem rot_not_exclS {d : ℕ} {c : List ℤ} {E C : Finset (Sym2 (RVx (RChk d) (ROut d)))}
    (hC : IsPhiMinFailR (rotEdges d) rotSide (phiRot c) E C) (S : Finset (Sym2 (RVx (RChk d) (ROut d))))
    (v0 : RChk d) (rest : List (RChk d)) (hadj : AdjChainR (v0 :: rest)) (hnd : (v0 :: rest).Nodup)
    (hS : ∀ uv ∈ pairs (v0 :: rest),
      (s(RVx.chk uv.1, RVx.chk uv.2) ∈ S ↔ s(RVx.chk uv.1, RVx.chk uv.2) ∉ C))
    (hlen : rest.length < d) :
    ¬ ExclS 2 c (patOfR S (v0 :: rest)) := by
  classical
  rintro ⟨W1, W2, hW⟩
  set w := patOfR S (v0 :: rest) with hw
  set pts := walkPts 2 (zeros 2) (w.map Prod.fst) with hpts
  have hz : addP (posC v0) (zeros 2) = posC v0 := by
    have := addP_zeros (posC v0); rwa [length_posC] at this
  -- the points of the window, translated, are the checks of the path
  have hwalk : pts.map (tr v0) = (v0 :: rest).map posC := by
    rw [← walkPts_patOfR S v0 rest hadj, ← hw, walkPts_eq_map (length_posC v0), hpts]
    rfl
  have hptsC : ∀ p ∈ pts, p.length = 2 ∧ ∃ u ∈ v0 :: rest, tr v0 p = posC u := by
    intro p hp
    refine ⟨length_of_mem_walkPts (length_zeros 2) hp, ?_⟩
    have : tr v0 p ∈ (v0 :: rest).map posC := by rw [← hwalk]; exact List.mem_map_of_mem hp
    obtain ⟨u, hu, hpu⟩ := List.mem_map.mp this
    exact ⟨u, hu, hpu.symm⟩
  -- the window edges
  have hE1 : edgesFrom 2 (posC v0) w =
      (edgesFrom 2 (zeros 2) w).map (fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2)) := by
    have := edgesFrom_translate (o := posC v0) (o' := zeros 2) (length_posC v0) (length_zeros 2) w
    rw [hz] at this
    exact this
  have hwinE : ∀ e ∈ edgesFrom 2 (zeros 2) w, ∃ uv ∈ pairs (v0 :: rest), tr v0 e.1.1 = posC uv.1 ∧
      tr v0 e.1.2 = posC uv.2 ∧ e.2 = decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S) := by
    intro e he
    have hm : ((tr v0 e.1.1, tr v0 e.1.2), e.2) ∈ edgesFrom 2 (posC v0) w := by
      rw [hE1]; exact List.mem_map_of_mem (f := fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2)) he
    rw [hw, edgesFrom_patOfR S v0 rest hadj, List.mem_map] at hm
    obtain ⟨uv, huv, heq⟩ := hm
    simp only [Prod.mk.injEq] at heq
    exact ⟨uv, huv, heq.1.1.symm, heq.1.2.symm, heq.2.symm⟩
  -- the range of `x - y` over the window
  have hds : winRange 2 w = ((pts.map dxy).foldl min 0, (pts.map dxy).foldl max 0) := rfl
  have hlo_le : ∀ p ∈ pts, (winRange 2 w).1 ≤ dxy p := fun p hp => by
    rw [hds]; exact foldl_min_le _ 0 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hp))
  have hle_hi : ∀ p ∈ pts, dxy p ≤ (winRange 2 w).2 := fun p hp => by
    rw [hds]; exact le_foldl_max _ 0 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hp))
  have hz0 : zeros 2 ∈ pts := zeros_mem_walkPts _
  have hlo_att : ∃ p ∈ pts, dxy p = (winRange 2 w).1 := by
    have := foldl_min_mem (pts.map dxy) 0
    rw [List.mem_cons] at this
    rcases this with h | h
    · exact ⟨zeros 2, hz0, by rw [hds, h]; rfl⟩
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
      exact ⟨p, hp, by rw [hds, hpe]⟩
  have hhi_att : ∃ p ∈ pts, dxy p = (winRange 2 w).2 := by
    have := foldl_max_mem (pts.map dxy) 0
    rw [List.mem_cons] at this
    rcases this with h | h
    · exact ⟨zeros 2, hz0, by rw [hds, h]; rfl⟩
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
      exact ⟨p, hp, by rw [hds, hpe]⟩
  -- absolute `x - y` of the window points
  have habs : ∀ p ∈ pts, dxy (tr v0 p) = dxy (posC v0) + dxy p ∧ -1 ≤ dxy (tr v0 p) ∧ dxy (tr v0 p) ≤ d - 1 := by
    intro p hp
    obtain ⟨hl, u, -, hu⟩ := hptsC p hp
    refine ⟨dxy_addP (length_posC v0) hl, ?_, ?_⟩
    · rw [hu]; exact (chk_facts u).1
    · rw [hu]; exact (chk_facts u).2.1
  have hwlen : (w.map Prod.fst).length = rest.length := by
    rw [List.length_map, hw, length_patOfR]; simp
  -- one of the two witnesses lies inside the smooth range
  unfold checkWS at hW
  simp only [Bool.and_eq_true] at hW
  obtain ⟨⟨⟨hc1, hc2⟩, hp1⟩, hp2⟩ := hW
  have hchoose : ∃ W : Wit, checkW 2 c w W = true ∧ ∀ e ∈ altEdges 2 W.alt,
      (-1 ≤ dxy (tr v0 e.1) ∧ dxy (tr v0 e.1) ≤ d - 1) ∧ (-1 ≤ dxy (tr v0 e.2) ∧ dxy (tr v0 e.2) ≤ d - 1) := by
    obtain ⟨plo, hplo, hplo'⟩ := hlo_att
    obtain ⟨phi, hphi, hphi'⟩ := hhi_att
    obtain ⟨-, hlo1, -⟩ := habs plo hplo
    obtain ⟨-, -, hhi1⟩ := habs phi hphi
    rw [(habs plo hplo).1, hplo'] at hlo1
    rw [(habs phi hphi).1, hphi'] at hhi1
    have hspan := dxy_walk_span (w.map Prod.fst) (zeros 2) (length_zeros 2) phi hphi plo hplo
    rw [hwlen, hphi', hplo'] at hspan
    -- the lengths of the alternative's points
    have hlen2 : ∀ (W : Wit), checkW 2 c w W = true → ∀ e ∈ altEdges 2 W.alt, e.1.length = 2 ∧ e.2.length = 2 := by
      intro W hW e he
      simp only [checkW, Bool.and_eq_true, List.all_eq_true] at hW
      simp only [altEdges, List.mem_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      have h3 := hW.1.1 a ha
      simp only [Bool.and_eq_true, inBB, beq_iff_eq] at h3
      exact ⟨h3.1.2.1, h3.2.1⟩
    by_cases hcase : dxy (posC v0) + (winRange 2 w).2 + 1 ≤ d - 1
    · refine ⟨W1, hc1, fun e he => ?_⟩
      simp only [profOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hp1 e he
      obtain ⟨l1e, l2e⟩ := hlen2 W1 hc1 e he
      rw [show tr v0 e.1 = addP (posC v0) e.1 from rfl, show tr v0 e.2 = addP (posC v0) e.2 from rfl,
        dxy_addP (length_posC v0) l1e, dxy_addP (length_posC v0) l2e]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · refine ⟨W2, hc2, fun e he => ?_⟩
      simp only [profOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp2
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hp2 e he
      obtain ⟨l1e, l2e⟩ := hlen2 W2 hc2 e he
      rw [show tr v0 e.1 = addP (posC v0) e.1 from rfl, show tr v0 e.2 = addP (posC v0) e.2 from rfl,
        dxy_addP (length_posC v0) l1e, dxy_addP (length_posC v0) l2e]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  obtain ⟨W, hcW, hprof⟩ := hchoose
  -- unpack the chosen witness
  simp only [checkW, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcW
  obtain ⟨⟨halt, hpar⟩, hsz⟩ := hcW
  set X := cEdges 2 w with hX
  set Y := if W.useE then eEdges 2 w else [] with hY
  set P := altEdges 2 W.alt with hP
  have hXmem : ∀ e ∈ X, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = true ∧ e'.1 = e := by
    intro e he
    simp only [hX, cEdges, List.mem_map, List.mem_filter] at he
    obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
    exact ⟨e', he', hl, rfl⟩
  have hYmem : ∀ e ∈ Y, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.2 = false ∧ e'.1 = e := by
    intro e he
    rw [hY] at he
    split_ifs at he
    · simp only [eEdges, List.mem_map, List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨e', ⟨he', hl⟩, rfl⟩ := he
      exact ⟨e', he', hl, rfl⟩
    · simp at he
  -- facts about a window edge
  have hwin : ∀ e' ∈ edgesFrom 2 (zeros 2) w, GoodR v0 [e'.1] ∧ keep v0 e'.1 = true ∧
      FS (tr v0 e'.1.1) = false ∧ FS (tr v0 e'.1.2) = false ∧
      ∃ uv ∈ pairs (v0 :: rest), trE v0 e'.1 = s(RVx.chk uv.1, RVx.chk uv.2) ∧
        e'.2 = decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S) := by
    intro e' he'
    obtain ⟨uv, huv, h1, h2, h3⟩ := hwinE e' he'
    have hpe := mem_edgesFrom_pts 2 (zeros 2) w e' he'
    have l1a : e'.1.1.length = 2 := length_of_mem_walkPts (length_zeros 2) hpe.1
    have l1b : e'.1.2.length = 2 := length_of_mem_walkPts (length_zeros 2) hpe.2
    have hadj1 := adj_of_mem_pairsR hadj huv
    refine ⟨?_, ?_, by rw [h1]; exact (chk_facts uv.1).2.2.1, by rw [h2]; exact (chk_facts uv.2).2.2.1,
      uv, huv, ?_, h3⟩
    · intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      refine ⟨l1a, l1b, ?_, ?_, ?_⟩
      · have : l1 (tr v0 e'.1.1) (tr v0 e'.1.2) = l1 e'.1.1 e'.1.2 := l1_translate (length_posC v0) l1a l1b
        rw [← this, h1, h2]; exact hadj1
      · rw [h1]; exact ⟨(chk_facts uv.1).1, (chk_facts uv.1).2.1⟩
      · rw [h2]; exact ⟨(chk_facts uv.2).1, (chk_facts uv.2).2.1⟩
    · simp only [keep, Bool.or_eq_true, decide_eq_true_eq]
      left; rw [h1]; exact (chk_facts uv.1).2.2.2
    · simp only [trE]; rw [h1, h2, toRV_posC, toRV_posC]
  have hwinXY : ∀ e ∈ X ++ Y, ∃ e' ∈ edgesFrom 2 (zeros 2) w, e'.1 = e := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · obtain ⟨e', he', -, rfl⟩ := hXmem e h; exact ⟨e', he', rfl⟩
    · obtain ⟨e', he', -, rfl⟩ := hYmem e h; exact ⟨e', he', rfl⟩
  have hgoodXY : GoodR v0 (X ++ Y) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact (hwin e' he').1 _ (by simp)
  have hkeepXY : ∀ e ∈ X ++ Y, keep v0 e = true := by
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact (hwin e' he').2.1
  have hgoodP : GoodR v0 P := by
    intro e he
    simp only [hP, altEdges, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨⟨hd4, hb1⟩, -⟩ := halt a ha
    have la : a.1.length = 2 := by
      simp only [inBB, Bool.and_eq_true, beq_iff_eq] at hb1; exact hb1.1
    have hprof' := hprof (a.1, addP a.1 (vecOf 2 a.2)) (by
      rw [hP]; simp only [altEdges, List.mem_map]; exact ⟨a, ha, rfl⟩)
    exact ⟨la, by simp [la], l1_unit la (by omega), hprof'.1, hprof'.2⟩
  -- the window edges are distinct
  have hE0 : (edgesFrom 2 (zeros 2) w).map (fun e => trE v0 e.1) =
      (pairs (v0 :: rest)).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2)) := by
    calc (edgesFrom 2 (zeros 2) w).map (fun e => trE v0 e.1)
        = ((edgesFrom 2 (zeros 2) w).map (fun e => ((tr v0 e.1.1, tr v0 e.1.2), e.2))).map
            (fun e : Edge × Bool => s(toRV (RVx.chk v0) e.1.1, toRV (RVx.chk v0) e.1.2)) := by
          rw [List.map_map]; rfl
      _ = ((pairs (v0 :: rest)).map
            (fun uv => ((posC uv.1, posC uv.2), decide (s(RVx.chk uv.1, RVx.chk uv.2) ∉ S)))).map
            (fun e : Edge × Bool => s(toRV (RVx.chk v0) e.1.1, toRV (RVx.chk v0) e.1.2)) := by
          rw [← hE1, hw, edgesFrom_patOfR S v0 rest hadj]
      _ = (pairs (v0 :: rest)).map (fun uv => s(RVx.chk uv.1, RVx.chk uv.2)) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro uv _
          simp [toRV_posC]
  have hall : ((cEdges 2 w ++ eEdges 2 w).map (trE v0)).Nodup := by
    have hperm : (cEdges 2 w ++ eEdges 2 w).Perm ((edgesFrom 2 (zeros 2) w).map Prod.fst) := by
      unfold cEdges eEdges
      rw [← List.map_append]
      exact (List.filter_append_perm _ _).map _
    have hl : ((edgesFrom 2 (zeros 2) w).map Prod.fst).map (trE v0) =
        ledges ((v0 :: rest).map (RVx.chk (W := ROut d))) := by
      rw [ledges_map_chk, List.map_map]
      exact hE0
    rw [(hperm.map _).nodup_iff, hl]
    exact ledges_nodup (hnd.map (fun _ _ h => RVx.chk.inj h))
  have hXYnd : (X.map (trE v0) ++ Y.map (trE v0)).Nodup := by
    rw [hY]
    split_ifs
    · rw [← List.map_append]; exact hall
    · rw [List.map_nil, List.append_nil, ← List.append_nil (X.map (trE v0))]
      rw [List.map_append] at hall
      exact (List.nodup_append.mp hall).1.append List.nodup_nil (by simp)
  have hXC : ∀ e ∈ X.map (trE v0), e ∈ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hXmem f hf
    obtain ⟨-, -, -, -, uv, huv, ht, hlab⟩ := hwin e' he'
    rw [ht]
    rw [hl] at hlab
    have hnS : s(RVx.chk uv.1, RVx.chk uv.2) ∉ S := by simpa using hlab.symm
    by_contra hc
    exact hnS ((hS uv huv).mpr hc)
  have hYC : ∀ e ∈ Y.map (trE v0), e ∉ C := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', hl, rfl⟩ := hYmem f hf
    obtain ⟨-, -, -, -, uv, huv, ht, hlab⟩ := hwin e' he'
    rw [ht]
    rw [hl] at hlab
    have hS' : s(RVx.chk uv.1, RVx.chk uv.2) ∈ S := by simpa using hlab.symm
    exact (hS uv huv).mp hS'
  have hg : ∀ e ∈ X.map (trE v0) ++ Y.map (trE v0) ++ (P.filter (keep v0)).map (trE v0), e ∈ rotEdges d := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · rw [← List.map_append] at h
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      exact kept_mem (goodR_sub hgoodXY (fun g hg => by simp at hg; subst hg; exact hf)) (hkeepXY f hf)
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
      rw [List.mem_filter] at hf
      exact kept_mem (goodR_sub hgoodP (fun g hg => by simp at hg; subst hg; exact hf.1)) hf.2
  have hXYout : ∀ e ∈ X.map (trE v0) ++ Y.map (trE v0), ∀ w' : ROut d, RVx.out w' ∉ e := by
    intro e he w'
    rw [← List.map_append] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    obtain ⟨e', he', rfl⟩ := hwinXY f hf
    obtain ⟨-, -, -, -, uv, -, ht, -⟩ := hwin e' he'
    rw [ht]
    simp [Sym2.mem_iff]
  have hpar' : Even (∑ w' ∈ univ.filter (fun w' : ROut d => rotSide w' = true),
      rldeg ((P.filter (keep v0)).map (trE v0)) (RVx.out w')) := by
    rw [side1_count v0 P hgoodP]
    refine crossings_even v0 (fun e he => ne_of_l1 (hgoodP e he).2.2.1) (parOK_spec hpar) ?_
    intro e he
    obtain ⟨e', he', rfl⟩ := hwinXY e he
    exact ⟨(hwin e' he').2.2.1, (hwin e' he').2.2.2.1⟩
  have hXYkeep : (X ++ Y).filter (keep v0) = X ++ Y := List.filter_eq_self.mpr hkeepXY
  have hodd : roddD ((P.filter (keep v0)).map (trE v0)) = roddD (X.map (trE v0) ++ Y.map (trE v0)) := by
    ext v
    simp only [roddD, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← List.map_append, ← hXYkeep, rldeg_kept v0 hgoodP v, rldeg_kept v0 hgoodXY v, Nat.odd_iff,
      Nat.odd_iff, parOK_spec hpar]
  have hex := exchangeR hC hXYnd hXC hYC hg hXYout hpar' hodd
  simp only [List.length_map] at hex
  have hPlen : (P.filter (keep v0)).length ≤ P.length := List.length_filter_le _ _
  rcases hsz with hlt | ⟨⟨heq, hnodup⟩, hphi⟩
  · exact absurd hex.1 (by omega)
  · by_cases hallk : (P.filter (keep v0)).length = P.length
    · have hkP : ∀ e ∈ P, keep v0 e = true := List.length_filter_eq_length_iff.mp hallk
      have hPf : P.filter (keep v0) = P := List.filter_eq_self.mpr hkP
      rw [hPf] at hex
      have h2 := hex.2 heq.symm (nodup_map_trE v0 hgoodP hkP hnodup)
      rw [phi_map_trE c v0 (goodR_sub hgoodXY (fun e he => List.mem_append_left _ he))
          (fun e he => hkeepXY e (List.mem_append_left _ he)),
        phi_map_trE c v0 (goodR_sub hgoodXY (fun e he => List.mem_append_right _ he))
          (fun e he => hkeepXY e (List.mem_append_right _ he)),
        phi_map_trE c v0 hgoodP hkP] at h2
      have hlen' : (X.length : ℤ) = Y.length + P.length := by exact_mod_cast heq.symm
      have hmul : 2 * (X.length : ℤ) * phiP c (posC v0) =
          2 * (Y.length : ℤ) * phiP c (posC v0) + 2 * (P.length : ℤ) * phiP c (posC v0) := by
        rw [hlen']; ring
      linarith
    · exact absurd hex.1 (by omega)

end QEC
