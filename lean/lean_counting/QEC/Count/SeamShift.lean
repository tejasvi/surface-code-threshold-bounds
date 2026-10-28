import QEC.Count.TorDefs
import QEC.Count.CertSound
import QEC.Count.BoxSound

/-!
# Seam offsets, and the translation lemma for the seam witness check

* `qoffZ_cases`: the seam offset of `b` is `b`, `b - L` or `b + L` (for `-3L ≤ 2b < 3L`), with the ranges.
* `offAt_nxtT`: along a walk from a renormalized offset `o`, the offset of the `i`-th vertex is
  `qoffZ L (o + xdisp (w.take i))`.
* `checkWT_shift`: if the walk of a window lies on one side of the seam both at offset `o` and at offset `o'`
  (`OneSide`), then `checkWT L0 o w W = checkWT L0 o' w W`: the alternative lies in the bounding box of the window,
  so all its points are on that side too, and in the tie case (equal edge counts) the `L`-parts of the two sides of
  the comparison agree and the difference of the other parts does not depend on the offset.
* `oneSide_of_ref`: a window whose points lie within `E` (in `x`) of a reference point whose seam offset is at
  least `E` away from the seam lies on one side of the seam.
-/

namespace QEC

open Finset QECComp

namespace SeamShift

/-! ## Seam offsets -/

theorem qoffZ_congr {L : ℕ} {a b : ℤ} (h : a % (L : ℤ) = b % (L : ℤ)) : qoffZ L a = qoffZ L b := by
  unfold qoffZ
  rw [h]

theorem qoffZ_emod {L : ℕ} (a : ℤ) : qoffZ L a % (L : ℤ) = a % (L : ℤ) := by
  unfold qoffZ
  split_ifs
  · exact Int.emod_emod_of_dvd a (dvd_refl _)
  · rw [Int.sub_emod, Int.emod_emod_of_dvd a (dvd_refl _), Int.emod_self, sub_zero,
      Int.emod_emod_of_dvd a (dvd_refl _)]

theorem qoffZ_idem {L : ℕ} (a : ℤ) : qoffZ L (qoffZ L a) = qoffZ L a :=
  qoffZ_congr (qoffZ_emod a)

theorem qoffZ_add {L : ℕ} (a c : ℤ) : qoffZ L (qoffZ L a + c) = qoffZ L (a + c) := by
  apply qoffZ_congr
  rw [Int.add_emod, qoffZ_emod, ← Int.add_emod]

theorem qoffZ_of_bounds {L : ℕ} (hL : 0 < L) {q : ℤ} (h1 : -(L : ℤ) ≤ 2 * q) (h2 : 2 * q < L) : qoffZ L q = q := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  unfold qoffZ
  rcases le_or_gt 0 q with hq | hq
  · have hm : q % (L : ℤ) = q := Int.emod_eq_of_lt hq (by omega)
    rw [hm, if_pos h2]
  · have hm : q % (L : ℤ) = q + L := by
      rw [← Int.add_emod_right q (L : ℤ)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm, if_neg (by omega)]
    ring

theorem qoffZ_bounds {L : ℕ} (hL : 0 < L) (a : ℤ) : -(L : ℤ) ≤ 2 * qoffZ L a ∧ 2 * qoffZ L a < L := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h0 : 0 ≤ a % (L : ℤ) := Int.emod_nonneg a (by omega)
  have h1 : a % (L : ℤ) < L := Int.emod_lt_of_pos a hL'
  unfold qoffZ
  split_ifs with h <;> omega

theorem qoffZ_sub_L {L : ℕ} (b : ℤ) : qoffZ L (b - L) = qoffZ L b := by
  apply qoffZ_congr
  rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd b (dvd_refl _)]

theorem qoffZ_add_L {L : ℕ} (b : ℤ) : qoffZ L (b + L) = qoffZ L b := by
  apply qoffZ_congr
  rw [Int.add_emod_right]

/-- The three cases of a seam offset. -/
theorem qoffZ_cases {L : ℕ} (hL : 0 < L) {b : ℤ} (h1 : -3 * (L : ℤ) ≤ 2 * b) (h2 : 2 * b < 3 * L) :
    (-(L : ℤ) ≤ 2 * b ∧ 2 * b < L ∧ qoffZ L b = b) ∨ ((L : ℤ) ≤ 2 * b ∧ qoffZ L b = b - L) ∨
      (2 * b < -(L : ℤ) ∧ qoffZ L b = b + L) := by
  rcases lt_or_ge (2 * b) (-(L : ℤ)) with ha | ha
  · right; right
    refine ⟨ha, ?_⟩
    rw [← qoffZ_add_L b]
    exact qoffZ_of_bounds hL (by omega) (by omega)
  · rcases lt_or_ge (2 * b) (L : ℤ) with hb | hb
    · left
      exact ⟨ha, hb, qoffZ_of_bounds hL ha hb⟩
    · right; left
      refine ⟨hb, ?_⟩
      rw [← qoffZ_sub_L b]
      exact qoffZ_of_bounds hL (by omega) (by omega)

/-! ## x-displacements -/

theorem foldl_add_map {α : Type*} (f : α → ℤ) : ∀ (w : List α) (a : ℤ),
    w.foldl (fun s x => s + f x) a = a + (w.map f).sum
  | [], a => by simp
  | x :: w, a => by
    simp only [List.foldl, List.map_cons, List.sum_cons]
    rw [foldl_add_map f w]
    ring

theorem dx_eq (x : ℕ × Bool) : (if x.1 == 0 then (1 : ℤ) else if x.1 == 1 then -1 else 0) = dxOf x.1 := by
  simp only [dxOf, beq_iff_eq]

theorem xdisp_eq (w : List (ℕ × Bool)) : xdisp w = ((w.map Prod.fst).map dxOf).sum := by
  unfold xdisp
  rw [foldl_add_map, zero_add, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  exact dx_eq x

@[simp] theorem xdisp_nil : xdisp [] = 0 := by simp [xdisp_eq]

theorem xdisp_append (a b : List (ℕ × Bool)) : xdisp (a ++ b) = xdisp a + xdisp b := by
  simp [xdisp_eq, List.sum_append]

theorem xdisp_single (x : ℕ × Bool) : xdisp [x] = dxOf x.1 := by simp [xdisp_eq]

theorem xdisp_cons (x : ℕ × Bool) (w : List (ℕ × Bool)) : xdisp (x :: w) = dxOf x.1 + xdisp w := by
  simp [xdisp_eq]

theorem dxOf_bounds (d : ℕ) : -1 ≤ dxOf d ∧ dxOf d ≤ 1 := by
  unfold dxOf
  split_ifs <;> omega

theorem xdisp_bounds : ∀ w : List (ℕ × Bool), -(w.length : ℤ) ≤ xdisp w ∧ xdisp w ≤ w.length
  | [] => by simp
  | x :: w => by
    rw [xdisp_cons, List.length_cons]
    have := xdisp_bounds w
    have := dxOf_bounds x.1
    push_cast
    omega

/-- `xdisp` of prefixes is 1-Lipschitz in the prefix length. -/
theorem xdisp_take_sub (w : List (ℕ × Bool)) {k i : ℕ} (hki : k ≤ i) :
    -((i - k : ℕ) : ℤ) ≤ xdisp (w.take i) - xdisp (w.take k) ∧
      xdisp (w.take i) - xdisp (w.take k) ≤ ((i - k : ℕ) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
  rw [List.take_add, xdisp_append, Nat.add_sub_cancel_left]
  have h := xdisp_bounds ((w.drop k).take j)
  have hl : ((w.drop k).take j).length ≤ j := List.length_take_le _ _
  have hl' : (((w.drop k).take j).length : ℤ) ≤ j := by exact_mod_cast hl
  constructor <;> omega

theorem xdisp_take_bounds (w : List (ℕ × Bool)) (i : ℕ) :
    -(i : ℤ) ≤ xdisp (w.take i) ∧ xdisp (w.take i) ≤ i := by
  have h := xdisp_take_sub w (Nat.zero_le i)
  simp only [List.take_zero, xdisp_nil, sub_zero, Nat.sub_zero] at h
  exact h

/-! ## Offsets along a walk -/

theorem foldl_nxtT {L : ℕ} : ∀ (ds : List ℕ) (o : ℤ), qoffZ L o = o →
    ds.foldl (nxtT L) o = qoffZ L (o + (ds.map dxOf).sum)
  | [], o, ho => by simp [ho]
  | d :: ds, o, _ => by
    simp only [List.foldl, List.map_cons, List.sum_cons]
    rw [foldl_nxtT ds (nxtT L o d) (qoffZ_idem _)]
    unfold nxtT
    rw [qoffZ_add, add_assoc]

/-- The offset of the `i`-th vertex of a walk from a renormalized offset. -/
theorem offAt_nxtT {L : ℕ} {o : ℤ} (ho : qoffZ L o = o) (w : List (ℕ × Bool)) (i : ℕ) :
    offAt (nxtT L) o w i = qoffZ L (o + xdisp (w.take i)) := by
  unfold offAt
  rw [foldl_nxtT _ o ho, xdisp_eq]

/-! ## The x-coordinates of the points of a walk -/

theorem vecOf_two_getD0 (d : ℕ) : (vecOf 2 d).getD 0 0 = dxOf d := by
  rw [getD_vecOf 2 d 0 (by norm_num)]
  match d with
  | 0 => simp [dxOf]
  | 1 => simp [dxOf]
  | d + 2 =>
    have h0 : ¬ (0 = (d + 2) / 2) := by omega
    simp only [h0, ite_false, dxOf, show d + 2 ≠ 0 by omega, show d + 2 ≠ 1 by omega]

theorem walkPts_x : ∀ (ds : List ℕ) (o : List ℤ), o.length = 2 → ∀ p ∈ walkPts 2 o ds,
    ∃ i ≤ ds.length, p.getD 0 0 = o.getD 0 0 + ((ds.take i).map dxOf).sum
  | [], o, _, p, hp => by
    simp only [walkPts_nil, List.mem_singleton] at hp
    exact ⟨0, le_rfl, by simp [hp]⟩
  | d :: ds, o, ho, p, hp => by
    simp only [walkPts_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · have ho' : (addP o (vecOf 2 d)).length = 2 := by simp [ho]
      obtain ⟨i, hi, hpi⟩ := walkPts_x ds _ ho' p hp
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [hpi, getD_addP _ _ 0 (by omega) (by simp), vecOf_two_getD0]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      ring

/-- The x-coordinate of a point of the walk of a pattern is the displacement of a prefix. -/
theorem walkPts_x_pat {w : List (ℕ × Bool)} {p : List ℤ} (hp : p ∈ walkPts 2 (zeros 2) (w.map Prod.fst)) :
    ∃ i ≤ w.length, p.getD 0 0 = xdisp (w.take i) := by
  obtain ⟨i, hi, hpi⟩ := walkPts_x _ _ (by simp) p hp
  refine ⟨i, by simpa using hi, ?_⟩
  rw [hpi, xdisp_eq, List.map_take]
  simp [zeros]

/-! ## `Φ` on one side of the seam -/

/-- The sum of the x-coordinates of the ends of the edges. -/
def sxE (L : List Edge) : ℤ := (L.map (fun e => e.1.getD 0 0 + e.2.getD 0 0)).sum

/-- On one side of the seam (`lft`: the left side), `Φ` of an edge list is `(2|L|, …)` or `(0, …)`. -/
theorem phiTE_side {o : ℤ} {lft : Bool} : ∀ {L : List Edge},
    (∀ e ∈ L, (o + e.1.getD 0 0 < 0 ↔ lft = true) ∧ (o + e.2.getD 0 0 < 0 ↔ lft = true)) →
    phiTE o L = ((2 : ℤ) * (if lft then 1 else 0) * L.length, 2 * o * L.length + sxE L)
  | [], _ => by simp [phiTE, sxE]
  | e :: L, h => by
    have ih := phiTE_side (L := L) (fun f hf => h f (List.mem_cons_of_mem _ hf))
    have he := h e List.mem_cons_self
    simp only [phiTE, ih, addPair, phiT, sxE, List.map_cons, List.sum_cons, List.length_cons]
    unfold sxE at ih
    cases lft
    · have h1 : ¬ (o + e.1.getD 0 0 < 0) := fun hc => by simpa using he.1.mp hc
      have h2 : ¬ (o + e.2.getD 0 0 < 0) := fun hc => by simpa using he.2.mp hc
      simp only [h1, h2, ite_false, Bool.false_eq_true]
      ext <;> push_cast <;> ring
    · have h1 : o + e.1.getD 0 0 < 0 := he.1.mpr rfl
      have h2 : o + e.2.getD 0 0 < 0 := he.2.mpr rfl
      simp only [h1, h2, ite_true]
      ext <;> push_cast <;> ring

/-- The comparison of the tie case, on one side of the seam. -/
theorem lexLt_side {o c : ℤ} {X Y P : List Edge}
    (hX : phiTE o X = (2 * c * X.length, 2 * o * X.length + sxE X))
    (hY : phiTE o Y = (2 * c * Y.length, 2 * o * Y.length + sxE Y))
    (hP : phiTE o P = (2 * c * P.length, 2 * o * P.length + sxE P))
    (hD : Y.length + P.length = X.length) :
    lexLt (addPair (phiTE o Y) (phiTE o P)) (phiTE o X) = decide (sxE Y + sxE P < sxE X) ∧
      ((phiTE o X).2 - (addPair (phiTE o Y) (phiTE o P)).2).natAbs = (sxE X - sxE Y - sxE P).natAbs := by
  have hD' : (Y.length : ℤ) + P.length = X.length := by exact_mod_cast hD
  have e1 : 2 * c * (Y.length : ℤ) + 2 * c * P.length = 2 * c * X.length := by rw [← hD']; ring
  have e2 : 2 * o * (Y.length : ℤ) + 2 * o * P.length = 2 * o * X.length := by rw [← hD']; ring
  rw [hX, hY, hP]
  simp only [lexLt, addPair]
  constructor
  · simp only [e1, lt_irrefl, decide_false, Bool.false_or, beq_self_eq_true, Bool.true_and]
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> linarith
  · congr 1
    linarith

/-! ## The translation lemma -/

/-- All points of the walk of `w` are on one side of the seam at offset `o` (`lft`: the left side, `o + x < 0`). -/
def OneSide (o : ℤ) (w : List (ℕ × Bool)) : Prop :=
  ∃ lft : Bool, ∀ p ∈ walkPts 2 (zeros 2) (w.map Prod.fst), (o + p.getD 0 0 < 0 ↔ lft = true)

theorem inBB_x {pts : List (List ℤ)} {x : List ℤ} (h : inBB 2 pts x = true) :
    (∃ p ∈ pts, p.getD 0 0 ≤ x.getD 0 0) ∧ (∃ p ∈ pts, x.getD 0 0 ≤ p.getD 0 0) := by
  unfold inBB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at h
  exact h.2 0 (by norm_num)

theorem side_of_inBB {o : ℤ} {lft : Bool} {pts : List (List ℤ)}
    (hs : ∀ p ∈ pts, (o + p.getD 0 0 < 0 ↔ lft = true)) {x : List ℤ} (hx : inBB 2 pts x = true) :
    (o + x.getD 0 0 < 0 ↔ lft = true) := by
  obtain ⟨⟨p, hp, hpx⟩, ⟨q, hq, hxq⟩⟩ := inBB_x hx
  cases lft
  · have h1 : ¬ (o + p.getD 0 0 < 0) := fun hc => by simpa using (hs p hp).mp hc
    simp only [Bool.false_eq_true, iff_false, not_lt]
    omega
  · have h1 : o + q.getD 0 0 < 0 := (hs q hq).mpr rfl
    simp only [iff_true]
    omega

theorem mem_cEdges_pts {w : List (ℕ × Bool)} {e : Edge} (he : e ∈ cEdges 2 w) :
    e.1 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) ∧ e.2 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) := by
  unfold cEdges at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  exact mem_edgesFrom_pts 2 _ w e' (List.mem_filter.mp he').1

theorem mem_eEdges_pts {w : List (ℕ × Bool)} {e : Edge} (he : e ∈ eEdges 2 w) :
    e.1 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) ∧ e.2 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) := by
  unfold eEdges at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  exact mem_edgesFrom_pts 2 _ w e' (List.mem_filter.mp he').1

/-- **The translation lemma.** -/
theorem checkWT_shift {L0 : ℕ} {o o' : ℤ} {w : List (ℕ × Bool)} (h : OneSide o w) (h' : OneSide o' w)
    (W : Wit) : checkWT L0 o w W = checkWT L0 o' w W := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  unfold checkWT
  dsimp only
  cases hA : W.alt.all (fun a => decide (a.2 < 4) && inBB 2 (walkPts 2 (zeros 2) (w.map Prod.fst)) a.1 &&
      inBB 2 (walkPts 2 (zeros 2) (w.map Prod.fst)) (addP a.1 (vecOf 2 a.2)))
  · simp
  · have hbox : ∀ e ∈ altEdges 2 W.alt, inBB 2 (walkPts 2 (zeros 2) (w.map Prod.fst)) e.1 = true ∧
        inBB 2 (walkPts 2 (zeros 2) (w.map Prod.fst)) e.2 = true := by
      intro e he
      unfold altEdges at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rw [List.all_eq_true] at hA
      have := hA a ha
      simp only [Bool.and_eq_true] at this
      exact ⟨this.1.2, this.2⟩
    have hY : ∀ e ∈ (if W.useE then eEdges 2 w else []), e.1 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) ∧
        e.2 ∈ walkPts 2 (zeros 2) (w.map Prod.fst) := by
      intro e he
      split at he
      · exact mem_eEdges_pts he
      · simp at he
    have sides : ∀ (q : ℤ) (b : Bool), (∀ p ∈ walkPts 2 (zeros 2) (w.map Prod.fst), (q + p.getD 0 0 < 0 ↔ b = true)) →
        phiTE q (cEdges 2 w) = ((2 : ℤ) * (if b then 1 else 0) * (cEdges 2 w).length,
          2 * q * (cEdges 2 w).length + sxE (cEdges 2 w)) ∧
        phiTE q (if W.useE then eEdges 2 w else []) = ((2 : ℤ) * (if b then 1 else 0) *
          (if W.useE then eEdges 2 w else []).length, 2 * q * (if W.useE then eEdges 2 w else []).length +
            sxE (if W.useE then eEdges 2 w else [])) ∧
        phiTE q (altEdges 2 W.alt) = ((2 : ℤ) * (if b then 1 else 0) * (altEdges 2 W.alt).length,
          2 * q * (altEdges 2 W.alt).length + sxE (altEdges 2 W.alt)) := by
      intro q b hq
      refine ⟨phiTE_side fun e he => ⟨hq _ (mem_cEdges_pts he).1, hq _ (mem_cEdges_pts he).2⟩,
        phiTE_side fun e he => ⟨hq _ (hY e he).1, hq _ (hY e he).2⟩,
        phiTE_side fun e he => ⟨side_of_inBB hq (hbox e he).1, side_of_inBB hq (hbox e he).2⟩⟩
    obtain ⟨sX, sY, sP⟩ := sides o l hl
    obtain ⟨sX', sY', sP'⟩ := sides o' l' hl'
    by_cases hD : (if W.useE then eEdges 2 w else []).length + (altEdges 2 W.alt).length = (cEdges 2 w).length
    · obtain ⟨e1, e2⟩ := lexLt_side sX sY sP hD
      obtain ⟨e1', e2'⟩ := lexLt_side sX' sY' sP' hD
      rw [e1, e2, e1', e2']
    · have hD' : ((if W.useE then eEdges 2 w else []).length + (altEdges 2 W.alt).length ==
          (cEdges 2 w).length) = false := by simpa using hD
      simp only [hD', Bool.false_and, Bool.or_false]

theorem exclT_shift {L0 : ℕ} {o o' : ℤ} {w : List (ℕ × Bool)} (h : OneSide o w) (h' : OneSide o' w) :
    ExclT L0 o w ↔ ExclT L0 o' w := by
  unfold ExclT
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W, (checkWT_shift h h' W) ▸ hW⟩
  · rintro ⟨W, hW⟩
    exact ⟨W, (checkWT_shift h h' W).symm ▸ hW⟩

/-! ## One-sided windows -/

theorem oneSide_right {t : ℤ} {w : List (ℕ × Bool)} (h : ∀ i ≤ w.length, 0 ≤ t + xdisp (w.take i)) :
    OneSide t w := by
  refine ⟨false, fun p hp => ?_⟩
  obtain ⟨i, hi, hpi⟩ := walkPts_x_pat hp
  have := h i hi
  simp only [Bool.false_eq_true, iff_false, not_lt]
  omega

theorem oneSide_left {t : ℤ} {w : List (ℕ × Bool)} (h : ∀ i ≤ w.length, t + xdisp (w.take i) < 0) :
    OneSide t w := by
  refine ⟨true, fun p hp => ?_⟩
  obtain ⟨i, hi, hpi⟩ := walkPts_x_pat hp
  have := h i hi
  simp only [iff_true]
  omega

/-- A window whose prefix displacements lie within `E` of `δ`, where the seam offset of `t + δ` is at least `E`
away from the seam, lies on one side of the seam at offset `t`. -/
theorem oneSide_of_ref {L : ℕ} (hL : 0 < L) {t δ E : ℤ} {w : List (ℕ × Bool)}
    (hE : ∀ i ≤ w.length, -E ≤ xdisp (w.take i) - δ ∧ xdisp (w.take i) - δ ≤ E) (hLE : 2 * E < L)
    (hb1 : -3 * (L : ℤ) ≤ 2 * (t + δ)) (hb2 : 2 * (t + δ) < 3 * L)
    (hfar : E ≤ qoffZ L (t + δ) ∨ qoffZ L (t + δ) < -E) : OneSide t w := by
  rcases qoffZ_cases hL hb1 hb2 with ⟨c1, c2, c3⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
  · rw [c3] at hfar
    rcases hfar with hf | hf
    · exact oneSide_right fun i hi => by have := hE i hi; omega
    · exact oneSide_left fun i hi => by have := hE i hi; omega
  · exact oneSide_right fun i hi => by have := hE i hi; omega
  · exact oneSide_left fun i hi => by have := hE i hi; omega

end SeamShift

end QEC
