import QEC.Count.AugDefs
import QEC.Count.SeamShift

/-!
# Soundness of the augmented certificate checks (rotated code, heights)

A state of the augmented certificate is a pattern `s` of `K` steps with a first-vertex height `h0` (`IsStA`); its head
height is `headHA s h0 = h0 - vdisp s`. Its potential `HofA` is the near potential `G` if the head height is below
`HC`, the bulk potential otherwise. From the checks (`CertOKA`) we get the hypotheses of `sum_legal_leT` for
`nxt = nxtA` and `Ex = ExA P.hN`:

* `certA_pos`, `certA_start`, `certA_closed`, `certA_rows`, `certA_startSum`.

Heights do not wrap: the height of the `i`-th vertex of a walk is `h0 - vdisp (w.take i)` (`offAt_nxtA`). The row of a
state with head height `h` is the computed row `rowSumA … s h` if `h ≤ HC` (near rows and the interface rows), and
`rowSumA … s bigH` otherwise: then every window of the row has first-vertex height at least its number of edges,
both at the true heights and at the heights of the computed row, so the ceiling of `checkWA` never binds and the
exclusions agree (`checkWA_shift`).
-/

namespace QEC

open Finset QECComp SeamShift CertSound

namespace CertSoundA

/-! ## Heights along a walk -/

theorem vdisp_eq (w : List (ℕ × Bool)) : vdisp w = ((w.map Prod.fst).map dl2).sum := by
  unfold vdisp
  rw [foldl_add_map (fun x : ℕ × Bool => dl2 x.1), zero_add, List.map_map]
  rfl

@[simp] theorem vdisp_nil : vdisp [] = 0 := by simp [vdisp_eq]

theorem vdisp_append (a b : List (ℕ × Bool)) : vdisp (a ++ b) = vdisp a + vdisp b := by
  simp [vdisp_eq, List.sum_append]

theorem vdisp_single (x : ℕ × Bool) : vdisp [x] = dl2 x.1 := by simp [vdisp_eq]

theorem vdisp_cons (x : ℕ × Bool) (w : List (ℕ × Bool)) : vdisp (x :: w) = dl2 x.1 + vdisp w := by
  simp [vdisp_eq]

theorem dl2_bounds (d : ℕ) : -1 ≤ dl2 d ∧ dl2 d ≤ 1 := by
  unfold dl2
  split_ifs <;> omega

theorem vdisp_bounds : ∀ w : List (ℕ × Bool), -(w.length : ℤ) ≤ vdisp w ∧ vdisp w ≤ w.length
  | [] => by simp
  | x :: w => by
    rw [vdisp_cons, List.length_cons]
    have := vdisp_bounds w
    have := dl2_bounds x.1
    push_cast
    omega

theorem vdisp_take_add (u : List (ℕ × Bool)) (j i : ℕ) :
    vdisp (u.take j) + vdisp ((u.drop j).take i) = vdisp (u.take (j + i)) := by
  rw [List.take_add, vdisp_append]

/-- `vdisp` of prefixes is 1-Lipschitz in the prefix length. -/
theorem vdisp_take_sub (w : List (ℕ × Bool)) {k i : ℕ} (hki : k ≤ i) :
    -((i - k : ℕ) : ℤ) ≤ vdisp (w.take i) - vdisp (w.take k) ∧
      vdisp (w.take i) - vdisp (w.take k) ≤ ((i - k : ℕ) : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
  rw [← vdisp_take_add w k j, Nat.add_sub_cancel_left]
  have h := vdisp_bounds ((w.drop k).take j)
  have hl : ((w.drop k).take j).length ≤ j := List.length_take_le _ _
  have hl' : (((w.drop k).take j).length : ℤ) ≤ j := by exact_mod_cast hl
  constructor <;> omega

theorem vdisp_take_bounds (w : List (ℕ × Bool)) (i : ℕ) :
    -(i : ℤ) ≤ vdisp (w.take i) ∧ vdisp (w.take i) ≤ i := by
  have h := vdisp_take_sub w (Nat.zero_le i)
  simp only [List.take_zero, vdisp_nil, sub_zero, Nat.sub_zero] at h
  exact h

theorem foldl_nxtA : ∀ (ds : List ℕ) (h : ℤ), ds.foldl nxtA h = h - (ds.map dl2).sum
  | [], h => by simp
  | d :: ds, h => by
    simp only [List.foldl, List.map_cons, List.sum_cons]
    rw [foldl_nxtA ds (nxtA h d)]
    unfold nxtA
    ring

/-- The height of the `i`-th vertex of a walk. -/
theorem offAt_nxtA (h0 : ℤ) (w : List (ℕ × Bool)) (i : ℕ) : offAt nxtA h0 w i = h0 - vdisp (w.take i) := by
  unfold offAt
  rw [foldl_nxtA, vdisp_eq]

/-! ## The bounding box of a window lies below the line `x - y = (number of edges)` -/

/-- The y-increment of a direction. -/
def dyA (d : ℕ) : ℤ := if d = 2 then 1 else if d = 3 then -1 else 0

theorem vecOf_two_getD1 (d : ℕ) : (vecOf 2 d).getD 1 0 = dyA d := by
  rw [getD_vecOf 2 d 1 (by norm_num)]
  match d with
  | 0 => simp [dyA]
  | 1 => simp [dyA]
  | 2 => simp [dyA]
  | 3 => simp [dyA]
  | d + 4 =>
    have h0 : ¬ (1 = (d + 4) / 2) := by omega
    simp only [h0, ite_false, dyA, show d + 4 ≠ 2 by omega, show d + 4 ≠ 3 by omega]

theorem walkPts_y : ∀ (ds : List ℕ) (o : List ℤ), o.length = 2 → ∀ p ∈ walkPts 2 o ds,
    ∃ i ≤ ds.length, p.getD 1 0 = o.getD 1 0 + ((ds.take i).map dyA).sum
  | [], o, _, p, hp => by
    simp only [walkPts_nil, List.mem_singleton] at hp
    exact ⟨0, le_rfl, by simp [hp]⟩
  | d :: ds, o, ho, p, hp => by
    simp only [walkPts_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · have ho' : (addP o (vecOf 2 d)).length = 2 := by simp [ho]
      obtain ⟨i, hi, hpi⟩ := walkPts_y ds _ ho' p hp
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [hpi, getD_addP _ _ 1 (by omega) (by simp), vecOf_two_getD1]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      ring

/-- A prefix sum of `f` is at most the full sum of `g` when `f ≤ g` and `0 ≤ g`. -/
theorem take_sum_le (f g : ℕ → ℤ) (hfg : ∀ d, f d ≤ g d) (hg : ∀ d, 0 ≤ g d) :
    ∀ (ds : List ℕ) (i : ℕ), ((ds.take i).map f).sum ≤ (ds.map g).sum
  | [], i => by simp
  | d :: ds, 0 => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons]
    have := hg d
    have : 0 ≤ (ds.map g).sum := List.sum_nonneg (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact hg y)
    omega
  | d :: ds, i + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    have := take_sum_le f g hfg hg ds i
    have := hfg d
    omega

/-- The indicator of `+x` steps. -/
def pxI (d : ℕ) : ℤ := if d = 0 then 1 else 0

/-- The indicator of `-y` steps. -/
def myI (d : ℕ) : ℤ := if d = 3 then 1 else 0

theorem px_my_le : ∀ ds : List ℕ, (ds.map pxI).sum + (ds.map myI).sum ≤ ds.length
  | [] => by simp
  | d :: ds => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := px_my_le ds
    have hd : pxI d + myI d ≤ 1 := by unfold pxI myI; split_ifs <;> omega
    push_cast
    omega

theorem sum_map_neg' (f : ℕ → ℤ) : ∀ l : List ℕ, (l.map (fun d => -f d)).sum = -(l.map f).sum
  | [] => by simp
  | d :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_neg' f l]
    ring

/-- Two points of the walk of a pattern: `x(p) - y(q)` is at most the number of steps. -/
theorem walk_x_sub_y {w : List (ℕ × Bool)} {p q : List ℤ} (hp : p ∈ walkPts 2 (zeros 2) (w.map Prod.fst))
    (hq : q ∈ walkPts 2 (zeros 2) (w.map Prod.fst)) : p.getD 0 0 - q.getD 1 0 ≤ w.length := by
  obtain ⟨i, -, hpi⟩ := walkPts_x _ _ (by simp [zeros]) p hp
  obtain ⟨j, -, hqj⟩ := walkPts_y _ _ (by simp [zeros]) q hq
  have h0 : (zeros 2).getD 0 0 = 0 := by simp [zeros]
  have h1 : (zeros 2).getD 1 0 = 0 := by simp [zeros]
  rw [h0, zero_add] at hpi
  rw [h1, zero_add] at hqj
  have a1 := take_sum_le dxOf pxI (fun d => by unfold dxOf pxI; split_ifs <;> omega)
    (fun d => by unfold pxI; split_ifs <;> omega) (w.map Prod.fst) i
  have a2 := take_sum_le (fun d => -dyA d) myI (fun d => by unfold dyA myI; split_ifs <;> omega)
    (fun d => by unfold myI; split_ifs <;> omega) (w.map Prod.fst) j
  have a3 := px_my_le (w.map Prod.fst)
  have hneg : (((w.map Prod.fst).take j).map (fun d => -dyA d)).sum = -(((w.map Prod.fst).take j).map dyA).sum :=
    sum_map_neg' dyA _
  rw [hneg] at a2
  rw [List.length_map] at a3
  rw [hpi, hqj]
  omega

theorem inBB_y {pts : List (List ℤ)} {x : List ℤ} (h : inBB 2 pts x = true) :
    (∃ p ∈ pts, p.getD 1 0 ≤ x.getD 1 0) ∧ (∃ p ∈ pts, x.getD 1 0 ≤ p.getD 1 0) := by
  unfold inBB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at h
  exact h.2 1 (by norm_num)

/-- A point of the bounding box of a window has `x - y` at most the number of edges of the window. -/
theorem xyOf_le_of_inBB {w : List (ℕ × Bool)} {x : List ℤ}
    (h : inBB 2 (walkPts 2 (zeros 2) (w.map Prod.fst)) x = true) : xyOf x ≤ w.length := by
  obtain ⟨-, ⟨p, hp, hxp⟩⟩ := inBB_x h
  obtain ⟨⟨q, hq, hqx⟩, -⟩ := inBB_y h
  have := walk_x_sub_y hp hq
  unfold xyOf
  omega

/-! ## The translation lemma -/

/-- **The translation lemma.** With `hN = 0`, the region-aware check does not depend on the first-vertex height as long
as it is at least the number of edges of the window (the ceiling never binds). -/
theorem checkWA_shift {h0 h0' : ℤ} {w : List (ℕ × Bool)} (h1 : (w.length : ℤ) ≤ h0) (h2 : (w.length : ℤ) ≤ h0')
    (W : Wit) : checkWA 0 h0 w W = checkWA 0 h0' w W := by
  have e1 : (if h0 < ((0 : ℕ) : ℤ) then (1 : ℤ) else 0) = 0 := by
    split_ifs with h
    · push_cast at h; omega
    · rfl
  have e2 : (if h0' < ((0 : ℕ) : ℤ) then (1 : ℤ) else 0) = 0 := by
    split_ifs with h
    · push_cast at h; omega
    · rfl
  unfold checkWA
  simp only [e1, e2]
  cases hc : checkW 2 cA w W
  · simp
  · obtain ⟨hA, -, -⟩ := checkW_spec hc
    have hbox : ∀ e ∈ altEdges 2 W.alt, xyOf e.1 ≤ w.length ∧ xyOf e.2 ≤ w.length := by
      intro e he
      unfold altEdges at he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      obtain ⟨-, hb1, hb2⟩ := hA a ha
      exact ⟨xyOf_le_of_inBB hb1, xyOf_le_of_inBB hb2⟩
    simp only [Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro H e he
      obtain ⟨⟨⟨-, -⟩, a3⟩, a4⟩ := H e he
      have := hbox e he
      exact ⟨⟨⟨by omega, by omega⟩, a3⟩, a4⟩
    · intro H e he
      obtain ⟨⟨⟨-, -⟩, a3⟩, a4⟩ := H e he
      have := hbox e he
      exact ⟨⟨⟨by omega, by omega⟩, a3⟩, a4⟩

theorem exclA_shift {h0 h0' : ℤ} {w : List (ℕ × Bool)} (h1 : (w.length : ℤ) ≤ h0) (h2 : (w.length : ℤ) ≤ h0') :
    ExclA 0 h0 w ↔ ExclA 0 h0' w := by
  unfold ExclA
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W, (checkWA_shift h1 h2 W) ▸ hW⟩
  · rintro ⟨W, hW⟩
    exact ⟨W, (checkWA_shift h1 h2 W).symm ▸ hW⟩

/-! ## Key facts (the only place where the encoding of the keys is used) -/

theorem stepCode_lt : ∀ s : List (ℕ × Bool), stepCode s < 4 ^ s.length
  | [] => by simp [stepCode]
  | x :: w => by
    have := stepCode_lt w
    have : x.1 % 4 < 4 := Nat.mod_lt _ (by norm_num)
    simp only [stepCode, List.length_cons, pow_succ]
    omega

theorem labCode_lt : ∀ s : List (ℕ × Bool), labCode s < 2 ^ s.length
  | [] => by simp [labCode]
  | x :: w => by
    have := labCode_lt w
    have : (if x.2 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    simp only [labCode, List.length_cons, pow_succ]
    omega

theorem stepCode_digit : ∀ (s : List (ℕ × Bool)) (i : ℕ) (hi : i < s.length), stepCode s / 4 ^ i % 4 = s[i].1 % 4
  | [], i, hi => by simp at hi
  | x :: w, 0, _ => by
    simp only [stepCode, pow_zero, Nat.div_one, List.getElem_cons_zero]
    omega
  | x :: w, i + 1, hi => by
    simp only [List.length_cons] at hi
    simp only [stepCode, List.getElem_cons_succ]
    rw [pow_succ, mul_comm (4 ^ i) 4, ← Nat.div_div_eq_div_mul]
    have : (x.1 % 4 + 4 * stepCode w) / 4 = stepCode w := by omega
    rw [this]
    exact stepCode_digit w i (by omega)

theorem labCode_bit : ∀ (s : List (ℕ × Bool)) (i : ℕ) (hi : i < s.length),
    labCode s / 2 ^ i % 2 = if s[i].2 then 1 else 0
  | [], i, hi => by simp at hi
  | x :: w, 0, _ => by
    simp only [labCode, pow_zero, Nat.div_one, List.getElem_cons_zero]
    split_ifs <;> omega
  | x :: w, i + 1, hi => by
    simp only [List.length_cons] at hi
    simp only [labCode, List.getElem_cons_succ]
    rw [pow_succ, mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul]
    have h1 : (if x.2 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have : ((if x.2 then 1 else 0) + 2 * labCode w) / 2 = labCode w := by omega
    rw [this]
    exact labCode_bit w i (by omega)

/-- A digit below position `K` does not see the multiples of `b ^ K`. -/
theorem div_pow_mod {a i K : ℕ} (Y b : ℕ) (hi : i < K) (hb : 2 ≤ b) : (a + b ^ K * Y) / b ^ i % b = a / b ^ i % b := by
  have hpos : 0 < b ^ i := pow_pos (by omega) i
  obtain ⟨t, rfl⟩ : ∃ t, K = i + 1 + t := ⟨K - i - 1, by omega⟩
  have e : b ^ (i + 1 + t) * Y = b ^ i * (b * (b ^ t * Y)) := by
    rw [pow_add, pow_succ]
    ring
  rw [e, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem eight_pow (K : ℕ) : (8 : ℕ) ^ K = 4 ^ K * 2 ^ K := by
  rw [← mul_pow]
  norm_num

theorem ckeyA_eq (K : ℕ) (s : List (ℕ × Bool)) (h : ℕ) :
    ckeyA K s h = stepCode s + 4 ^ K * (labCode s + 2 ^ K * h) := by
  unfold ckeyA
  rw [eight_pow]
  ring

/-- Keys decode to their patterns. -/
theorem decodeA_ckeyA {K : ℕ} {s : List (ℕ × Bool)} (hs : s.length = K) (hd : DirOK 2 s) (h : ℕ) :
    decodeA K (ckeyA K s h) = s := by
  apply List.ext_getElem (by simp [decodeA, hs])
  intro i h1 h2
  have hiK : i < K := by simpa [decodeA] using h1
  simp only [decodeA, List.getElem_map, List.getElem_range]
  rw [ckeyA_eq]
  have hst : stepCode s < 4 ^ K := hs ▸ stepCode_lt s
  have e1 : (stepCode s + 4 ^ K * (labCode s + 2 ^ K * h)) / 4 ^ i % 4 = s[i].1 := by
    rw [div_pow_mod _ 4 hiK (by norm_num), stepCode_digit s i h2]
    exact Nat.mod_eq_of_lt (by have := hd _ (List.getElem_mem h2); omega)
  have e2 : (stepCode s + 4 ^ K * (labCode s + 2 ^ K * h)) / 4 ^ K = labCode s + 2 ^ K * h := by
    rw [Nat.add_mul_div_left _ _ (pow_pos (by norm_num) K), Nat.div_eq_of_lt hst, zero_add]
  rw [e1, e2, div_pow_mod _ 2 hiK (by norm_num), labCode_bit s i h2]
  refine Prod.ext rfl ?_
  show ((if s[i].2 = true then 1 else 0) == 1) = s[i].2
  cases s[i].2 <;> rfl

/-- Keys give back their heights. -/
theorem heightOf_ckeyA {K : ℕ} {s : List (ℕ × Bool)} (hs : s.length = K) (h : ℕ) :
    heightOf K (ckeyA K s h) = h := by
  unfold heightOf ckeyA
  have hst := stepCode_lt s
  have hlb := labCode_lt s
  rw [hs] at hst hlb
  have hlt : stepCode s + 4 ^ K * labCode s < 8 ^ K := by
    rw [eight_pow]
    have : 4 ^ K * labCode s + 4 ^ K ≤ 4 ^ K * 2 ^ K := by
      rw [← mul_add_one]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  rw [Nat.add_mul_div_left _ _ (pow_pos (by norm_num) K), Nat.div_eq_of_lt hlt, zero_add]

/-! ## The computational checks, unfolded -/

section Computed

variable (P : ParamsA) (nk nG bk bH : Array ℕ)

theorem exclWinA_sound {h0 : ℤ} {u : List (ℕ × Bool)} (h : exclWinA P h0 u = true) : ExclA P.hN h0 u := by
  unfold exclWinA at h
  split at h
  · exact ⟨_, h⟩
  · exact absurd h (by simp)

theorem exclEndingA_sound {h0 : ℤ} {u : List (ℕ × Bool)} (h : exclEndingA P h0 u = true) :
    ∃ m, 2 ≤ m ∧ m ≤ u.length ∧ m ≤ P.K + 1 ∧
      ExclA P.hN (h0 - vdisp (u.take (u.length - m))) (u.drop (u.length - m)) := by
  unfold exclEndingA at h
  rw [List.any_eq_true] at h
  obtain ⟨m, hm, hx⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_range] at hm
  exact ⟨m, hx.1.1, hx.1.2, by omega, exclWinA_sound P hx.2⟩

/-- The contribution of the candidate `x` to the computed row of `s` at head height `h`. -/
def rcontribA (s : List (ℕ × Bool)) (h : ℤ) (x : ℕ × Bool) : ℕ :=
  if (!selfAvoid 2 (s ++ [x]) || decide (h - dl2 x.1 < 0)) = true then 0
  else match potA P nk nG bk bH (s ++ [x]).tail (h - dl2 x.1) with
    | some H => if exclWinA P (h + vdisp s) (s ++ [x]) = true then 0 else (if x.2 then P.wC else P.wE) * H
    | none => 0

/-- A candidate that is not skipped and leads to an unlisted state has an excluded window. -/
def rgoodA (s : List (ℕ × Bool)) (h : ℤ) (x : ℕ × Bool) : Prop :=
  (!selfAvoid 2 (s ++ [x]) || decide (h - dl2 x.1 < 0)) = false →
    potA P nk nG bk bH (s ++ [x]).tail (h - dl2 x.1) = none → exclEndingA P (h + vdisp s) (s ++ [x]) = true

theorem rowSumA_spec {s : List (ℕ × Bool)} {h : ℤ} {tot : ℕ} (hr : rowSumA P nk nG bk bH s h = some tot) :
    tot = ((candList 2).map (rcontribA P nk nG bk bH s h)).sum ∧
      ∀ x ∈ candList 2, rgoodA P nk nG bk bH s h x := by
  unfold rowSumA at hr
  have := foldl_opt _ (rcontribA P nk nG bk bH s h) (rgoodA P nk nG bk bH s h) (fun x => rfl) ?_ ?_
    (candList 2) 0 tot hr
  · simpa using this
  · intro a x hx
    simp only [rgoodA] at hx
    simp only [rcontribA]
    cases h1 : (!selfAvoid 2 (s ++ [x]) || decide (h - dl2 x.1 < 0))
    · simp only [Bool.false_eq_true, ite_false]
      cases h2 : potA P nk nG bk bH (s ++ [x]).tail (h - dl2 x.1) with
      | some j =>
        simp only
        by_cases h3 : exclWinA P (h + vdisp s) (s ++ [x]) = true
        · simp [h3]
        · simp [h3]
      | none =>
        have h3 := hx h1 h2
        simp [h3]
    · simp
  · intro a x hx
    simp only [rgoodA, not_imp] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    simp only [Bool.not_eq_true] at h3
    simp only [h1, h2, h3, Bool.false_eq_true, ite_false]

theorem rowOKA_spec {s : List (ℕ × Bool)} {h : ℤ} {H : ℕ} (hr : rowOKA P nk nG bk bH s h H = true) :
    0 < P.Hmin ∧ P.Hmin ≤ H ∧ ∃ tot, rowSumA P nk nG bk bH s h = some tot ∧ tot * P.lamD ≤ P.lamN * P.Q * H := by
  unfold rowOKA at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  refine ⟨h1, h2, ?_⟩
  split at h3
  · rename_i tot htot
    exact ⟨tot, htot, by simpa using h3⟩
  · exact absurd h3 (by simp)

theorem nearRowA {hi : ℕ} (hr : nearRowsOKA P nk nG bk bH 0 hi = true) {i : ℕ} (hi' : i < hi) :
    heightOf P.K nk[i]! < P.HC ∧
      rowOKA P nk nG bk bH (decodeA P.K nk[i]!) ((heightOf P.K nk[i]! : ℕ) : ℤ) nG[i]! = true := by
  unfold nearRowsOKA at hr
  rw [List.all_eq_true] at hr
  have := hr i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem ifRowA {hi : ℕ} (hr : ifRowsOKA P nk nG bk bH 0 hi = true) {i : ℕ} (hi' : i < hi) :
    rowOKA P nk nG bk bH (decodeA P.K bk[i]!) (P.HC : ℤ) bH[i]! = true := by
  unfold ifRowsOKA at hr
  rw [List.all_eq_true] at hr
  exact hr i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)

theorem bulkRowA {hi : ℕ} (hr : bulkRowsOKA P nk nG bk bH 0 hi = true) {i : ℕ} (hi' : i < hi) :
    rowOKA P nk nG bk bH (decodeA P.K bk[i]!) bigH bH[i]! = true := by
  unfold bulkRowsOKA at hr
  rw [List.all_eq_true] at hr
  exact hr i (List.mem_range'.mpr ⟨i, by omega, by simp⟩)

theorem potA_neg {s : List (ℕ × Bool)} {h : ℤ} (hh : h < 0) : potA P nk nG bk bH s h = none := by
  unfold potA
  simp only [hh, ↓reduceIte]

theorem potA_near {s : List (ℕ × Bool)} {h : ℤ} (h1 : 0 ≤ h) (h2 : h < P.HC) :
    potA P nk nG bk bH s h = (lookup nk (ckeyA P.K s h.toNat)).map (fun j => nG[j]!) := by
  unfold potA
  simp only [show ¬ (h < 0) by omega, h2, ↓reduceIte]

theorem potA_far {s : List (ℕ × Bool)} {h : ℤ} (h2 : (P.HC : ℤ) ≤ h) :
    potA P nk nG bk bH s h = (lookup bk (ckeyA P.K s 0)).map (fun j => bH[j]!) := by
  unfold potA
  simp only [show ¬ (h < 0) by omega, show ¬ (h < (P.HC : ℤ)) by omega, ↓reduceIte]

end Computed

/-! ## Heights of states -/

variable {P : ParamsA} {nk nG bk bH : Array ℕ}

/-- The head height at which the computed row of a state with head height `h` is checked. -/
def hcOf (P : ParamsA) (h : ℤ) : ℤ := if h ≤ P.HC then h else bigH

theorem K_le (hc : CertOKA P nk nG bk bH) : P.K ≤ 126 := by
  have := hc.hHC
  have := hc.hHC2
  omega

/-- The head height of the next state. -/
theorem headHA_next {s : List (ℕ × Bool)} {h0 : ℤ} (hs : s ≠ []) (x : ℕ × Bool) :
    headHA (s ++ [x]).tail (offAt nxtA h0 s 1) = headHA s h0 - dl2 x.1 := by
  obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs
  unfold headHA
  rw [offAt_nxtA]
  simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.tail_cons, vdisp_append, vdisp_cons,
    vdisp_nil]
  ring

/-- The computed row of a listed state, and its potential. -/
theorem row_of_isStA (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStA P nk nG bk bH s h0) :
    P.Hmin ≤ HofA P nk nG bk bH s h0 ∧ ∃ tot, rowSumA P nk nG bk bH s (hcOf P (headHA s h0)) = some tot ∧
      tot * P.lamD ≤ P.lamN * P.Q * HofA P nk nG bk bH s h0 := by
  obtain ⟨hlen, hdir, hpot⟩ := hs
  unfold HofA
  generalize headHA s h0 = h at hpot ⊢
  have hHC2 := hc.hHC2
  by_cases hneg : h < 0
  · rw [potA_neg P nk nG bk bH hneg] at hpot
    exact absurd hpot (by simp)
  by_cases hn : h < P.HC
  · rw [potA_near P nk nG bk bH (by omega) hn] at hpot ⊢
    rw [Option.isSome_map] at hpot
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpot
    obtain ⟨hjlt, hk⟩ := lookup_some hj
    obtain ⟨-, hrow⟩ := nearRowA P nk nG bk bH hc.near hjlt
    rw [hk, decodeA_ckeyA hlen hdir, heightOf_ckeyA hlen, Int.toNat_of_nonneg (by omega)] at hrow
    have hoc : hcOf P h = h := by unfold hcOf; simp only [show h ≤ (P.HC : ℤ) by omega, ↓reduceIte]
    rw [hoc, hj]
    obtain ⟨-, h2, h3⟩ := rowOKA_spec P nk nG bk bH hrow
    exact ⟨h2, h3⟩
  · rw [potA_far P nk nG bk bH (by omega)] at hpot ⊢
    rw [Option.isSome_map] at hpot
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hpot
    obtain ⟨hjlt, hk⟩ := lookup_some hj
    have hr1 := ifRowA P nk nG bk bH hc.iface hjlt
    have hr2 := bulkRowA P nk nG bk bH hc.bulk hjlt
    rw [hk, decodeA_ckeyA hlen hdir] at hr1 hr2
    rw [hj]
    simp only [Option.map_some, Option.getD_some]
    unfold hcOf
    by_cases hsm : h ≤ P.HC
    · simp only [hsm, ↓reduceIte]
      rw [show h = (P.HC : ℤ) by omega]
      obtain ⟨-, h2, h3⟩ := rowOKA_spec P nk nG bk bH hr1
      exact ⟨h2, h3⟩
    · simp only [hsm, ↓reduceIte]
      obtain ⟨-, h2, h3⟩ := rowOKA_spec P nk nG bk bH hr2
      exact ⟨h2, h3⟩

/-- The exclusions of the windows of a successor agree at the heights of the computed row and at the true heights. -/
theorem win_equivA (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ} (hlen : s.length = P.K)
    (x : ℕ × Bool) {j : ℕ} (hj : j < P.K) :
    ExclA P.hN (hcOf P (headHA s h0) + vdisp s - vdisp ((s ++ [x]).take j)) ((s ++ [x]).drop j) ↔
      ExclA P.hN (offAt nxtA h0 (s ++ [x]) j) ((s ++ [x]).drop j) := by
  rw [offAt_nxtA]
  unfold hcOf
  by_cases hsm : headHA s h0 ≤ P.HC
  · simp only [hsm, ↓reduceIte]
    unfold headHA
    ring_nf
  · simp only [hsm, ↓reduceIte]
    rw [hc.hN0]
    have hHC := hc.hHC
    have hK2 := K_le hc
    have hulen : (s ++ [x]).length = P.K + 1 := by simp [hlen]
    have hwl : (((s ++ [x]).drop j).length : ℤ) = P.K + 1 - j := by
      rw [List.length_drop, hulen]
      push_cast [show j ≤ P.K + 1 by omega]
      ring
    have htj : (s ++ [x]).take j = s.take j := List.take_append_of_le_length (by omega)
    have hsK : s.take P.K = s := by rw [← hlen]; exact List.take_length
    have hsub := vdisp_take_sub s (show j ≤ P.K by omega)
    rw [hsK] at hsub
    have hxj := vdisp_take_bounds s j
    have hxs := vdisp_bounds s
    rw [hlen] at hxs
    unfold headHA at hsm
    rw [htj]
    apply exclA_shift
    · rw [hwl]
      unfold bigH
      omega
    · rw [hwl]
      push_cast [Nat.cast_sub (show j ≤ P.K by omega)] at hsub
      omega

/-- The potential of a successor at the height of the computed row is its true potential. -/
theorem pot_succA (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ} (hlen : s.length = P.K)
    (x : ℕ × Bool) :
    potA P nk nG bk bH (s ++ [x]).tail (hcOf P (headHA s h0) - dl2 x.1) =
      potA P nk nG bk bH (s ++ [x]).tail (headHA (s ++ [x]).tail (offAt nxtA h0 s 1)) := by
  have hK1 := hc.hK
  have hs0 : s ≠ [] := by rintro rfl; simp at hlen; omega
  rw [headHA_next hs0]
  have hd := dl2_bounds x.1
  have hHC2 := hc.hHC2
  unfold hcOf
  by_cases hsm : headHA s h0 ≤ P.HC
  · simp only [hsm, ↓reduceIte]
  · simp only [hsm, ↓reduceIte]
    rw [potA_far P nk nG bk bH (by unfold bigH; omega), potA_far P nk nG bk bH (by omega)]

/-- A legal successor does not go above the top side. -/
theorem succ_head_nonneg {s : List (ℕ × Bool)} {h0 : ℤ} {x : ℕ × Bool} (hK : 1 ≤ s.length)
    {hN : ℕ} (hx : SuccG nxtA (ExA hN) s h0 x) : 0 ≤ headHA s h0 - dl2 x.1 := by
  have h := hx.2.2 (s.length + 1) (by omega) le_rfl
  rw [Nat.sub_self, offAt_nxtA, List.take_zero, vdisp_nil, sub_zero, List.drop_zero] at h
  have h2 : ¬ (h0 - vdisp ((s ++ [x]).take (s ++ [x]).length) < 0) := fun hlt => h (Or.inr ⟨_, le_rfl, hlt⟩)
  rw [List.take_length, vdisp_append, vdisp_single] at h2
  unfold headHA
  omega

end CertSoundA

open CertSoundA

variable {P : ParamsA} {nk nG bk bH : Array ℕ}

/-! ## Positivity, closure and rows -/

theorem certA_pos (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStA P nk nG bk bH s h0) : P.Hmin ≤ HofA P nk nG bk bH s h0 :=
  (row_of_isStA hc hs).1

theorem certA_closed (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStA P nk nG bk bH s h0) {x : ℕ × Bool} (hx : SuccG nxtA (ExA P.hN) s h0 x) :
    IsStA P nk nG bk bH (s ++ [x]).tail (offAt nxtA h0 s 1) := by
  have hs' := hs
  obtain ⟨hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, tot, htot, -⟩ := row_of_isStA hc hs'
  obtain ⟨-, hgood⟩ := rowSumA_spec P nk nG bk bH htot
  have hx1 : x.1 < 2 * 2 := hx.1
  have hg := hgood x (mem_candList.mpr hx1)
  have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
  have hnn := succ_head_nonneg (by omega) hx
  have hnn' : ¬ (hcOf P (headHA s h0) - dl2 x.1 < 0) := by
    have hd := dl2_bounds x.1
    unfold hcOf
    split_ifs
    · omega
    · unfold bigH; omega
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp (List.mem_of_mem_tail hy) with hy | hy
    · exact hdir y hy
    · rw [List.mem_singleton.mp hy]
      exact hx1
  · rw [← pot_succA hc hlen x]
    cases hp : potA P nk nG bk bH (s ++ [x]).tail (hcOf P (headHA s h0) - dl2 x.1) with
    | some _ => rfl
    | none =>
      exfalso
      have hcond : (!selfAvoid 2 (s ++ [x]) || decide (hcOf P (headHA s h0) - dl2 x.1 < 0)) = false := by
        simp [hsa, hnn']
      obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingA_sound P (hg hcond hp)
      have hulen : (s ++ [x]).length = s.length + 1 := by simp
      rw [hulen] at hmle hex
      have hj : s.length + 1 - m < P.K := by omega
      rw [win_equivA hc hlen x hj] at hex
      exact hx.2.2 m hm2 hmle (Or.inl hex)

open scoped Classical in
theorem certA_rows (hc : CertOKA P nk nG bk bH) {s : List (ℕ × Bool)} {h0 : ℤ}
    (hs : IsStA P nk nG bk bH s h0) :
    ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofA P nk nG bk bH (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ) ≤
      ((P.lamN : ℝ) / P.lamD) * HofA P nk nG bk bH s h0 := by
  have hs' := hs
  obtain ⟨hlen, hdir, -⟩ := hs
  have hK1 := hc.hK
  obtain ⟨-, tot, htot, hrow⟩ := row_of_isStA hc hs'
  obtain ⟨htot_eq, -⟩ := rowSumA_spec P nk nG bk bH htot
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hlamDr : (0 : ℝ) < P.lamD := by exact_mod_cast hc.hlamD
  have hterm : ∀ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
        (HofA P nk nG bk bH (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ) =
      (rcontribA P nk nG bk bH s (hcOf P (headHA s h0)) x : ℝ) / P.Q := by
    intro x hxm
    have hx := (Finset.mem_filter.mp hxm).2
    have hsa : selfAvoid 2 (s ++ [x]) = true := selfAvoid_iff.mpr hx.2.1
    have hnn := succ_head_nonneg (by omega) hx
    have hnn' : ¬ (hcOf P (headHA s h0) - dl2 x.1 < 0) := by
      have hd := dl2_bounds x.1
      unfold hcOf
      split_ifs
      · omega
      · unfold bigH; omega
    have hcond : (!selfAvoid 2 (s ++ [x]) || decide (hcOf P (headHA s h0) - dl2 x.1 < 0)) = false := by
      simp [hsa, hnn']
    have hnex : exclWinA P (hcOf P (headHA s h0) + vdisp s) (s ++ [x]) = false := by
      cases he : exclWinA P (hcOf P (headHA s h0) + vdisp s) (s ++ [x])
      · rfl
      · exfalso
        have hE := exclWinA_sound P he
        have hw := win_equivA hc hlen x (h0 := h0) (j := 0) (by omega)
        simp only [List.take_zero, vdisp_nil, sub_zero, List.drop_zero] at hw
        rw [hw] at hE
        exact hx.2.2 (s.length + 1) (by omega) le_rfl (Or.inl (by simpa using hE))
    obtain ⟨-, -, hp⟩ := certA_closed hc hs' hx
    obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp hp
    have hps := pot_succA hc hlen x (h0 := h0)
    have hHof : HofA P nk nG bk bH (s ++ [x]).tail (offAt nxtA h0 s 1) = h' := by
      unfold HofA
      rw [hh']
      rfl
    rw [hHof]
    simp only [rcontribA, hcond, Bool.false_eq_true, ite_false, hps, hh', hnex]
    unfold wtW
    obtain ⟨d, b⟩ := x
    cases b <;> simp [div_mul_eq_mul_div]
  have hsumC : ∑ x ∈ cands 2, (rcontribA P nk nG bk bH s (hcOf P (headHA s h0)) x : ℝ) = (tot : ℝ) := by
    rw [cands_eq_toFinset, List.sum_toFinset _ (candList_nodup _), htot_eq]
    push_cast
    rw [List.map_map]
    rfl
  calc ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) [x] *
          (HofA P nk nG bk bH (s ++ [x]).tail (offAt nxtA h0 s 1) : ℝ)
      = ∑ x ∈ (cands 2).filter (SuccG nxtA (ExA P.hN) s h0),
          (rcontribA P nk nG bk bH s (hcOf P (headHA s h0)) x : ℝ) / P.Q := Finset.sum_congr rfl hterm
    _ ≤ ∑ x ∈ cands 2, (rcontribA P nk nG bk bH s (hcOf P (headHA s h0)) x : ℝ) / P.Q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (tot : ℝ) / P.Q := by rw [← Finset.sum_div, hsumC]
    _ ≤ ((P.lamN : ℝ) / P.lamD) * HofA P nk nG bk bH s h0 := by
        rw [div_le_iff₀ hQr]
        have hrow' : (tot : ℝ) * P.lamD ≤ P.lamN * P.Q * (HofA P nk nG bk bH s h0 : ℝ) := by exact_mod_cast hrow
        rw [show (P.lamN : ℝ) / P.lamD * (HofA P nk nG bk bH s h0 : ℝ) * P.Q =
          (P.lamN * P.Q * (HofA P nk nG bk bH s h0 : ℝ)) / P.lamD by ring, le_div_iff₀ hlamDr]
        exact hrow'

/-! ## Start completeness -/

namespace CertSoundA

theorem rangeAllA_of {lo : ℤ} {cnt : ℕ} {f : ℤ → Bool} (h : rangeAllA lo cnt f = true) {q : ℤ} (h1 : lo ≤ q)
    (h2 : q < lo + cnt) : f q = true := by
  unfold rangeAllA at h
  rw [List.all_eq_true] at h
  have := h (q - lo).toNat (List.mem_range.mpr (by omega))
  rwa [show lo + ((q - lo).toNat : ℤ) = q by omega] at this

theorem exclEndingA_single (P : ParamsA) (h0 : ℤ) (x : ℕ × Bool) : exclEndingA P h0 [x] = false := by
  unfold exclEndingA
  rw [List.any_eq_false]
  intro m _
  simp only [List.length_singleton, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro h1 h2
  omega

/-- Start completeness from the check `dfsHA` at `hd`, for a pattern whose vertices are at heights `≥ 0` from `hd` and
whose exclusions at the heights `hd - vdisp (s.take i)` imply its exclusions at its true heights. -/
theorem start_of_dfsA {h0 hd : ℤ} {s : List (ℕ × Bool)} (hK : 1 ≤ P.K) (hlen : s.length = P.K)
    (hdfs : dfsHA P nk nG bk bH hd = true) (hleg : LegalG nxtA (ExA P.hN) (P.K + 1) h0 s)
    (hnn : ∀ i, 1 ≤ i → i ≤ P.K → 0 ≤ hd - vdisp (s.take i))
    (hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclA P.hN (hd - vdisp (s.take i)) ((s.drop i).take m) →
      ExA P.hN (offAt nxtA h0 s i) ((s.drop i).take m)) :
    (potA P nk nG bk bH s (hd - vdisp s)).isSome = true := by
  obtain ⟨hsa, hdir, hw⟩ := hleg
  have key : ∀ j, 1 ≤ j → j ≤ P.K → dfsA P nk nG bk bH hd (P.K - j) (s.take j) = true := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- the first step: `dfsHA`
        have hs0 : 0 < s.length := by omega
        have hmem : s[0] ∈ candList 2 := mem_candList.mpr (hdir _ (List.getElem_mem hs0))
        obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
        unfold dfsHA at hdfs
        rw [List.all_eq_true] at hdfs
        have hx := hdfs k (List.mem_range.mpr hk)
        simp only [dfsTopA, List.getElem?_eq_getElem hk, hke] at hx
        have h1 : s.take (0 + 1) = [s[0]] := by
          rw [Nat.zero_add, List.take_one, List.head?_eq_getElem?]
          simp [List.getElem?_eq_getElem hs0]
        have hsa1 : selfAvoid 2 [s[0]] = true := by
          rw [← h1]
          exact selfAvoid_iff.mpr (selfAv_take hsa 1)
        have hnn1 := hnn 1 le_rfl hK
        rw [show (1 : ℕ) = 0 + 1 from rfl, h1] at hnn1
        have hd1 : decide (hd - vdisp [s[0]] < 0) = false := by simp only [decide_eq_false_iff_not]; omega
        rw [hsa1, hd1, exclEndingA_single] at hx
        simp only [Bool.not_true, Bool.false_or] at hx
        rw [h1, show P.K - (0 + 1) = P.K - 1 by omega]
        exact hx
      · have h1 := ih (by omega) (by omega)
        rw [show P.K - j = (P.K - (j + 1)) + 1 by omega] at h1
        simp only [dfsA, List.all_eq_true] at h1
        have hjs : j < s.length := by omega
        have hx := h1 s[j] (mem_candList.mpr (hdir _ (List.getElem_mem hjs)))
        rw [List.take_append_getElem hjs] at hx
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hx
        have hlt : (s.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
        rcases hx with ((hx | hx) | hx) | hx
        · exfalso
          have := selfAvoid_iff.mpr (selfAv_take hsa (j + 1))
          rw [hx] at this
          exact absurd this (by simp)
        · exfalso
          have := hnn (j + 1) (by omega) hj
          omega
        · exfalso
          obtain ⟨m, hm2, hmle, -, hex⟩ := exclEndingA_sound P hx
          rw [hlt] at hmle hex
          have hw1 : (s.take (j + 1)).drop (j + 1 - m) = (s.drop (j + 1 - m)).take m := by
            rw [List.drop_take]
            congr 1
            omega
          have hw2 : (s.take (j + 1)).take (j + 1 - m) = s.take (j + 1 - m) := by
            rw [List.take_take]
            congr 1
            omega
          rw [hw1, hw2] at hex
          exact hw (j + 1 - m) m hm2 (by omega) (by omega) (hwin _ _ hm2 (by omega) hex)
        · exact hx
  have hK' := key P.K hK le_rfl
  rw [Nat.sub_self, List.take_of_length_le (by omega)] at hK'
  simpa only [dfsA] using hK'

/-- The vertices of a legal walk from a height `≥ 0` stay at heights `≥ 0`. -/
theorem legal_nonneg {h0 : ℤ} {s : List (ℕ × Bool)} {hN : ℕ} (hK : 2 ≤ s.length)
    (hleg : LegalG nxtA (ExA hN) (s.length + 1) h0 s) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ s.length) :
    0 ≤ h0 - vdisp (s.take i) := by
  obtain ⟨-, -, hw⟩ := hleg
  set i' := min (i - 1) (s.length - 2) with hi'
  have h1 : i' + 2 ≤ s.length := by omega
  have h2 : i' ≤ i := by omega
  have h3 : i - i' ≤ 2 := by omega
  have hne := hw i' 2 le_rfl (by omega) h1
  have hlen2 : ((s.drop i').take 2).length = 2 := by rw [List.length_take, List.length_drop]; omega
  have hc : ¬ (offAt nxtA h0 s i' - vdisp (((s.drop i').take 2).take (i - i')) < 0) :=
    fun hlt => hne (Or.inr ⟨i - i', by omega, hlt⟩)
  rw [offAt_nxtA, List.take_take, show min (i - i') 2 = i - i' by omega, sub_sub, vdisp_take_add,
    show i' + (i - i') = i by omega] at hc
  omega

end CertSoundA

theorem certA_start (hc : CertOKA P nk nG bk bH) {h0 : ℤ} (hh : 0 ≤ h0) {s : List (ℕ × Bool)}
    (hs : s.length = P.K) (hleg : LegalG nxtA (ExA P.hN) (P.K + 1) h0 s) : IsStA P nk nG bk bH s h0 := by
  refine ⟨hs, hleg.2.1, ?_⟩
  have hK2 := hc.hK
  have hHC := hc.hHC
  have hKle := K_le hc
  have hHC2 := hc.hHC2
  have hK1 : 1 ≤ P.K := by omega
  have hverts : ∀ i, 1 ≤ i → i ≤ P.K → 0 ≤ h0 - vdisp (s.take i) := by
    intro i hi1 hi
    rw [← hs] at hleg hi
    exact legal_nonneg (by omega) hleg hi1 hi
  have hxs := vdisp_bounds s
  rw [hs] at hxs
  unfold headHA
  by_cases hn : h0 ≤ P.HC + P.K
  · -- a start near the top: the check `dfsHA` at `h0`
    have hd : dfsHA P nk nG bk bH h0 = true :=
      rangeAllA_of hc.dfsNear (by omega) (by push_cast; omega)
    exact start_of_dfsA hK1 hs hd hleg hverts (fun i m _ _ hE => Or.inl (by rw [offAt_nxtA]; exact hE))
  · -- a start far from the top: the check `dfsHA` at `bigH`, by translation
    have hwin : ∀ i m, 2 ≤ m → i + m ≤ P.K → ExclA P.hN (bigH - vdisp (s.take i)) ((s.drop i).take m) →
        ExA P.hN (offAt nxtA h0 s i) ((s.drop i).take m) := by
      intro i m _ him hE
      left
      rw [offAt_nxtA]
      rw [hc.hN0] at hE ⊢
      have hwl : (((s.drop i).take m).length : ℤ) ≤ m := by exact_mod_cast List.length_take_le _ _
      have hxi := vdisp_take_bounds s i
      refine (exclA_shift ?_ ?_).mp hE
      · unfold bigH; omega
      · omega
    have := start_of_dfsA hK1 hs hc.dfsBig hleg (fun i _ hi => by
      have := vdisp_take_bounds s i; unfold bigH; omega) hwin
    rw [potA_far P nk nG bk bH (by unfold bigH; omega)] at this
    rw [potA_far P nk nG bk bH (by omega)]
    exact this

/-! ## The start sums -/

namespace CertSoundA

theorem getElem!_modify_add {a : Array ℕ} {k t : ℕ} (c : ℕ) (ht : t < a.size) :
    (a.modify k (· + c))[t]! = a[t]! + (if k = t then c else 0) := by
  rw [getElem!_pos (a.modify k (· + c)) t (by simpa using ht), getElem!_pos a t ht, Array.getElem_modify]
  split_ifs <;> simp

/-- A fold that adds `inc i t` at every slot `t`. -/
theorem foldl_pointwise (F : Array ℕ → ℕ → Array ℕ) (inc : ℕ → ℕ → ℕ) (N : ℕ)
    (hF : ∀ acc i, acc.size = N → (F acc i).size = N ∧ ∀ t < N, (F acc i)[t]! = acc[t]! + inc i t) :
    ∀ (L : List ℕ) (acc : Array ℕ), acc.size = N →
      (L.foldl F acc).size = N ∧ ∀ t < N, (L.foldl F acc)[t]! = acc[t]! + (L.map (fun i => inc i t)).sum
  | [], acc, hs => by simp [hs]
  | i :: L, acc, hs => by
    simp only [List.foldl]
    obtain ⟨h1, h2⟩ := hF acc i hs
    obtain ⟨h3, h4⟩ := foldl_pointwise F inc N hF L (F acc i) h1
    refine ⟨h3, fun t ht => ?_⟩
    rw [h4 t ht, h2 t ht, List.map_cons, List.sum_cons]
    ring

theorem sum_range_indicator (n t : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map (fun i => if i = t then f i else 0)).sum = if t < n then f t else 0 := by
  rw [list_sum_range, Finset.sum_ite_eq']
  simp only [Finset.mem_range]

theorem wtTable_get (P : ParamsA) {c : ℕ} (hc : c ≤ P.K) : (wtTable P)[c]! = P.wE ^ (P.K - c) * P.wC ^ c := by
  unfold wtTable
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

/-- The number of C-labels of a pattern. -/
def nCA (σ : List (ℕ × Bool)) : ℕ := (σ.filter (fun x => x.2)).length

/-- The first-vertex height of the near record `i`. -/
def h0N (P : ParamsA) (nk : Array ℕ) (i : ℕ) : ℤ := ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!)

/-- The start term of the near record `i`. -/
def vN (P : ParamsA) (nk nG : Array ℕ) (i : ℕ) : ℕ := (wtTable P)[nCA (decodeA P.K nk[i]!)]! * nG[i]!

/-- The start term of the bulk record `j`. -/
def vB (P : ParamsA) (bk bH : Array ℕ) (j : ℕ) : ℕ := (wtTable P)[nCA (decodeA P.K bk[j]!)]! * bH[j]!

/-- What the near record `i` adds to the start sum of slot `t`. -/
def incN (P : ParamsA) (nk nG : Array ℕ) (i t : ℕ) : ℕ :=
  if 0 ≤ h0N P nk i ∧ h0N P nk i < ((P.HC + P.K + 1 : ℕ) : ℤ) ∧ (h0N P nk i).toNat = t then vN P nk nG i else 0

/-- What the bulk record `j` adds to the start sum of slot `t`. -/
def incB (P : ParamsA) (bk bH : Array ℕ) (j t : ℕ) : ℕ :=
  (if P.HC + P.K + 1 = t then vB P bk bH j else 0) +
    (if t < P.HC + P.K + 1 ∧ ¬ ((t : ℤ) - vdisp (decodeA P.K bk[j]!) < P.HC) then vB P bk bH j else 0)

theorem startSumsA_spec (P : ParamsA) (nk nG bk bH : Array ℕ) :
    (startSumsA P nk nG bk bH).size = P.HC + P.K + 2 ∧ ∀ t < P.HC + P.K + 2,
      (startSumsA P nk nG bk bH)[t]! =
        ∑ i ∈ Finset.range nk.size, incN P nk nG i t + ∑ j ∈ Finset.range bk.size, incB P bk bH j t := by
  unfold startSumsA
  dsimp only
  set n := P.HC + P.K + 1 with hn
  -- the near records
  have hA := foldl_pointwise (fun acc i =>
      if 0 ≤ ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) ∧
          ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) < (n : ℤ) then
        acc.modify (((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!)).toNat
          (· + (wtTable P)[(List.filter (fun x => x.2) (decodeA P.K nk[i]!)).length]! * nG[i]!)
      else acc) (incN P nk nG) (n + 1) ?_ (List.range nk.size) (Array.replicate (n + 1) 0) (by simp)
  · obtain ⟨hA1, hA2⟩ := hA
    -- the bulk records
    have hB := foldl_pointwise (fun acc j =>
        List.foldl (fun acc (h0 : ℕ) =>
          if (h0 : ℤ) - vdisp (decodeA P.K bk[j]!) < (P.HC : ℤ) then acc
          else acc.modify h0 (· + (wtTable P)[(List.filter (fun x => x.2) (decodeA P.K bk[j]!)).length]! * bH[j]!))
          (acc.modify n (· + (wtTable P)[(List.filter (fun x => x.2) (decodeA P.K bk[j]!)).length]! * bH[j]!))
          (List.range n)) (incB P bk bH) (n + 1) ?_ (List.range bk.size) _ hA1
    · obtain ⟨hB1, hB2⟩ := hB
      refine ⟨by rw [hB1], fun t ht => ?_⟩
      rw [hB2 t ht, hA2 t ht, list_sum_range, list_sum_range]
      have h0 : (Array.replicate (n + 1) (0 : ℕ))[t]! = 0 := by
        rw [getElem!_pos _ _ (by simp; omega)]
        simp
      rw [h0, zero_add]
    · intro acc j hs
      set v := (wtTable P)[(List.filter (fun x => x.2) (decodeA P.K bk[j]!)).length]! * bH[j]! with hv
      have hs' : (acc.modify n (· + v)).size = n + 1 := by simp [hs]
      have hI := foldl_pointwise (fun acc (h0 : ℕ) =>
          if (h0 : ℤ) - vdisp (decodeA P.K bk[j]!) < (P.HC : ℤ) then acc else acc.modify h0 (· + v))
        (fun h0 t => if h0 = t then (if (h0 : ℤ) - vdisp (decodeA P.K bk[j]!) < (P.HC : ℤ) then 0 else v) else 0)
        (n + 1) ?_ (List.range n) _ hs'
      · obtain ⟨hI1, hI2⟩ := hI
        refine ⟨hI1, fun t ht => ?_⟩
        rw [hI2 t ht, getElem!_modify_add v (by omega), sum_range_indicator]
        unfold incB vB nCA
        rw [← hv, ← hn]
        split_ifs <;> omega
      · intro acc' h0 hs''
        by_cases hc : (h0 : ℤ) - vdisp (decodeA P.K bk[j]!) < (P.HC : ℤ)
        · simp only [hc, ↓reduceIte]
          exact ⟨hs'', fun t _ => by split_ifs <;> simp⟩
        · simp only [hc, ↓reduceIte]
          refine ⟨by simp [hs''], fun t ht => ?_⟩
          rw [getElem!_modify_add v (by omega)]
  · intro acc i hs
    by_cases hc : 0 ≤ ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) ∧
        ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) < (n : ℤ)
    · simp only [hc, and_self, ↓reduceIte]
      refine ⟨by simp [hs], fun t ht => ?_⟩
      rw [getElem!_modify_add _ (by omega)]
      unfold incN vN h0N nCA
      rw [← hn]
      simp only [hc.1, hc.2, true_and]
    · simp only [hc, ↓reduceIte]
      refine ⟨hs, fun t _ => ?_⟩
      unfold incN h0N
      rw [← hn]
      have : ¬ (0 ≤ ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) ∧
          ((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!) < (n : ℤ) ∧
          (((heightOf P.K nk[i]! : ℕ) : ℤ) + vdisp (decodeA P.K nk[i]!)).toNat = t) :=
        fun h => hc ⟨h.1, h.2.1⟩
      simp only [this, ↓reduceIte, add_zero]

/-- The weight of a pattern scaled by `Q^K`. -/
def wtNA (P : ParamsA) (σ : List (ℕ × Bool)) : ℕ := P.wE ^ (P.K - nCA σ) * P.wC ^ nCA σ

end CertSoundA

open scoped Classical in
theorem certA_startSum (hc : CertOKA P nk nG bk bH) {h0 : ℤ} (hh : 0 ≤ h0) :
    ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 *
      ∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
        wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofA P nk nG bk bH s h0 : ℝ) ≤
      ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
  have hHC := hc.hHC
  have hHC2 := hc.hHC2
  have hKle := K_le hc
  obtain ⟨hS1, hS2⟩ := startSumsA_spec P nk nG bk bH
  -- the slot of the start
  let t : ℕ := if h0 ≤ P.HC + P.K then h0.toNat else P.HC + P.K + 1
  have ht : t < P.HC + P.K + 2 := by
    simp only [t]
    split_ifs <;> omega
  have hst : (P.wE + P.wC) ^ 2 * (startSumsA P nk nG bk bH)[t]! * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2) := by
    have h := hc.start
    unfold startOKA at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
    have := h.2 t (by omega)
    rw [getElem!_pos _ _ (by omega)]
    exact this
  -- (1) the bound in integers, state by state
  have hnat : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
      wtNA P s * HofA P nk nG bk bH s h0 ≤ (startSumsA P nk nG bk bH)[t]! := by
    rw [hS2 t ht, ← Finset.sum_filter_add_sum_filter_not _ (fun s => headHA s h0 < P.HC)]
    apply add_le_add
    · -- near heads: the near records
      apply Finset.sum_le_sum_of_injOn (fun s => (lookup nk (ckeyA P.K s (headHA s h0).toNat)).getD 0)
      · intro s hs u hu hsu
        simp only [Finset.mem_coe, Finset.mem_filter] at hs hu
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨⟨-, huS⟩, hun⟩ := hu
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        obtain ⟨hulen, hudir, hup⟩ := huS
        have hs0 : 0 ≤ headHA s h0 := by
          by_contra hneg
          rw [potA_neg P nk nG bk bH (by omega)] at hsp
          exact absurd hsp (by simp)
        have hu0 : 0 ≤ headHA u h0 := by
          by_contra hneg
          rw [potA_neg P nk nG bk bH (by omega)] at hup
          exact absurd hup (by simp)
        rw [potA_near P nk nG bk bH hs0 hsn, Option.isSome_map] at hsp
        rw [potA_near P nk nG bk bH hu0 hun, Option.isSome_map] at hup
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hup
        simp only [hj, hj', Option.getD_some] at hsu
        subst hsu
        have h1 := (lookup_some hj).2
        have h2 := (lookup_some hj').2
        rw [← decodeA_ckeyA hslen hsdir (headHA s h0).toNat, ← h1, h2, decodeA_ckeyA hulen hudir]
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, hsp⟩ := hsS
        have hs0 : 0 ≤ headHA s h0 := by
          by_contra hneg
          rw [potA_neg P nk nG bk bH (by omega)] at hsp
          exact absurd hsp (by simp)
        rw [potA_near P nk nG bk bH hs0 hsn, Option.isSome_map] at hsp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        simp only [hj, Option.getD_some, Finset.mem_range]
        exact (lookup_some hj).1
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        have hs0 : 0 ≤ headHA s h0 := by
          by_contra hneg
          rw [potA_neg P nk nG bk bH (by omega)] at hsp
          exact absurd hsp (by simp)
        have hsp' := hsp
        rw [potA_near P nk nG bk bH hs0 hsn, Option.isSome_map] at hsp'
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp'
        have hk := (lookup_some hj).2
        simp only [hj, Option.getD_some]
        have hxs := vdisp_bounds s
        rw [hslen] at hxs
        have hh0 : h0N P nk j = h0 := by
          unfold h0N
          rw [hk, decodeA_ckeyA hslen hsdir, heightOf_ckeyA hslen, Int.toNat_of_nonneg hs0]
          unfold headHA
          ring
        have hnear : h0 ≤ P.HC + P.K := by unfold headHA at hsn; omega
        have htn : h0.toNat = t := by
          simp only [t, hnear, ↓reduceIte]
        have hcond : 0 ≤ h0 ∧ h0 < ((P.HC + P.K + 1 : ℕ) : ℤ) ∧ h0.toNat = t := ⟨hh, by push_cast; omega, htn⟩
        unfold incN
        rw [hh0]
        simp only [hcond, and_self, ↓reduceIte]
        apply le_of_eq
        unfold vN wtNA
        rw [hk, decodeA_ckeyA hslen hsdir, wtTable_get P (by unfold nCA; rw [← hslen]; exact List.length_filter_le _ _)]
        congr 1
        unfold HofA
        rw [potA_near P nk nG bk bH hs0 hsn, hj]
        rfl
      · intro _ _ _
        exact Nat.zero_le _
    · -- far heads: the bulk records
      apply Finset.sum_le_sum_of_injOn (fun s => (lookup bk (ckeyA P.K s 0)).getD 0)
      · intro s hs u hu hsu
        simp only [Finset.mem_coe, Finset.mem_filter] at hs hu
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨⟨-, huS⟩, hun⟩ := hu
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        obtain ⟨hulen, hudir, hup⟩ := huS
        rw [potA_far P nk nG bk bH (by omega), Option.isSome_map] at hsp
        rw [potA_far P nk nG bk bH (by omega), Option.isSome_map] at hup
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hup
        simp only [hj, hj', Option.getD_some] at hsu
        subst hsu
        have h1 := (lookup_some hj).2
        have h2 := (lookup_some hj').2
        rw [← decodeA_ckeyA hslen hsdir 0, ← h1, h2, decodeA_ckeyA hulen hudir]
      · intro j hj
        simp only [Finset.mem_image, Finset.mem_filter] at hj
        obtain ⟨s, ⟨⟨-, hsS⟩, hsn⟩, rfl⟩ := hj
        obtain ⟨-, -, hsp⟩ := hsS
        rw [potA_far P nk nG bk bH (by omega), Option.isSome_map] at hsp
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp
        simp only [hj, Option.getD_some, Finset.mem_range]
        exact (lookup_some hj).1
      · intro s hs
        simp only [Finset.mem_filter] at hs
        obtain ⟨⟨-, hsS⟩, hsn⟩ := hs
        obtain ⟨hslen, hsdir, hsp⟩ := hsS
        have hsp' := hsp
        rw [potA_far P nk nG bk bH (by omega), Option.isSome_map] at hsp'
        obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsp'
        have hk := (lookup_some hj).2
        simp only [hj, Option.getD_some]
        have hxs := vdisp_bounds s
        rw [hslen] at hxs
        have hterm : wtNA P s * HofA P nk nG bk bH s h0 = vB P bk bH j := by
          unfold vB wtNA
          rw [hk, decodeA_ckeyA hslen hsdir,
            wtTable_get P (by unfold nCA; rw [← hslen]; exact List.length_filter_le _ _)]
          congr 1
          unfold HofA
          rw [potA_far P nk nG bk bH (by omega), hj]
          rfl
        rw [hterm]
        unfold incB
        rw [hk, decodeA_ckeyA hslen hsdir]
        unfold headHA at hsn
        simp only [t]
        split_ifs <;> omega
      · intro _ _ _
        exact Nat.zero_le _
  -- (2) in reals
  have hQr : (0 : ℝ) < P.Q := by exact_mod_cast hc.hQ
  have hKr : (0 : ℝ) < P.K0d := by exact_mod_cast hc.hK0d
  have hreal : ∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
      wtW ((P.wE : ℝ) / P.Q) ((P.wC : ℝ) / P.Q) s * (HofA P nk nG bk bH s h0 : ℝ) =
      ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
        wtNA P s * HofA P nk nG bk bH s h0 : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    have hlen : s.length = P.K := (Finset.mem_filter.mp hs).2.1
    have hcK : nCA s ≤ P.K := by unfold nCA; rw [← hlen]; exact List.length_filter_le _ _
    rw [wtW_eq, hlen]
    unfold wtNA
    unfold nCA at hcK ⊢
    push_cast
    rw [div_pow, div_pow]
    have hQK : (P.Q : ℝ) ^ P.K =
        (P.Q : ℝ) ^ (P.K - (s.filter (fun x => x.2)).length) * (P.Q : ℝ) ^ (s.filter (fun x => x.2)).length := by
      rw [← pow_add, Nat.sub_add_cancel hcK]
    rw [hQK]
    field_simp
  have hst_r : ((P.wE : ℝ) + P.wC) ^ 2 * ((startSumsA P nk nG bk bH)[t]! : ℝ) * P.K0d ≤
      P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) := by exact_mod_cast hst
  have hnat_r : ((∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
      wtNA P s * HofA P nk nG bk bH s h0 : ℕ) : ℝ) ≤ ((startSumsA P nk nG bk bH)[t]! : ℝ) := by
    exact_mod_cast hnat
  rw [hreal]
  calc ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 *
        (((∑ s ∈ (pats 2 P.K).filter (fun s => IsStA P nk nG bk bH s h0),
          wtNA P s * HofA P nk nG bk bH s h0 : ℕ) : ℝ) / (P.Q : ℝ) ^ P.K)
      ≤ ((P.wE : ℝ) / P.Q + (P.wC : ℝ) / P.Q) ^ 2 *
          (((startSumsA P nk nG bk bH)[t]! : ℝ) / (P.Q : ℝ) ^ P.K) := by
        gcongr
    _ = ((P.wE : ℝ) + P.wC) ^ 2 * ((startSumsA P nk nG bk bH)[t]! : ℝ) / (P.Q : ℝ) ^ (P.K + 2) := by
        field_simp
        ring
    _ ≤ ((P.K0n : ℝ) / P.K0d) * P.Hmin := by
        rw [div_le_iff₀ (by positivity), show (P.K0n : ℝ) / P.K0d * P.Hmin * (P.Q : ℝ) ^ (P.K + 2) =
          (P.K0n * P.Hmin * (P.Q : ℝ) ^ (P.K + 2)) / P.K0d by ring, le_div_iff₀ hKr]
        exact hst_r

end QEC
