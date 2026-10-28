import QECML.TwoD.T2Path
import QECML.S3.Embed

/-!
# The metric input (M) of the T2 count: weights of edge sets against ℓ1 distances

* `sum_psyn_left`, `sum_psyn_below` (cut handshake): for an edge set without half-edges, the parity of its odd checks
  in the columns `≤ k` (rows `≤ k`) is the parity of its horizontal (vertical) edges crossing the cut.
* `exists_hor_cross`, `exists_ver_cross`: an edge set without half-edges whose odd checks are `{u, v}` crosses every
  vertical cut between `u` and `v` and every horizontal cut between them.
* `wsum_ge_l1`: with bulk weights at least `wmin ≥ 0`, its weight is at least `wmin · |u - v|_1`.
-/

open Finset Classical

namespace QECML

namespace PlanarMetric

variable {w h : ℕ}

/-- The column of a horizontal edge (`0` for the others). -/
def hcol : PEdge w h → ℕ
  | .hor x _ => x.val
  | _ => 0

/-- The row of a vertical edge (`0` for the others). -/
def vrow : PEdge w h → ℕ
  | .ver _ y => y.val
  | _ => 0

/-- The edge is horizontal. -/
def isHor : PEdge w h → Prop
  | .hor _ _ => True
  | _ => False

/-- The edge is vertical. -/
def isVer : PEdge w h → Prop
  | .ver _ _ => True
  | _ => False

theorem count_ends (X : PEdge w h → ZMod 2) (P : PVert w h → Prop) [DecidablePred P] (f : PEdge w h) :
    (∑ v, if P v then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) =
      X f * (((f.ends.filter P).card : ℕ) : ZMod 2) := by
  rw [mul_comm]
  have : ∀ v, (if P v then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) =
      (if v ∈ f.ends.filter P then (1 : ZMod 2) else 0) * X f := by
    intro v
    by_cases hv : P v <;> by_cases hvf : v ∈ f.ends <;> simp [hv, hvf]
  rw [Finset.sum_congr rfl fun v _ => this v, ← Finset.sum_mul, Finset.sum_boole]
  congr 3
  ext x
  simp

theorem sum_psyn_P (X : PEdge w h → ZMod 2) (P : PVert w h → Prop) [DecidablePred P] :
    ∑ v, (if P v then psyn w h X v else 0) = ∑ f, X f * (((f.ends.filter P).card : ℕ) : ZMod 2) := by
  calc ∑ v, (if P v then psyn w h X v else 0)
      = ∑ v, ∑ f, (if P v then (if v ∈ f.ends then (1 : ZMod 2) else 0) * X f else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [psyn_apply]
        split_ifs <;> simp
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun f _ => count_ends X P f

theorem two_eq_zero : ((2 : ℕ) : ZMod 2) = 0 := by decide

/-- **Cut handshake (vertical cut)**: for an edge set without half-edges, the odd checks in the columns `≤ k` have the
parity of the horizontal edges between columns `k` and `k + 1`. -/
theorem sum_psyn_left (X : PEdge w h → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0) (k : ℕ)
    (hk : k < w) :
    ∑ v : PVert w h, (if v.1.val ≤ k then psyn w h X v else 0) = ∑ y : Fin (h + 1), X (.hor ⟨k, hk⟩ y) := by
  rw [sum_psyn_P, sum_pedge]
  have hver : ∀ p : Fin (w + 1) × Fin h, X (.ver p.1 p.2) *
      ((((PEdge.ver p.1 p.2).ends.filter (fun v : PVert w h => v.1.val ≤ k)).card : ℕ) : ZMod 2) = 0 := by
    intro p
    simp only [PEdge.ends]
    by_cases hx : p.1.val ≤ k
    · rw [Finset.filter_true_of_mem (by simp [hx]), Finset.card_pair (by
        simp [Prod.ext_iff, Fin.ext_iff])]
      rw [two_eq_zero, mul_zero]
    · rw [Finset.filter_false_of_mem (by simp; omega), Finset.card_empty]
      simp
  have hbot : ∀ x : Fin (w + 1), X (.bot x) *
      ((((PEdge.bot x : PEdge w h).ends.filter (fun v : PVert w h => v.1.val ≤ k)).card : ℕ) : ZMod 2) = 0 :=
    fun x => by rw [(hX x).1, zero_mul]
  have htop : ∀ x : Fin (w + 1), X (.top x) *
      ((((PEdge.top x : PEdge w h).ends.filter (fun v : PVert w h => v.1.val ≤ k)).card : ℕ) : ZMod 2) = 0 :=
    fun x => by rw [(hX x).2, zero_mul]
  rw [Finset.sum_eq_zero fun p _ => hver p, Finset.sum_eq_zero fun x _ => hbot x,
    Finset.sum_eq_zero fun x _ => htop x, add_zero, add_zero, add_zero]
  -- the horizontal part: only column `k` survives
  have hhor : ∀ p : Fin w × Fin (h + 1), X (.hor p.1 p.2) *
      ((((PEdge.hor p.1 p.2).ends.filter (fun v : PVert w h => v.1.val ≤ k)).card : ℕ) : ZMod 2) =
        if p.1.val = k then X (.hor p.1 p.2) else 0 := by
    intro p
    simp only [PEdge.ends]
    have hne : ((p.1.castSucc, p.2) : PVert w h) ≠ (p.1.succ, p.2) := by
      simp [Prod.ext_iff, Fin.ext_iff]
    by_cases h1 : p.1.val + 1 ≤ k
    · rw [Finset.filter_true_of_mem (by simp; omega), Finset.card_pair hne, two_eq_zero, mul_zero]
      rw [ite_eq_right (by omega)]
    · by_cases h2 : p.1.val = k
      · have : (({(p.1.castSucc, p.2), (p.1.succ, p.2)} : Finset (PVert w h)).filter
            (fun v : PVert w h => v.1.val ≤ k)) = {(p.1.castSucc, p.2)} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨h | h, hv⟩
            · exact h
            · subst h
              simp at hv
              omega
          · rintro rfl
            simp
            omega
        rw [this, Finset.card_singleton, ite_eq_left h2]
        simp
      · rw [Finset.filter_false_of_mem (by simp; omega), Finset.card_empty, ite_eq_right h2]
        simp
  rw [Finset.sum_congr rfl fun p _ => hhor p, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin w)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [ite_eq_right (fun h => hb (Fin.ext h))]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Cut handshake (horizontal cut)**: for an edge set without half-edges, the odd checks in the rows `≤ k` have the
parity of the vertical edges between rows `k` and `k + 1`. -/
theorem sum_psyn_below (X : PEdge w h → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0) (k : ℕ)
    (hk : k < h) :
    ∑ v : PVert w h, (if v.2.val ≤ k then psyn w h X v else 0) = ∑ x : Fin (w + 1), X (.ver x ⟨k, hk⟩) := by
  rw [sum_psyn_P, sum_pedge]
  have hhor : ∀ p : Fin w × Fin (h + 1), X (.hor p.1 p.2) *
      ((((PEdge.hor p.1 p.2).ends.filter (fun v : PVert w h => v.2.val ≤ k)).card : ℕ) : ZMod 2) = 0 := by
    intro p
    simp only [PEdge.ends]
    by_cases hy : p.2.val ≤ k
    · rw [Finset.filter_true_of_mem (by simp [hy]), Finset.card_pair (by
        simp [Prod.ext_iff, Fin.ext_iff])]
      rw [two_eq_zero, mul_zero]
    · rw [Finset.filter_false_of_mem (by simp; omega), Finset.card_empty]
      simp
  have hbot : ∀ x : Fin (w + 1), X (.bot x) *
      ((((PEdge.bot x : PEdge w h).ends.filter (fun v : PVert w h => v.2.val ≤ k)).card : ℕ) : ZMod 2) = 0 :=
    fun x => by rw [(hX x).1, zero_mul]
  have htop : ∀ x : Fin (w + 1), X (.top x) *
      ((((PEdge.top x : PEdge w h).ends.filter (fun v : PVert w h => v.2.val ≤ k)).card : ℕ) : ZMod 2) = 0 :=
    fun x => by rw [(hX x).2, zero_mul]
  rw [Finset.sum_eq_zero fun p _ => hhor p, Finset.sum_eq_zero fun x _ => hbot x,
    Finset.sum_eq_zero fun x _ => htop x, zero_add, add_zero, add_zero]
  have hver : ∀ p : Fin (w + 1) × Fin h, X (.ver p.1 p.2) *
      ((((PEdge.ver p.1 p.2).ends.filter (fun v : PVert w h => v.2.val ≤ k)).card : ℕ) : ZMod 2) =
        if p.2.val = k then X (.ver p.1 p.2) else 0 := by
    intro p
    simp only [PEdge.ends]
    have hne : ((p.1, p.2.castSucc) : PVert w h) ≠ (p.1, p.2.succ) := by
      simp [Prod.ext_iff, Fin.ext_iff]
    by_cases h1 : p.2.val + 1 ≤ k
    · rw [Finset.filter_true_of_mem (by simp; omega), Finset.card_pair hne, two_eq_zero, mul_zero]
      rw [ite_eq_right (by omega)]
    · by_cases h2 : p.2.val = k
      · have : (({(p.1, p.2.castSucc), (p.1, p.2.succ)} : Finset (PVert w h)).filter
            (fun v : PVert w h => v.2.val ≤ k)) = {(p.1, p.2.castSucc)} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨h | h, hv⟩
            · exact h
            · subst h
              simp at hv
              omega
          · rintro rfl
            simp
            omega
        rw [this, Finset.card_singleton, ite_eq_left h2]
        simp
      · rw [Finset.filter_false_of_mem (by simp; omega), Finset.card_empty, ite_eq_right h2]
        simp
  rw [Finset.sum_congr rfl fun p _ => hver p, Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin h)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (fun h => hb (Fin.ext h))]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_single_pair_P {u v : PVert w h} (P : PVert w h → Prop) [DecidablePred P] :
    ∑ z : PVert w h, (if P z then (Pi.single u 1 + Pi.single v 1 : PVert w h → ZMod 2) z else 0) =
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

/-- An edge set without half-edges with odd checks `{u, v}` crosses every vertical cut between them. -/
theorem exists_hor_cross (X : PEdge w h → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0)
    {u v : PVert w h} (hpsyn : psyn w h X = Pi.single u 1 + Pi.single v 1) {k : ℕ}
    (hk1 : min u.1.val v.1.val ≤ k) (hk2 : k < max u.1.val v.1.val) :
    ∃ y : Fin (h + 1), X (.hor ⟨k, by have := u.1.isLt; have := v.1.isLt; omega⟩ y) ≠ 0 := by
  have hk : k < w := by have := u.1.isLt; have := v.1.isLt; omega
  have hsum := sum_psyn_left X hX k hk
  rw [hpsyn, sum_single_pair_P] at hsum
  have hone : (if u.1.val ≤ k then (1 : ZMod 2) else 0) + (if v.1.val ≤ k then 1 else 0) = 1 := by
    by_cases hu : u.1.val ≤ k <;> by_cases hv : v.1.val ≤ k <;> simp [hu, hv] <;> omega
  rw [hone] at hsum
  exact Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero) |>.imp fun y hy => hy.2

/-- An edge set without half-edges with odd checks `{u, v}` crosses every horizontal cut between them. -/
theorem exists_ver_cross (X : PEdge w h → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0)
    {u v : PVert w h} (hpsyn : psyn w h X = Pi.single u 1 + Pi.single v 1) {k : ℕ}
    (hk1 : min u.2.val v.2.val ≤ k) (hk2 : k < max u.2.val v.2.val) :
    ∃ x : Fin (w + 1), X (.ver x ⟨k, by have := u.2.isLt; have := v.2.isLt; omega⟩) ≠ 0 := by
  have hk : k < h := by have := u.2.isLt; have := v.2.isLt; omega
  have hsum := sum_psyn_below X hX k hk
  rw [hpsyn, sum_single_pair_P] at hsum
  have hone : (if u.2.val ≤ k then (1 : ZMod 2) else 0) + (if v.2.val ≤ k then 1 else 0) = 1 := by
    by_cases hu : u.2.val ≤ k <;> by_cases hv : v.2.val ≤ k <;> simp [hu, hv] <;> omega
  rw [hone] at hsum
  exact Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hsum]; exact one_ne_zero) |>.imp fun x hx => hx.2

/-- **Weight against ℓ1 distance**: with bulk weights at least `wmin ≥ 0` (and all weights `≥ 0`), an edge set without
half-edges whose odd checks are `{u, v}` weighs at least `wmin · |u - v|_1`. -/
theorem wsum_ge_l1 {wt : PEdge w h → ℝ} {wmin : ℝ} (hmin0 : 0 ≤ wmin) (hwt0 : ∀ e, 0 ≤ wt e)
    (hwt : ∀ e, S3Geom.isBulk e → wmin ≤ wt e) (X : PEdge w h → ZMod 2)
    (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0) {u v : PVert w h}
    (hpsyn : psyn w h X = Pi.single u 1 + Pi.single v 1) :
    wmin * ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) ≤ ∑ e, if X e ≠ 0 then wt e else 0 := by
  set Sh := univ.filter (fun e : PEdge w h => X e ≠ 0 ∧ isHor e) with hSh
  set Sv := univ.filter (fun e : PEdge w h => X e ≠ 0 ∧ isVer e) with hSv
  -- every vertical cut between u and v is crossed
  have hcardh : ndist u.1.val v.1.val ≤ Sh.card := by
    have hsub : Finset.Ico (min u.1.val v.1.val) (max u.1.val v.1.val) ⊆ Sh.image hcol := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨y, hy⟩ := exists_hor_cross X hX hpsyn hk.1 hk.2
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy, trivial⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := Sh) (f := hcol)
    rw [Nat.card_Ico] at h1
    simp only [ndist]
    omega
  have hcardv : ndist u.2.val v.2.val ≤ Sv.card := by
    have hsub : Finset.Ico (min u.2.val v.2.val) (max u.2.val v.2.val) ⊆ Sv.image vrow := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      obtain ⟨x, hx⟩ := exists_ver_cross X hX hpsyn hk.1 hk.2
      exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, trivial⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := Sv) (f := vrow)
    rw [Nat.card_Ico] at h1
    simp only [ndist]
    omega
  -- the two sets are disjoint parts of the support
  have hdisj : Disjoint Sh Sv := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [hSh, Finset.mem_filter] at he
    rw [hSv, Finset.mem_filter] at he'
    rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
    · exact he'.2.2
    · exact he.2.2
    · exact he.2.2
    · exact he.2.2
  have hsupp : Sh ∪ Sv ⊆ univ.filter (fun e : PEdge w h => X e ≠ 0) := by
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2.1⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2.1⟩
  have hbulk : ∀ e ∈ Sh ∪ Sv, wmin ≤ wt e := by
    intro e he
    refine hwt e ?_
    rcases Finset.mem_union.1 he with he | he
    · have hh := (Finset.mem_filter.1 he).2.2
      rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
      · trivial
      · trivial
      · exact absurd hh id
      · exact absurd hh id
    · have hv := (Finset.mem_filter.1 he).2.2
      rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
      · trivial
      · trivial
      · exact absurd hv id
      · exact absurd hv id
  calc wmin * ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ)
      ≤ wmin * ((Sh ∪ Sv).card : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hmin0
        rw [Finset.card_union_of_disjoint hdisj]
        exact_mod_cast Nat.add_le_add hcardh hcardv
    _ = ((Sh ∪ Sv).card : ℝ) * wmin := mul_comm _ _
    _ ≤ ∑ e ∈ Sh ∪ Sv, wt e := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ hbulk
    _ ≤ ∑ e ∈ univ.filter (fun e : PEdge w h => X e ≠ 0), wt e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsupp fun e _ _ => hwt0 e
    _ = ∑ e, if X e ≠ 0 then wt e else 0 := by rw [Finset.sum_filter]

theorem psyn_single_edge (e : PEdge w h) (v : PVert w h) :
    psyn w h (Pi.single e 1) v = if v ∈ e.ends then 1 else 0 := by
  rw [psyn_apply, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [hfe]
  · simp

theorem psyn_single_hor (x : Fin w) (y : Fin (h + 1)) :
    psyn w h (Pi.single (PEdge.hor x y) 1) = Pi.single (x.castSucc, y) 1 + Pi.single (x.succ, y) 1 := by
  funext v
  rw [psyn_single_edge, Pi.add_apply]
  have hne : ((x.castSucc, y) : PVert w h) ≠ (x.succ, y) := by simp [Prod.ext_iff, Fin.ext_iff]
  simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : v = (x.castSucc, y)
  · subst h1
    simp [hne]
  · by_cases h2 : v = (x.succ, y)
    · subst h2
      simp [Ne.symm hne]
    · simp [h1, h2]

theorem psyn_single_ver (x : Fin (w + 1)) (y : Fin h) :
    psyn w h (Pi.single (PEdge.ver x y) 1) = Pi.single (x, y.castSucc) 1 + Pi.single (x, y.succ) 1 := by
  funext v
  rw [psyn_single_edge, Pi.add_apply]
  have hne : ((x, y.castSucc) : PVert w h) ≠ (x, y.succ) := by simp [Prod.ext_iff, Fin.ext_iff]
  simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : v = (x, y.castSucc)
  · subst h1
    simp [hne]
  · by_cases h2 : v = (x, y.succ)
    · subst h2
      simp [Ne.symm hne]
    · simp [h1, h2]

/-- The horizontal segment of row `y` from column `a`, of length `n`. -/
noncomputable def hsegN (y : Fin (h + 1)) (a : ℕ) : ℕ → PEdge w h → ZMod 2
  | 0 => 0
  | n + 1 => hsegN y a n + if hn : a + n < w then Pi.single (PEdge.hor ⟨a + n, hn⟩ y) 1 else 0

/-- The vertical segment of column `x` from row `a`, of length `n`. -/
noncomputable def vsegN (x : Fin (w + 1)) (a : ℕ) : ℕ → PEdge w h → ZMod 2
  | 0 => 0
  | n + 1 => vsegN x a n + if hn : a + n < h then Pi.single (PEdge.ver x ⟨a + n, hn⟩) 1 else 0

theorem psyn_hsegN (y : Fin (h + 1)) (a : ℕ) : ∀ n (ha : a + n ≤ w),
    psyn w h (hsegN y a n) = Pi.single (⟨a, by omega⟩, y) 1 + Pi.single (⟨a + n, by omega⟩, y) 1
  | 0, ha => by
    simp only [hsegN, map_zero, add_zero]
    funext v
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [zmod2_add_self]
  | n + 1, ha => by
    simp only [hsegN, map_add, dite_eq_left (show a + n < w by omega), psyn_hsegN y a n (by omega),
      psyn_single_hor]
    have e1 : ((⟨a + n, by omega⟩ : Fin w).castSucc : Fin (w + 1)) = ⟨a + n, by omega⟩ := rfl
    have e2 : ((⟨a + n, by omega⟩ : Fin w).succ : Fin (w + 1)) = ⟨a + (n + 1), by omega⟩ := by
      ext
      simp
      omega
    rw [e1, e2]
    funext v
    simp only [Pi.add_apply]
    linear_combination (zmod2_add_self ((Pi.single ((⟨a + n, by omega⟩ : Fin (w + 1)), y) (1 : ZMod 2) :
      PVert w h → ZMod 2) v))

theorem psyn_vsegN (x : Fin (w + 1)) (a : ℕ) : ∀ n (ha : a + n ≤ h),
    psyn w h (vsegN x a n) = Pi.single (x, (⟨a, by omega⟩ : Fin (h + 1))) 1 +
      Pi.single (x, (⟨a + n, by omega⟩ : Fin (h + 1))) 1
  | 0, ha => by
    simp only [vsegN, map_zero, add_zero]
    funext v
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [zmod2_add_self]
  | n + 1, ha => by
    simp only [vsegN, map_add, dite_eq_left (show a + n < h by omega), psyn_vsegN x a n (by omega),
      psyn_single_ver]
    have e1 : ((⟨a + n, by omega⟩ : Fin h).castSucc : Fin (h + 1)) = ⟨a + n, by omega⟩ := rfl
    have e2 : ((⟨a + n, by omega⟩ : Fin h).succ : Fin (h + 1)) = ⟨a + (n + 1), by omega⟩ := by
      ext
      simp
      omega
    rw [e1, e2]
    funext v
    simp only [Pi.add_apply]
    linear_combination (zmod2_add_self ((Pi.single (x, (⟨a + n, by omega⟩ : Fin (h + 1))) (1 : ZMod 2) :
      PVert w h → ZMod 2) v))

/-- The weight of an edge set (the sum of `wt` over its support). -/
noncomputable def wsumP (wt : PEdge w h → ℝ) (X : PEdge w h → ZMod 2) : ℝ := ∑ e, if X e ≠ 0 then wt e else 0

theorem wsumP_add_le {wt : PEdge w h → ℝ} (hwt : ∀ e, 0 ≤ wt e) (X Y : PEdge w h → ZMod 2) :
    wsumP wt (X + Y) ≤ wsumP wt X + wsumP wt Y := by
  unfold wsumP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hw := hwt e
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases (X e) with hx | hx <;> rcases zmod2_cases (Y e) with hy | hy
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy]
  · simp [Pi.add_apply, hx, hy, h11]
    linarith

theorem wsumP_single (wt : PEdge w h → ℝ) (e : PEdge w h) : wsumP wt (Pi.single e 1) = wt e := by
  unfold wsumP
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hf
    simp [hf]
  · simp

theorem wsumP_zero (wt : PEdge w h → ℝ) : wsumP wt 0 = 0 := by
  simp [wsumP]

theorem wsumP_hsegN_le {wt : PEdge w h → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, S3Geom.isBulk e → wt e ≤ wmax) (y : Fin (h + 1)) (a : ℕ) :
    ∀ n, wsumP wt (hsegN y a n) ≤ n * wmax
  | 0 => by simp [hsegN, wsumP_zero]
  | n + 1 => by
    simp only [hsegN]
    refine (wsumP_add_le hwt0 _ _).trans ?_
    have ih := wsumP_hsegN_le hwt0 hmax0 hwt y a n
    push_cast
    split_ifs with hn
    · rw [wsumP_single]
      have := hwt (.hor ⟨a + n, hn⟩ y) trivial
      linarith
    · rw [wsumP_zero]
      linarith

theorem wsumP_vsegN_le {wt : PEdge w h → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, S3Geom.isBulk e → wt e ≤ wmax) (x : Fin (w + 1)) (a : ℕ) :
    ∀ n, wsumP wt (vsegN x a n) ≤ n * wmax
  | 0 => by simp [vsegN, wsumP_zero]
  | n + 1 => by
    simp only [vsegN]
    refine (wsumP_add_le hwt0 _ _).trans ?_
    have ih := wsumP_vsegN_le hwt0 hmax0 hwt x a n
    push_cast
    split_ifs with hn
    · rw [wsumP_single]
      have := hwt (.ver x ⟨a + n, hn⟩) trivial
      linarith
    · rw [wsumP_zero]
      linarith

/-- **Staircase**: an edge set with odd checks `{u, v}` of weight at most `wmax · |u - v|_1`. -/
theorem exists_stair {wt : PEdge w h → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, S3Geom.isBulk e → wt e ≤ wmax) (u v : PVert w h) :
    ∃ X : PEdge w h → ZMod 2, psyn w h X = Pi.single u 1 + Pi.single v 1 ∧
      wsumP wt X ≤ ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) * wmax := by
  have hu1 := u.1.isLt
  have hv1 := v.1.isLt
  have hu2 := u.2.isLt
  have hv2 := v.2.isLt
  refine ⟨hsegN u.2 (min u.1.val v.1.val) (ndist u.1.val v.1.val) +
    vsegN v.1 (min u.2.val v.2.val) (ndist u.2.val v.2.val), ?_, ?_⟩
  · rw [map_add, psyn_hsegN u.2 _ _ (by simp only [ndist]; omega),
      psyn_vsegN v.1 _ _ (by simp only [ndist]; omega)]
    -- the endpoints of the two segments
    have hh : (Pi.single ((⟨min u.1.val v.1.val, by omega⟩ : Fin (w + 1)), u.2) (1 : ZMod 2) +
        Pi.single ((⟨min u.1.val v.1.val + ndist u.1.val v.1.val, by simp only [ndist]; omega⟩ : Fin (w + 1)), u.2) 1 :
          PVert w h → ZMod 2) = Pi.single u 1 + Pi.single (v.1, u.2) 1 := by
      by_cases huv : u.1.val ≤ v.1.val
      · have e1 : ((⟨min u.1.val v.1.val, by omega⟩ : Fin (w + 1)), u.2) = u :=
          Prod.ext (Fin.ext (by simp; omega)) rfl
        have e2 : ((⟨min u.1.val v.1.val + ndist u.1.val v.1.val, by simp only [ndist]; omega⟩ :
            Fin (w + 1)), u.2) = (v.1, u.2) := Prod.ext (Fin.ext (by simp [ndist]; omega)) rfl
        rw [e1, e2]
      · have e1 : ((⟨min u.1.val v.1.val, by omega⟩ : Fin (w + 1)), u.2) = (v.1, u.2) :=
          Prod.ext (Fin.ext (by simp; omega)) rfl
        have e2 : ((⟨min u.1.val v.1.val + ndist u.1.val v.1.val, by simp only [ndist]; omega⟩ :
            Fin (w + 1)), u.2) = u := Prod.ext (Fin.ext (by simp [ndist]; omega)) rfl
        rw [e1, e2, add_comm]
    have hv : (Pi.single (v.1, (⟨min u.2.val v.2.val, by omega⟩ : Fin (h + 1))) (1 : ZMod 2) +
        Pi.single (v.1, (⟨min u.2.val v.2.val + ndist u.2.val v.2.val, by simp only [ndist]; omega⟩ :
          Fin (h + 1))) 1 : PVert w h → ZMod 2) = Pi.single (v.1, u.2) 1 + Pi.single v 1 := by
      by_cases huv : u.2.val ≤ v.2.val
      · have e1 : (v.1, (⟨min u.2.val v.2.val, by omega⟩ : Fin (h + 1))) = (v.1, u.2) :=
          Prod.ext rfl (Fin.ext (by simp; omega))
        have e2 : (v.1, (⟨min u.2.val v.2.val + ndist u.2.val v.2.val, by simp only [ndist]; omega⟩ :
            Fin (h + 1))) = v := Prod.ext rfl (Fin.ext (by simp [ndist]; omega))
        rw [e1, e2]
      · have e1 : (v.1, (⟨min u.2.val v.2.val, by omega⟩ : Fin (h + 1))) = v :=
          Prod.ext rfl (Fin.ext (by simp; omega))
        have e2 : (v.1, (⟨min u.2.val v.2.val + ndist u.2.val v.2.val, by simp only [ndist]; omega⟩ :
            Fin (h + 1))) = (v.1, u.2) := Prod.ext rfl (Fin.ext (by simp [ndist]; omega))
        rw [e1, e2, add_comm]
    rw [hh, hv]
    funext z
    simp only [Pi.add_apply]
    linear_combination (zmod2_add_self ((Pi.single (v.1, u.2) (1 : ZMod 2) : PVert w h → ZMod 2) z))
  · refine (wsumP_add_le hwt0 _ _).trans ?_
    have h1 := wsumP_hsegN_le hwt0 hmax0 hwt u.2 (min u.1.val v.1.val) (ndist u.1.val v.1.val)
    have h2 := wsumP_vsegN_le hwt0 hmax0 hwt v.1 (min u.2.val v.2.val) (ndist u.2.val v.2.val)
    push_cast
    linarith

theorem psyn_single_bot (x : Fin (w + 1)) : psyn w h (Pi.single (PEdge.bot x) 1) = Pi.single (x, 0) 1 := by
  funext v
  rw [psyn_single_edge]
  simp only [PEdge.ends, Finset.mem_singleton]
  by_cases hv : v = (x, 0)
  · subst hv
    simp
  · simp [hv]

theorem psyn_single_top (x : Fin (w + 1)) :
    psyn w h (Pi.single (PEdge.top x) 1) = Pi.single (x, Fin.last h) 1 := by
  funext v
  rw [psyn_single_edge]
  simp only [PEdge.ends, Finset.mem_singleton]
  by_cases hv : v = (x, Fin.last h)
  · subst hv
    simp
  · simp [hv]

/-- **Leg to the bottom boundary**: an edge set with the single odd check `u`, of weight at most
`u_y · wmax + w_half`. -/
theorem exists_leg_bot {wt : PEdge w h → ℝ} {wmax wh : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, S3Geom.isBulk e → wt e ≤ wmax) (hwh : ∀ x, wt (.bot x) ≤ wh) (u : PVert w h) :
    ∃ X : PEdge w h → ZMod 2, psyn w h X = Pi.single u 1 ∧ wsumP wt X ≤ (u.2.val : ℝ) * wmax + wh := by
  have hu2 := u.2.isLt
  refine ⟨vsegN u.1 0 u.2.val + Pi.single (PEdge.bot u.1) 1, ?_, ?_⟩
  · rw [map_add, psyn_vsegN u.1 0 _ (by omega), psyn_single_bot]
    have e1 : (u.1, (⟨0, by omega⟩ : Fin (h + 1))) = (u.1, (0 : Fin (h + 1))) := rfl
    have e2 : (u.1, (⟨0 + u.2.val, by omega⟩ : Fin (h + 1))) = u := Prod.ext rfl (Fin.ext (by simp))
    rw [e1, e2]
    funext z
    simp only [Pi.add_apply]
    linear_combination (zmod2_add_self ((Pi.single (u.1, (0 : Fin (h + 1))) (1 : ZMod 2) :
      PVert w h → ZMod 2) z))
  · refine (wsumP_add_le hwt0 _ _).trans ?_
    rw [wsumP_single]
    have h1 := wsumP_vsegN_le hwt0 hmax0 hwt u.1 0 u.2.val
    have h2 := hwh u.1
    linarith

/-- **Leg to the top boundary**: an edge set with the single odd check `u`, of weight at most
`(h - u_y) · wmax + w_half`. -/
theorem exists_leg_top {wt : PEdge w h → ℝ} {wmax wh : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, S3Geom.isBulk e → wt e ≤ wmax) (hwh : ∀ x, wt (.top x) ≤ wh) (u : PVert w h) :
    ∃ X : PEdge w h → ZMod 2, psyn w h X = Pi.single u 1 ∧
      wsumP wt X ≤ ((h - u.2.val : ℕ) : ℝ) * wmax + wh := by
  have hu2 := u.2.isLt
  refine ⟨vsegN u.1 u.2.val (h - u.2.val) + Pi.single (PEdge.top u.1) 1, ?_, ?_⟩
  · rw [map_add, psyn_vsegN u.1 u.2.val _ (by omega), psyn_single_top]
    have e1 : (u.1, (⟨u.2.val, by omega⟩ : Fin (h + 1))) = u := Prod.ext rfl (Fin.ext rfl)
    have e2 : (u.1, (⟨u.2.val + (h - u.2.val), by omega⟩ : Fin (h + 1))) = (u.1, Fin.last h) :=
      Prod.ext rfl (Fin.ext (by simp; omega))
    rw [e1, e2]
    funext z
    simp only [Pi.add_apply]
    linear_combination (zmod2_add_self ((Pi.single (u.1, Fin.last h) (1 : ZMod 2) : PVert w h → ZMod 2) z))
  · refine (wsumP_add_le hwt0 _ _).trans ?_
    rw [wsumP_single]
    have h1 := wsumP_vsegN_le hwt0 hmax0 hwt u.1 u.2.val (h - u.2.val)
    have h2 := hwh u.1
    linarith

end PlanarMetric

namespace S3Geom

variable {G : S3Geom}

/-- **(M), lower bound**: a bulk edge set of `G` with odd checks `{u, v}` weighs at least `wmin · |u - v|_1`. -/
theorem wsum_ge_l1 {wt : G.Ed → ℝ} {wmin : ℝ} (hmin0 : 0 ≤ wmin) (hwt0 : ∀ e, 0 ≤ wt e)
    (hwt : ∀ e, isBulk e → wmin ≤ wt e) (X : G.Ed → ZMod 2) (hX : ∀ x, X (.bot x) = 0 ∧ X (.top x) = 0)
    {u v : G.V} (hpsyn : psyn G.w G.h X = Pi.single u 1 + Pi.single v 1) :
    wmin * ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) ≤ wsum wt X :=
  PlanarMetric.wsum_ge_l1 hmin0 hwt0 hwt X hX hpsyn

/-- **(M), upper bound**: the pair cost of `{u, v}` is at most `wmax · |u - v|_1`. -/
theorem pairCost_le_l1 {wt : G.Ed → ℝ} {wmax : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, isBulk e → wt e ≤ wmax) (u v : G.V) :
    pairCost wt (Pi.single u 1 + Pi.single v 1) ≤ ((ndist u.1.val v.1.val + ndist u.2.val v.2.val : ℕ) : ℝ) * wmax := by
  obtain ⟨X, hX, hw⟩ := PlanarMetric.exists_stair hwt0 hmax0 hwt u v
  exact (pairCost_le hX).trans hw

/-- The pair cost of a single check with the bottom boundary. -/
theorem pairCost_le_bot {wt : G.Ed → ℝ} {wmax wh : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, isBulk e → wt e ≤ wmax) (hwh : ∀ x, wt (.bot x) ≤ wh) (u : G.V) :
    pairCost wt (Pi.single u 1) ≤ (u.2.val : ℝ) * wmax + wh := by
  obtain ⟨X, hX, hw⟩ := PlanarMetric.exists_leg_bot hwt0 hmax0 hwt hwh u
  exact (pairCost_le hX).trans hw

/-- The pair cost of a single check with the top boundary. -/
theorem pairCost_le_top {wt : G.Ed → ℝ} {wmax wh : ℝ} (hwt0 : ∀ e, 0 ≤ wt e) (hmax0 : 0 ≤ wmax)
    (hwt : ∀ e, isBulk e → wt e ≤ wmax) (hwh : ∀ x, wt (.top x) ≤ wh) (u : G.V) :
    pairCost wt (Pi.single u 1) ≤ ((G.h - u.2.val : ℕ) : ℝ) * wmax + wh := by
  obtain ⟨X, hX, hw⟩ := PlanarMetric.exists_leg_top hwt0 hmax0 hwt hwh u
  exact (pairCost_le hX).trans hw

end S3Geom

end QECML
