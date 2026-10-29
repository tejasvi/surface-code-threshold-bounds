import QECD1.Conn3

/-!
# Regions of components are connected (3D)

The 3D analogue of the 2D `S3/Regions`.

* `box3 c r`: the checks of the blocks within block distance `r` of `c` (a box of checks, clipped to the code). It is
  connected (`box3_conn`): a monotone path changes `t`, then `x`, then `y` (`line_reach`).
* `region3 K r`: the union of the boxes of the blocks of `K`. If the blocks of `K` contain checks and any two of them
  are joined by a chain in `K` with steps of block distance at most `a ≤ 2r`, the region is connected
  (`region3_conn`): the boxes of consecutive blocks share the corner check of a middle block.
-/

open Finset

namespace QECD1

variable {T w h : ℕ}

theorem reach3_symm {U : Set (PVert3 T w h)} {u v : PVert3 T w h} (huv : Relation.ReflTransGen (stepU3 U) u v) :
    Relation.ReflTransGen (stepU3 U) v u := by
  induction huv with
  | refl => exact .refl
  | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, adj3_symm hbc.2.2⟩ ih

theorem reach3_mono {U U' : Set (PVert3 T w h)} (hUU : U ⊆ U') {u v : PVert3 T w h}
    (huv : Relation.ReflTransGen (stepU3 U) u v) : Relation.ReflTransGen (stepU3 U') u v := by
  induction huv with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih ⟨hUU hbc.1, hUU hbc.2.1, hbc.2.2⟩

/-- A path along a line of checks: if consecutive points of the line are adjacent and the points from `a` to `b` lie
in `U`, then `line a` and `line b` are joined inside `U`. -/
theorem line_reach {U : Set (PVert3 T w h)} {n : ℕ} (line : ℕ → PVert3 T w h)
    (hadj : ∀ j, j < n → adj3 (line j) (line (j + 1))) {a : ℕ} :
    ∀ d, a + d ≤ n → (∀ j, a ≤ j → j ≤ a + d → line j ∈ U) →
      Relation.ReflTransGen (stepU3 U) (line a) (line (a + d)) := by
  intro d
  induction d with
  | zero => intro _ _; exact .refl
  | succ d ih =>
    intro hd hU
    have h1 := ih (by omega) fun j hj1 hj2 => hU j hj1 (by omega)
    exact h1.tail ⟨hU (a + d) (by omega) (by omega), hU (a + d + 1) (by omega) (by omega), hadj (a + d) (by omega)⟩

theorem line_reach' {U : Set (PVert3 T w h)} {n : ℕ} (line : ℕ → PVert3 T w h)
    (hadj : ∀ j, j < n → adj3 (line j) (line (j + 1))) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (hU : ∀ j, min a b ≤ j → j ≤ max a b → line j ∈ U) : Relation.ReflTransGen (stepU3 U) (line a) (line b) := by
  rcases le_total a b with hab | hab
  · have h := line_reach line hadj (a := a) (b - a) (by omega) fun j hj1 hj2 => hU j (by omega) (by omega)
    rwa [show a + (b - a) = b by omega] at h
  · have h := line_reach line hadj (a := b) (a - b) (by omega) fun j hj1 hj2 => hU j (by omega) (by omega)
    rw [show b + (a - b) = a by omega] at h
    exact reach3_symm h

/-- The checks of the blocks at block distance at most `r` from `c`. -/
def box3 (c : V3) (r : ℕ) : Set (PVert3 T w h) := {v | dist3 (blockOf3 v) c ≤ r}

/-- The checks of the blocks at block distance at most `r` from a block of `K`. -/
def region3 (K : Finset V3) (r : ℕ) : Set (PVert3 T w h) := {v | ∃ c ∈ K, dist3 (blockOf3 v) c ≤ r}

theorem box3_subset_region3 {K : Finset V3} {c : V3} (hc : c ∈ K) (r : ℕ) :
    (box3 c r : Set (PVert3 T w h)) ⊆ region3 K r :=
  fun _ hv => ⟨c, hc, hv⟩

theorem mem_box3_iff (c : V3) (r : ℕ) (v : PVert3 T w h) :
    v ∈ (box3 c r : Set (PVert3 T w h)) ↔ ((v.1.val : ℤ) / 35 - c.1).natAbs ≤ r ∧
      ((v.2.1.val : ℤ) / 35 - c.2.1).natAbs ≤ r ∧ ((v.2.2.val : ℤ) / 35 - c.2.2).natAbs ≤ r := by
  show dist3 (blockOf3 v) c ≤ r ↔ _
  simp only [dist3, linf, blockOf3, blockOf, PVert3.toV3, Prod.fst_sub, Prod.snd_sub, max_le_iff]

/-- The line in the time direction through `(·, x, y)`. -/
def tline (x : Fin (w + 1)) (y : Fin (h + 1)) (j : ℕ) : PVert3 T w h := (⟨min j T, by omega⟩, x, y)

/-- The line in the x direction through `(t, ·, y)`. -/
def xline (t : Fin (T + 1)) (y : Fin (h + 1)) (j : ℕ) : PVert3 T w h := (t, ⟨min j w, by omega⟩, y)

/-- The line in the y direction through `(t, x, ·)`. -/
def yline (t : Fin (T + 1)) (x : Fin (w + 1)) (j : ℕ) : PVert3 T w h := (t, x, ⟨min j h, by omega⟩)

theorem tline_adj (x : Fin (w + 1)) (y : Fin (h + 1)) (j : ℕ) (hj : j < T) :
    adj3 (tline (T := T) x y j) (tline x y (j + 1)) := by
  have e1 : tline (T := T) x y j = ((⟨j, hj⟩ : Fin T).castSucc, x, y) :=
    Prod.ext (Fin.ext (show min j T = j by omega)) rfl
  have e2 : tline (T := T) x y (j + 1) = ((⟨j, hj⟩ : Fin T).succ, x, y) :=
    Prod.ext (Fin.ext (show min (j + 1) T = j + 1 by omega)) rfl
  rw [e1, e2]
  refine ⟨PEdge3.time ⟨j, hj⟩ x y, rfl, fun heq => ?_⟩
  have := congrArg (fun v : PVert3 T w h => v.1.val) heq
  simp at this

theorem xline_adj (t : Fin (T + 1)) (y : Fin (h + 1)) (j : ℕ) (hj : j < w) :
    adj3 (xline (w := w) t y j) (xline t y (j + 1)) := by
  have e1 : xline (w := w) t y j = (t, (⟨j, hj⟩ : Fin w).castSucc, y) :=
    Prod.ext rfl (Prod.ext (Fin.ext (show min j w = j by omega)) rfl)
  have e2 : xline (w := w) t y (j + 1) = (t, (⟨j, hj⟩ : Fin w).succ, y) :=
    Prod.ext rfl (Prod.ext (Fin.ext (show min (j + 1) w = j + 1 by omega)) rfl)
  rw [e1, e2]
  refine ⟨PEdge3.hor t ⟨j, hj⟩ y, rfl, fun heq => ?_⟩
  have := congrArg (fun v : PVert3 T w h => v.2.1.val) heq
  simp at this

theorem yline_adj (t : Fin (T + 1)) (x : Fin (w + 1)) (j : ℕ) (hj : j < h) :
    adj3 (yline (h := h) t x j) (yline t x (j + 1)) := by
  have e1 : yline (h := h) t x j = (t, x, (⟨j, hj⟩ : Fin h).castSucc) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min j h = j by omega)))
  have e2 : yline (h := h) t x (j + 1) = (t, x, (⟨j, hj⟩ : Fin h).succ) :=
    Prod.ext rfl (Prod.ext rfl (Fin.ext (show min (j + 1) h = j + 1 by omega)))
  rw [e1, e2]
  refine ⟨PEdge3.ver t x ⟨j, hj⟩, rfl, fun heq => ?_⟩
  have := congrArg (fun v : PVert3 T w h => v.2.2.val) heq
  simp at this

theorem div_between {a b j r : ℕ} {c : ℤ} (hj1 : min a b ≤ j) (hj2 : j ≤ max a b)
    (ha : ((a : ℤ) / 35 - c).natAbs ≤ r) (hb : ((b : ℤ) / 35 - c).natAbs ≤ r) : ((j : ℤ) / 35 - c).natAbs ≤ r := by
  rcases le_total a b with hab | hab
  · have e1 : (a : ℤ) / 35 ≤ (j : ℤ) / 35 := Int.ediv_le_ediv (by norm_num) (by omega)
    have e2 : (j : ℤ) / 35 ≤ (b : ℤ) / 35 := Int.ediv_le_ediv (by norm_num) (by omega)
    omega
  · have e1 : (b : ℤ) / 35 ≤ (j : ℤ) / 35 := Int.ediv_le_ediv (by norm_num) (by omega)
    have e2 : (j : ℤ) / 35 ≤ (a : ℤ) / 35 := Int.ediv_le_ediv (by norm_num) (by omega)
    omega

/-- **A box is connected.** -/
theorem box3_conn (c : V3) (r : ℕ) : Conn3 (box3 c r : Set (PVert3 T w h)) := by
  intro u hu v hv
  obtain ⟨ut, ux, uy⟩ := u
  obtain ⟨vt, vx, vy⟩ := v
  rw [mem_box3_iff] at hu hv
  simp only at hu hv
  have ht1 := ut.isLt
  have ht2 := vt.isLt
  have hx1 := ux.isLt
  have hx2 := vx.isLt
  have hy1 := uy.isLt
  have hy2 := vy.isLt
  -- move t, then x, then y
  have s1 : Relation.ReflTransGen (stepU3 (box3 c r : Set (PVert3 T w h))) (ut, ux, uy) (vt, ux, uy) := by
    have hut : ut.val ≤ T := by omega
    have hvt : vt.val ≤ T := by omega
    have hr := line_reach' (U := (box3 c r : Set (PVert3 T w h))) (tline (T := T) ux uy) (tline_adj ux uy) hut hvt
      fun j hj1 hj2 => by
        rw [mem_box3_iff]
        have hjT : min j T = j := by omega
        simp only [tline, hjT]
        exact ⟨div_between hj1 hj2 hu.1 hv.1, hu.2.1, hu.2.2⟩
    have e1 : tline (T := T) ux uy ut.val = (ut, ux, uy) := Prod.ext (Fin.ext (show min ut.val T = ut.val by omega)) rfl
    have e2 : tline (T := T) ux uy vt.val = (vt, ux, uy) := Prod.ext (Fin.ext (show min vt.val T = vt.val by omega)) rfl
    rwa [e1, e2] at hr
  have s2 : Relation.ReflTransGen (stepU3 (box3 c r : Set (PVert3 T w h))) (vt, ux, uy) (vt, vx, uy) := by
    have hux : ux.val ≤ w := by omega
    have hvx : vx.val ≤ w := by omega
    have hr := line_reach' (U := (box3 c r : Set (PVert3 T w h))) (xline (w := w) vt uy) (xline_adj vt uy) hux hvx
      fun j hj1 hj2 => by
        rw [mem_box3_iff]
        have hjw : min j w = j := by omega
        simp only [xline, hjw]
        exact ⟨hv.1, div_between hj1 hj2 hu.2.1 hv.2.1, hu.2.2⟩
    have e1 : xline (w := w) vt uy ux.val = (vt, ux, uy) :=
      Prod.ext rfl (Prod.ext (Fin.ext (show min ux.val w = ux.val by omega)) rfl)
    have e2 : xline (w := w) vt uy vx.val = (vt, vx, uy) :=
      Prod.ext rfl (Prod.ext (Fin.ext (show min vx.val w = vx.val by omega)) rfl)
    rwa [e1, e2] at hr
  have s3 : Relation.ReflTransGen (stepU3 (box3 c r : Set (PVert3 T w h))) (vt, vx, uy) (vt, vx, vy) := by
    have huy : uy.val ≤ h := by omega
    have hvy : vy.val ≤ h := by omega
    have hr := line_reach' (U := (box3 c r : Set (PVert3 T w h))) (yline (h := h) vt vx) (yline_adj vt vx) huy hvy
      fun j hj1 hj2 => by
        rw [mem_box3_iff]
        have hjh : min j h = j := by omega
        simp only [yline, hjh]
        exact ⟨hv.1, hv.2.1, div_between hj1 hj2 hu.2.2 hv.2.2⟩
    have e1 : yline (h := h) vt vx uy.val = (vt, vx, uy) :=
      Prod.ext rfl (Prod.ext rfl (Fin.ext (show min uy.val h = uy.val by omega)))
    have e2 : yline (h := h) vt vx vy.val = (vt, vx, vy) :=
      Prod.ext rfl (Prod.ext rfl (Fin.ext (show min vy.val h = vy.val by omega)))
    rwa [e1, e2] at hr
  exact (s1.trans s2).trans s3

/-- The middle block of two blocks. -/
def midBlock (c c' : V3) : V3 := ((c.1 + c'.1) / 2, (c.2.1 + c'.2.1) / 2, (c.2.2 + c'.2.2) / 2)

theorem dist3_midBlock {c c' : V3} {a r : ℕ} (har : a ≤ 2 * r) (hcc : dist3 c c' ≤ a) :
    dist3 (midBlock c c') c ≤ r ∧ dist3 (midBlock c c') c' ≤ r := by
  simp only [dist3, linf, midBlock, Prod.fst_sub, Prod.snd_sub, max_le_iff] at hcc ⊢
  omega

/-- The first check of a block of the code. -/
def corner3 (m : V3) (hm : ∃ v : PVert3 T w h, blockOf3 v = m) : PVert3 T w h :=
  (⟨(m.1 * 35).toNat, by
      obtain ⟨v, hv⟩ := hm
      have := v.1.isLt
      have h1 : m.1 = (v.1.val : ℤ) / 35 := by rw [← hv]; rfl
      omega⟩,
    ⟨(m.2.1 * 35).toNat, by
      obtain ⟨v, hv⟩ := hm
      have := v.2.1.isLt
      have h1 : m.2.1 = (v.2.1.val : ℤ) / 35 := by rw [← hv]; rfl
      omega⟩,
    ⟨(m.2.2 * 35).toNat, by
      obtain ⟨v, hv⟩ := hm
      have := v.2.2.isLt
      have h1 : m.2.2 = (v.2.2.val : ℤ) / 35 := by rw [← hv]; rfl
      omega⟩)

theorem blockOf3_corner3 (m : V3) (hm : ∃ v : PVert3 T w h, blockOf3 v = m) : blockOf3 (corner3 m hm) = m := by
  obtain ⟨v, hv⟩ := hm
  have h1 : m.1 = (v.1.val : ℤ) / 35 := by rw [← hv]; rfl
  have h2 : m.2.1 = (v.2.1.val : ℤ) / 35 := by rw [← hv]; rfl
  have h3 : m.2.2 = (v.2.2.val : ℤ) / 35 := by rw [← hv]; rfl
  simp only [blockOf3, blockOf, PVert3.toV3, corner3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> omega

/-- The middle block of two blocks of the code is a block of the code. -/
theorem midBlock_mem {c c' : V3} (hc : ∃ v : PVert3 T w h, blockOf3 v = c) (hc' : ∃ v : PVert3 T w h, blockOf3 v = c') :
    ∃ v : PVert3 T w h, blockOf3 v = midBlock c c' := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨u', hu'⟩ := hc'
  have h1 : c.1 = (u.1.val : ℤ) / 35 := by rw [← hu]; rfl
  have h2 : c.2.1 = (u.2.1.val : ℤ) / 35 := by rw [← hu]; rfl
  have h3 : c.2.2 = (u.2.2.val : ℤ) / 35 := by rw [← hu]; rfl
  have h1' : c'.1 = (u'.1.val : ℤ) / 35 := by rw [← hu']; rfl
  have h2' : c'.2.1 = (u'.2.1.val : ℤ) / 35 := by rw [← hu']; rfl
  have h3' : c'.2.2 = (u'.2.2.val : ℤ) / 35 := by rw [← hu']; rfl
  have g1 := u.1.isLt
  have g2 := u.2.1.isLt
  have g3 := u.2.2.isLt
  have g1' := u'.1.isLt
  have g2' := u'.2.1.isLt
  have g3' := u'.2.2.isLt
  refine ⟨(⟨(((c.1 + c'.1) / 2) * 35).toNat, by omega⟩, ⟨(((c.2.1 + c'.2.1) / 2) * 35).toNat, by omega⟩,
    ⟨(((c.2.2 + c'.2.2) / 2) * 35).toNat, by omega⟩), ?_⟩
  simp only [blockOf3, blockOf, PVert3.toV3, midBlock]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> omega

/-- **The region of a block set chained by steps of block distance `≤ a ≤ 2r` is connected**, if its blocks contain
checks. -/
theorem region3_conn {K : Finset V3} {a r : ℕ} (har : a ≤ 2 * r) (hKc : ∀ c ∈ K, ∃ v : PVert3 T w h, blockOf3 v = c)
    (hK : ∀ c1 ∈ K, ∀ c2 ∈ K,
      Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ dist3 x y ≤ a) c1 c2) :
    Conn3 (region3 K r : Set (PVert3 T w h)) := by
  intro u hu v hv
  obtain ⟨c1, hc1, hu1⟩ := hu
  obtain ⟨c2, hc2, hv2⟩ := hv
  have key : ∀ k, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ dist3 x y ≤ a) c1 k →
      k ∈ K → ∀ z ∈ (box3 k r : Set (PVert3 T w h)), Relation.ReflTransGen (stepU3 (region3 K r)) u z := by
    intro k hk
    induction hk with
    | refl =>
      intro _ z hz
      exact reach3_mono (box3_subset_region3 hc1 r) (box3_conn c1 r u hu1 z hz)
    | @tail b k' _ hstep ih =>
      intro hk' z hz
      obtain ⟨hb, _, hbk⟩ := hstep
      have hmid := dist3_midBlock har hbk
      have hmem := midBlock_mem (hKc b hb) (hKc k' hk')
      have hm1 : corner3 (midBlock b k') hmem ∈ (box3 b r : Set (PVert3 T w h)) := by
        show dist3 (blockOf3 (corner3 (midBlock b k') hmem)) b ≤ r
        rw [blockOf3_corner3]
        exact hmid.1
      have hm2 : corner3 (midBlock b k') hmem ∈ (box3 k' r : Set (PVert3 T w h)) := by
        show dist3 (blockOf3 (corner3 (midBlock b k') hmem)) k' ≤ r
        rw [blockOf3_corner3]
        exact hmid.2
      exact (ih hb _ hm1).trans (reach3_mono (box3_subset_region3 hk' r) (box3_conn k' r _ hm2 z hz))
  exact key c2 (hK c1 hc1 c2 hc2) hc2 v hv2

end QECD1
