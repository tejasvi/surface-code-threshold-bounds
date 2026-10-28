import QECML.S3.Connectivity

/-!
# Regions of components are connected

`box c r`: the checks of the blocks at block distance at most `r` from `c` (a rectangle of checks, clipped to the
code); it is connected (`box_conn`) by monotone paths. `region K r`: the union of the boxes of the blocks of `K`.
If any two blocks of `K` are joined by a chain in `K` with steps of block distance at most `a ≤ 2r`, the region is
connected (`region_conn`): the boxes of consecutive blocks share the corner check of a middle block. This is the
statement "the region of an `a`-connected component is a connected union of blocks" of the decoder's proof.
-/

open Finset

namespace QECML

namespace S3Geom

variable {G : S3Geom}

theorem reach_symm {U : Set G.V} {u v : G.V} (h : Relation.ReflTransGen (G.stepU U) u v) :
    Relation.ReflTransGen (G.stepU U) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head ⟨hbc.2.1, hbc.1, G.adj_symm hbc.2.2⟩ ih

theorem reach_mono {U U' : Set G.V} (hUU : U ⊆ U') {u v : G.V} (h : Relation.ReflTransGen (G.stepU U) u v) :
    Relation.ReflTransGen (G.stepU U') u v := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih ⟨hUU hbc.1, hUU hbc.2.1, hbc.2.2⟩

variable (G)

/-- The checks of the blocks at block distance at most `r` from `c`. -/
def box (c : G.Block) (r : ℕ) : Set G.V := {v | G.blockDist (G.blockOf v) c ≤ r}

/-- The checks of the blocks at block distance at most `r` from a block of `K`. -/
def region (K : Set G.Block) (r : ℕ) : Set G.V := {v | ∃ c ∈ K, G.blockDist (G.blockOf v) c ≤ r}

theorem box_subset_region {K : Set G.Block} {c : G.Block} (hc : c ∈ K) (r : ℕ) : G.box c r ⊆ G.region K r :=
  fun _ hv => ⟨c, hc, hv⟩

variable {G}

theorem mem_box_iff (c : G.Block) (r : ℕ) (v : G.V) :
    v ∈ G.box c r ↔ ndist (v.1.val / G.L) c.1.val ≤ r ∧ ndist (v.2.val / G.L) c.2.val ≤ r := by
  simp only [box, Set.mem_ofPred_eq, blockDist, blockOf, bcol, brow, max_le_iff]

theorem ndist_convex {p m q a r : ℕ} (hpm : p ≤ m) (hmq : m ≤ q) (hp : ndist p a ≤ r) (hq : ndist q a ≤ r) :
    ndist m a ≤ r := by
  simp only [ndist] at *
  omega

/-- Horizontal neighbours are adjacent. -/
theorem adj_right (x : Fin (G.w + 1)) (hx : x.val < G.w) (y : Fin (G.h + 1)) :
    G.adj (x, y) (⟨x.val + 1, by omega⟩, y) := by
  refine ⟨PEdge.hor ⟨x.val, hx⟩ y, ?_, ?_⟩
  · simp only [PEdge.ends]
    rfl
  · intro h
    have := congrArg (fun v : G.V => v.1.val) h
    simp at this

/-- Vertical neighbours are adjacent. -/
theorem adj_up (x : Fin (G.w + 1)) (y : Fin (G.h + 1)) (hy : y.val < G.h) :
    G.adj (x, y) (x, ⟨y.val + 1, by omega⟩) := by
  refine ⟨PEdge.ver x ⟨y.val, hy⟩, ?_, ?_⟩
  · simp only [PEdge.ends]
    rfl
  · intro h
    have := congrArg (fun v : G.V => v.2.val) h
    simp at this

theorem box_row_path {c : G.Block} {r : ℕ} (y : Fin (G.h + 1)) :
    ∀ (d : ℕ) (x : Fin (G.w + 1)) (hxd : x.val + d ≤ G.w), (x, y) ∈ G.box c r →
      ((⟨x.val + d, by omega⟩ : Fin (G.w + 1)), y) ∈ G.box c r →
      Relation.ReflTransGen (G.stepU (G.box c r)) (x, y) (⟨x.val + d, by omega⟩, y) := by
  intro d
  induction d with
  | zero =>
    intro x _ _ _
    have : (⟨x.val + 0, by omega⟩ : Fin (G.w + 1)) = x := Fin.ext rfl
    rw [this]
  | succ d ih =>
    intro x hxd hx hx'
    have hx1 : x.val < G.w := by omega
    set x1 : Fin (G.w + 1) := ⟨x.val + 1, by omega⟩ with hx1def
    have hmem : (x1, y) ∈ G.box c r := by
      rw [mem_box_iff] at hx hx' ⊢
      refine ⟨ndist_convex (Nat.div_le_div_right (by simp [x1])) (Nat.div_le_div_right ?_) hx.1 hx'.1, hx.2⟩
      simp only [x1]
      omega
    have h2 := ih x1 (by simp only [x1]; omega) hmem (by
      have : (⟨x1.val + d, by simp only [x1]; omega⟩ : Fin (G.w + 1)) = ⟨x.val + (d + 1), by omega⟩ :=
        Fin.ext (by simp only [x1]; omega)
      rw [this]
      exact hx')
    have : (⟨x1.val + d, by simp only [x1]; omega⟩ : Fin (G.w + 1)) = ⟨x.val + (d + 1), by omega⟩ :=
      Fin.ext (by simp only [x1]; omega)
    rw [this] at h2
    exact .head ⟨hx, hmem, adj_right x hx1 y⟩ h2

theorem box_col_path {c : G.Block} {r : ℕ} (x : Fin (G.w + 1)) :
    ∀ (d : ℕ) (y : Fin (G.h + 1)) (hyd : y.val + d ≤ G.h), (x, y) ∈ G.box c r →
      (x, (⟨y.val + d, by omega⟩ : Fin (G.h + 1))) ∈ G.box c r →
      Relation.ReflTransGen (G.stepU (G.box c r)) (x, y) (x, ⟨y.val + d, by omega⟩) := by
  intro d
  induction d with
  | zero =>
    intro y _ _ _
    have : (⟨y.val + 0, by omega⟩ : Fin (G.h + 1)) = y := Fin.ext rfl
    rw [this]
  | succ d ih =>
    intro y hyd hy hy'
    have hy1 : y.val < G.h := by omega
    set y1 : Fin (G.h + 1) := ⟨y.val + 1, by omega⟩ with hy1def
    have hmem : (x, y1) ∈ G.box c r := by
      rw [mem_box_iff] at hy hy' ⊢
      refine ⟨hy.1, ndist_convex (Nat.div_le_div_right (by simp [y1])) (Nat.div_le_div_right ?_) hy.2 hy'.2⟩
      simp only [y1]
      omega
    have h2 := ih y1 (by simp only [y1]; omega) hmem (by
      have : (⟨y1.val + d, by simp only [y1]; omega⟩ : Fin (G.h + 1)) = ⟨y.val + (d + 1), by omega⟩ :=
        Fin.ext (by simp only [y1]; omega)
      rw [this]
      exact hy')
    have : (⟨y1.val + d, by simp only [y1]; omega⟩ : Fin (G.h + 1)) = ⟨y.val + (d + 1), by omega⟩ :=
      Fin.ext (by simp only [y1]; omega)
    rw [this] at h2
    exact .head ⟨hy, hmem, adj_up x y hy1⟩ h2

/-- Paths along a row of a box, in either direction. -/
theorem box_row_reach {c : G.Block} {r : ℕ} {x x' : Fin (G.w + 1)} {y : Fin (G.h + 1)}
    (hx : (x, y) ∈ G.box c r) (hx' : (x', y) ∈ G.box c r) :
    Relation.ReflTransGen (G.stepU (G.box c r)) (x, y) (x', y) := by
  rcases le_total x.val x'.val with hle | hle
  · have := box_row_path y (x'.val - x.val) x (by omega) hx (by
      have : (⟨x.val + (x'.val - x.val), by omega⟩ : Fin (G.w + 1)) = x' := Fin.ext (by simp; omega)
      rw [this]; exact hx')
    have e : (⟨x.val + (x'.val - x.val), by omega⟩ : Fin (G.w + 1)) = x' := Fin.ext (by simp; omega)
    rw [e] at this
    exact this
  · have := box_row_path y (x.val - x'.val) x' (by omega) hx' (by
      have : (⟨x'.val + (x.val - x'.val), by omega⟩ : Fin (G.w + 1)) = x := Fin.ext (by simp; omega)
      rw [this]; exact hx)
    have e : (⟨x'.val + (x.val - x'.val), by omega⟩ : Fin (G.w + 1)) = x := Fin.ext (by simp; omega)
    rw [e] at this
    exact reach_symm this

/-- Paths along a column of a box, in either direction. -/
theorem box_col_reach {c : G.Block} {r : ℕ} {x : Fin (G.w + 1)} {y y' : Fin (G.h + 1)}
    (hy : (x, y) ∈ G.box c r) (hy' : (x, y') ∈ G.box c r) :
    Relation.ReflTransGen (G.stepU (G.box c r)) (x, y) (x, y') := by
  rcases le_total y.val y'.val with hle | hle
  · have := box_col_path x (y'.val - y.val) y (by omega) hy (by
      have : (⟨y.val + (y'.val - y.val), by omega⟩ : Fin (G.h + 1)) = y' := Fin.ext (by simp; omega)
      rw [this]; exact hy')
    have e : (⟨y.val + (y'.val - y.val), by omega⟩ : Fin (G.h + 1)) = y' := Fin.ext (by simp; omega)
    rw [e] at this
    exact this
  · have := box_col_path x (y.val - y'.val) y' (by omega) hy' (by
      have : (⟨y'.val + (y.val - y'.val), by omega⟩ : Fin (G.h + 1)) = y := Fin.ext (by simp; omega)
      rw [this]; exact hy)
    have e : (⟨y'.val + (y.val - y'.val), by omega⟩ : Fin (G.h + 1)) = y := Fin.ext (by simp; omega)
    rw [e] at this
    exact reach_symm this

/-- A box is connected. -/
theorem box_conn (c : G.Block) (r : ℕ) : G.Conn (G.box c r) := by
  intro u hu v hv
  obtain ⟨ux, uy⟩ := u
  obtain ⟨vx, vy⟩ := v
  have hm : (vx, uy) ∈ G.box c r := by
    rw [mem_box_iff] at hu hv ⊢
    exact ⟨hv.1, hu.2⟩
  exact (box_row_reach hu hm).trans (box_col_reach hm hv)

/-- The middle block of two blocks. -/
def midBlock (c c' : G.Block) : G.Block :=
  (⟨(c.1.val + c'.1.val) / 2, by omega⟩, ⟨(c.2.val + c'.2.val) / 2, by omega⟩)

theorem blockDist_midBlock {c c' : G.Block} {a r : ℕ} (har : a ≤ 2 * r) (hcc : G.blockDist c c' ≤ a) :
    G.blockDist (midBlock c c') c ≤ r ∧ G.blockDist (midBlock c c') c' ≤ r := by
  simp only [blockDist, midBlock, ndist, max_le_iff] at hcc ⊢
  omega

/-- The lower-left check of a block. -/
def corner (m : G.Block) : G.V :=
  (⟨m.1.val * G.L, by
      have h := Nat.mul_le_mul_right G.L (Nat.succ_le_of_lt m.1.isLt)
      have := G.w_succ
      rw [Nat.succ_mul] at h
      have := G.hL
      omega⟩,
    ⟨m.2.val * G.L, by
      have h := Nat.mul_le_mul_right G.L (Nat.succ_le_of_lt m.2.isLt)
      have := G.h_succ
      rw [Nat.succ_mul] at h
      have := G.hL
      omega⟩)

theorem blockOf_corner (m : G.Block) : G.blockOf (corner m) = m := by
  have hL := G.hL
  ext <;> simp [blockOf, bcol, brow, corner, Nat.mul_div_cancel _ (show 0 < G.L by omega)]

/-- The region of a block set whose blocks are chained by steps of block distance `≤ a ≤ 2r` is connected. -/
theorem region_conn {K : Set G.Block} {a r : ℕ} (har : a ≤ 2 * r)
    (hK : ∀ c1 ∈ K, ∀ c2 ∈ K,
      Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) c1 c2) :
    G.Conn (G.region K r) := by
  intro u hu v hv
  obtain ⟨c1, hc1, hu1⟩ := hu
  obtain ⟨c2, hc2, hv2⟩ := hv
  have key : ∀ k, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ G.blockDist x y ≤ a) c1 k →
      k ∈ K → ∀ z ∈ G.box k r, Relation.ReflTransGen (G.stepU (G.region K r)) u z := by
    intro k hk
    induction hk with
    | refl =>
      intro _ z hz
      exact reach_mono (G.box_subset_region hc1 r) (box_conn c1 r u hu1 z hz)
    | @tail b k' _ hstep ih =>
      intro hk' z hz
      obtain ⟨hb, _, hbk⟩ := hstep
      have hmid := blockDist_midBlock har hbk
      have hm1 : corner (midBlock b k') ∈ G.box b r := by
        show G.blockDist (G.blockOf (corner (midBlock b k'))) b ≤ r
        rw [blockOf_corner]
        exact hmid.1
      have hm2 : corner (midBlock b k') ∈ G.box k' r := by
        show G.blockDist (G.blockOf (corner (midBlock b k'))) k' ≤ r
        rw [blockOf_corner]
        exact hmid.2
      exact (ih hb _ hm1).trans (reach_mono (G.box_subset_region hk' r) (box_conn k' r _ hm2 z hz))
  exact key c2 (hK c1 hc1 c2 hc2) hc2 v hv2

end S3Geom

end QECML
