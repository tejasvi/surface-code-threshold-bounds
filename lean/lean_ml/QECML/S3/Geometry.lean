import QECML.Independence

/-!
# Geometry of the windowed decoder S3

The code has `W = n_x L` columns and
`H = n_y L` rows of checks. Block `c = (a, b)` is the set of checks `[aL, aL + L) × [bL, bL + L)`; it owns the
edges whose left or lower endpoint lies in it (a half-edge belongs to the block of its check). The window `W_c` is
the set of checks within `ℓ∞` distance `R` of `c`, and `N_1(c)` is the set of blocks at block distance at most 1.

`Nbhd c` is the set of edges with an endpoint in the window of a block of `N_1(c)`; the bad event of `c` depends
only on the errors there (`QECML.S3.Events`). For `blockDist c c' ≥ D = 4 + ⌊2R/L⌋` the two edge sets are disjoint
(`nbhd_disjoint`), because `(D - 3) L > 2R`.
-/

namespace QECML

/-- Distance of `x` from the interval `[a, b]` of natural numbers. -/
def dist1 (x a b : ℕ) : ℕ := (a - x) + (x - b)

/-- `|a - b|` on natural numbers. -/
def ndist (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- Geometry of S3: block side `L`, window radius `R`, `n_x × n_y` blocks. -/
structure S3Geom where
  L : ℕ
  R : ℕ
  nx : ℕ
  ny : ℕ
  hL : 1 ≤ L
  hnx : 1 ≤ nx
  hny : 1 ≤ ny

namespace S3Geom

variable (G : S3Geom)

/-- The code has `w + 1 = n_x L` columns. -/
abbrev w : ℕ := G.nx * G.L - 1
/-- The code has `h + 1 = n_y L` rows. -/
abbrev h : ℕ := G.ny * G.L - 1
/-- Checks. -/
abbrev V : Type := PVert G.w G.h
/-- Edges. -/
abbrev Ed : Type := PEdge G.w G.h
/-- Blocks. -/
abbrev Block : Type := Fin G.nx × Fin G.ny

theorem W_pos : 1 ≤ G.nx * G.L := Nat.mul_pos G.hnx G.hL
theorem H_pos : 1 ≤ G.ny * G.L := Nat.mul_pos G.hny G.hL
theorem w_succ : G.w + 1 = G.nx * G.L := Nat.sub_add_cancel G.W_pos
theorem h_succ : G.h + 1 = G.ny * G.L := Nat.sub_add_cancel G.H_pos

/-- Block column of a check column. -/
def bcol (x : Fin (G.w + 1)) : Fin G.nx :=
  ⟨x.val / G.L, (Nat.div_lt_iff_lt_mul G.hL).2 (by have := x.isLt; have := G.w_succ; omega)⟩

/-- Block row of a check row. -/
def brow (y : Fin (G.h + 1)) : Fin G.ny :=
  ⟨y.val / G.L, (Nat.div_lt_iff_lt_mul G.hL).2 (by have := y.isLt; have := G.h_succ; omega)⟩

/-- The block of a check. -/
def blockOf (v : G.V) : G.Block := (G.bcol v.1, G.brow v.2)

/-- `ℓ∞` distance of the check `v` from the block `c`. -/
def distVB (v : G.V) (c : G.Block) : ℕ :=
  max (dist1 v.1.val (c.1.val * G.L) (c.1.val * G.L + G.L - 1))
    (dist1 v.2.val (c.2.val * G.L) (c.2.val * G.L + G.L - 1))

/-- `ℓ∞` distance of blocks. -/
def blockDist (c c' : G.Block) : ℕ := max (ndist c.1.val c'.1.val) (ndist c.2.val c'.2.val)

/-- The left or lower endpoint of an edge (the check of a half-edge). -/
def lowEnd : G.Ed → G.V
  | .hor x y => (x.castSucc, y)
  | .ver x y => (x, y.castSucc)
  | .bot x => (x, 0)
  | .top x => (x, Fin.last _)

/-- The block that owns an edge. -/
def owner (e : G.Ed) : G.Block := G.blockOf (G.lowEnd e)

/-- The window of block `c`: checks within `ℓ∞` distance `R`. -/
def inWin (c : G.Block) (v : G.V) : Prop := G.distVB v c ≤ G.R

/-- Edges with an endpoint in the window of a block of `N_1(c)`. -/
def Nbhd (c : G.Block) (e : G.Ed) : Prop :=
  ∃ v ∈ e.ends, ∃ c' : G.Block, G.blockDist c' c ≤ 1 ∧ G.distVB v c' ≤ G.R

/-- Block rows `2, …, n_y - 3` (the sampled rows; convention (i) declares rows `0, 1, n_y-2, n_y-1` bad). -/
def sampledRow (c : G.Block) : Prop := 2 ≤ c.2.val ∧ c.2.val + 3 ≤ G.ny

/-- The independence distance `D = 4 + ⌊2R/L⌋`. -/
def D : ℕ := 4 + 2 * G.R / G.L

/-! ## Basic facts -/

theorem div_le_div_succ (x L : ℕ) : x / L ≤ (x + 1) / L := Nat.div_le_div_right (Nat.le_succ x)

theorem div_succ_le {L : ℕ} (hL : 1 ≤ L) (x : ℕ) : (x + 1) / L ≤ x / L + 1 := by
  have h1 := Nat.lt_div_mul_add (a := x) (b := L) (by omega)
  have h2 : (x + 1) / L < x / L + 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), add_mul]
    omega
  omega

/-- A check lies at distance `0` from its own block. -/
theorem distVB_blockOf (v : G.V) : G.distVB v (G.blockOf v) = 0 := by
  have hL := G.hL
  have a1 := Nat.div_mul_le_self v.1.val G.L
  have a2 := Nat.lt_div_mul_add (a := v.1.val) (b := G.L) (by omega)
  have b1 := Nat.div_mul_le_self v.2.val G.L
  have b2 := Nat.lt_div_mul_add (a := v.2.val) (b := G.L) (by omega)
  simp only [distVB, blockOf, bcol, brow, dist1]
  omega

theorem blockDist_self (c : G.Block) : G.blockDist c c = 0 := by
  simp [blockDist, ndist]

theorem blockDist_comm (c c' : G.Block) : G.blockDist c c' = G.blockDist c' c := by
  simp only [blockDist, ndist]
  omega

/-- The two endpoints of an edge differ by at most one in each coordinate. -/
theorem ends_adjacent (e : G.Ed) {u u' : G.V} (hu : u ∈ e.ends) (hu' : u' ∈ e.ends) :
    ndist u.1.val u'.1.val ≤ 1 ∧ ndist u.2.val u'.2.val ≤ 1 := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu hu' <;>
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
    simp [ndist, Fin.val_succ, Fin.val_castSucc]

/-- The owner of an edge is at block distance at most `1` from the block of each endpoint. -/
theorem blockDist_owner (e : G.Ed) {v : G.V} (hv : v ∈ e.ends) : G.blockDist (G.owner e) (G.blockOf v) ≤ 1 := by
  have hL := G.hL
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;>
    simp only [PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hv
  · rcases hv with rfl | rfl
    · simp [owner, lowEnd, blockDist, ndist]
    · have h1 := div_le_div_succ x.val G.L
      have h2 := div_succ_le hL x.val
      simp only [owner, lowEnd, blockDist, blockOf, bcol, brow, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
  · rcases hv with rfl | rfl
    · simp [owner, lowEnd, blockDist, ndist]
    · have h1 := div_le_div_succ y.val G.L
      have h2 := div_succ_le hL y.val
      simp only [owner, lowEnd, blockDist, blockOf, bcol, brow, ndist, Fin.val_castSucc, Fin.val_succ]
      omega
  · subst hv
    simp [owner, lowEnd, blockDist, ndist]
  · subst hv
    simp [owner, lowEnd, blockDist, ndist]

/-- The lower endpoint of an edge is an endpoint. -/
theorem lowEnd_mem_ends (e : G.Ed) : G.lowEnd e ∈ e.ends := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;> simp [lowEnd, PEdge.ends]

/-- `(D - 3) L > 2R`. -/
theorem two_R_lt : 2 * G.R < (G.D - 3) * G.L := by
  have hL := G.hL
  have h1 := Nat.lt_div_mul_add (a := 2 * G.R) (b := G.L) (by omega)
  have h2 : G.D - 3 = 2 * G.R / G.L + 1 := by
    simp only [D]
    generalize 2 * G.R / G.L = t
    omega
  rw [h2, add_mul, one_mul]
  exact h1

theorem four_le_D : 4 ≤ G.D := by
  simp only [D]
  generalize 2 * G.R / G.L = t
  omega

theorem sep_aux {L R K a a' x x' : ℕ} (hL : 1 ≤ L) (hK : 2 * R < K) (hA : a * L + K + L ≤ a' * L)
    (hx : dist1 x (a * L) (a * L + L - 1) ≤ R) (hx' : dist1 x' (a' * L) (a' * L + L - 1) ≤ R)
    (hxx : ndist x x' ≤ 1) : False := by
  simp only [dist1, ndist] at hx hx' hxx
  generalize a * L = A at *
  generalize a' * L = A' at *
  omega

/-- The separation step in one coordinate. -/
theorem sep_coord {L R Dd b b' a a' x x' : ℕ} (hL : 1 ≤ L) (hK : 2 * R < (Dd - 3) * L) (hD : 4 ≤ Dd)
    (hbb : Dd ≤ ndist b b') (hab : ndist a b ≤ 1) (hab' : ndist a' b' ≤ 1)
    (hx : dist1 x (a * L) (a * L + L - 1) ≤ R) (hx' : dist1 x' (a' * L) (a' * L + L - 1) ≤ R)
    (hxx : ndist x x' ≤ 1) : False := by
  simp only [ndist] at hbb hab hab'
  rcases Nat.le_total b b' with hle | hle
  · have hge : a + (Dd - 3) + 1 ≤ a' := by omega
    have hm := Nat.mul_le_mul_right L hge
    rw [add_mul, add_mul, one_mul] at hm
    exact sep_aux hL hK hm hx hx' hxx
  · have hge : a' + (Dd - 3) + 1 ≤ a := by omega
    have hm := Nat.mul_le_mul_right L hge
    rw [add_mul, add_mul, one_mul] at hm
    refine sep_aux hL hK hm hx' hx ?_
    simp only [ndist] at hxx ⊢
    omega

/-- Blocks at block distance at least `D` have disjoint edge neighbourhoods. -/
theorem nbhd_disjoint {c c' : G.Block} (hcc : G.D ≤ G.blockDist c c') {e : G.Ed} (h1 : G.Nbhd c e)
    (h2 : G.Nbhd c' e) : False := by
  obtain ⟨u, hu, c1, hc1, hu1⟩ := h1
  obtain ⟨u', hu', c1', hc1', hu1'⟩ := h2
  have hadj := G.ends_adjacent e hu hu'
  have hK := G.two_R_lt
  have hD4 := G.four_le_D
  simp only [blockDist] at hcc hc1 hc1'
  simp only [distVB] at hu1 hu1'
  rcases le_max_iff.1 hcc with hx | hy
  · exact sep_coord G.hL hK hD4 hx (le_of_max_le_left hc1) (le_of_max_le_left hc1')
      (le_of_max_le_left hu1) (le_of_max_le_left hu1') hadj.1
  · exact sep_coord G.hL hK hD4 hy (le_of_max_le_right hc1) (le_of_max_le_right hc1')
      (le_of_max_le_right hu1) (le_of_max_le_right hu1') hadj.2

end S3Geom

end QECML
