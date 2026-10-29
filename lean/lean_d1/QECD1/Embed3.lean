import QECD1.Types3

/-!
# Embedding a 3D code into a larger one (for the block types)

The 3D analogue of the 2D `S3/Embed`. `Emb3 T' w' h' T w h` places the code `(T', w', h')` inside the code
`(T, w, h)` at block offset `(a, b, d)`: checks `(t, x, y) ↦ (t + 35 a, x + 35 b, y + 35 d)`, blocks
`c ↦ c + (a, b, d)`, edges likewise.

* `V_inj`, `E_inj`: the embedding is injective on checks and edges.
* `blockOf3_V`, `distVB_V`, `dist3_B`, `inWin_V`: it preserves the block of a check, check-block distances, block
  distances and windows (`inWin_iff_distVB`: a window is the set of checks within distance 34 of the block).
* `mem_ends_E`, `ends_E_sub`, `lowEnd3_E`, `owner3_E`: it preserves the ends, lower ends and owners of bulk edges.
-/

namespace QECD1

/-- A check is in the window of block `c` iff it is within `ℓ∞` distance 34 of `c`. -/
theorem inWin_iff_distVB (c p : V3) : InWin c p ↔ distVB p c ≤ 34 := by
  refine ⟨fun hw => ?_, inWin_of_distVB⟩
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp only [coord] at h0 h1 h2
  simp only [distVB, max_le_iff, dist1]
  omega

/-- An embedding of the code `(T', w', h')` into the code `(T, w, h)` at block offset `(a, b, d)`. -/
structure Emb3 (T' w' h' T w h : ℕ) where
  a : ℕ
  b : ℕ
  d : ℕ
  hT : T' + 35 * a ≤ T
  hw : w' + 35 * b ≤ w
  hh : h' + 35 * d ≤ h

namespace Emb3

variable {T' w' h' T w h : ℕ} (ι : Emb3 T' w' h' T w h)

theorem lt_T {t : ℕ} (ht : t < T' + 1) : t + 35 * ι.a < T + 1 := by have := ι.hT; omega
theorem lt_T' {t : ℕ} (ht : t < T') : t + 35 * ι.a < T := by have := ι.hT; omega
theorem lt_w {x : ℕ} (hx : x < w' + 1) : x + 35 * ι.b < w + 1 := by have := ι.hw; omega
theorem lt_w' {x : ℕ} (hx : x < w') : x + 35 * ι.b < w := by have := ι.hw; omega
theorem lt_h {y : ℕ} (hy : y < h' + 1) : y + 35 * ι.d < h + 1 := by have := ι.hh; omega
theorem lt_h' {y : ℕ} (hy : y < h') : y + 35 * ι.d < h := by have := ι.hh; omega

/-- The image of a check. -/
def V (v : PVert3 T' w' h') : PVert3 T w h :=
  (⟨v.1.val + 35 * ι.a, ι.lt_T v.1.isLt⟩, ⟨v.2.1.val + 35 * ι.b, ι.lt_w v.2.1.isLt⟩,
    ⟨v.2.2.val + 35 * ι.d, ι.lt_h v.2.2.isLt⟩)

/-- The image of a block. -/
def B (c : V3) : V3 := (c.1 + (ι.a : ℤ), c.2.1 + (ι.b : ℤ), c.2.2 + (ι.d : ℤ))

/-- The image of an edge (meaningful for bulk edges). -/
def E : PEdge3 T' w' h' → PEdge3 T w h
  | .hor t x y => .hor ⟨t.val + 35 * ι.a, ι.lt_T t.isLt⟩ ⟨x.val + 35 * ι.b, ι.lt_w' x.isLt⟩
      ⟨y.val + 35 * ι.d, ι.lt_h y.isLt⟩
  | .ver t x y => .ver ⟨t.val + 35 * ι.a, ι.lt_T t.isLt⟩ ⟨x.val + 35 * ι.b, ι.lt_w x.isLt⟩
      ⟨y.val + 35 * ι.d, ι.lt_h' y.isLt⟩
  | .time t x y => .time ⟨t.val + 35 * ι.a, ι.lt_T' t.isLt⟩ ⟨x.val + 35 * ι.b, ι.lt_w x.isLt⟩
      ⟨y.val + 35 * ι.d, ι.lt_h y.isLt⟩
  | .bot t x => .bot ⟨t.val + 35 * ι.a, ι.lt_T t.isLt⟩ ⟨x.val + 35 * ι.b, ι.lt_w x.isLt⟩
  | .top t x => .top ⟨t.val + 35 * ι.a, ι.lt_T t.isLt⟩ ⟨x.val + 35 * ι.b, ι.lt_w x.isLt⟩

@[simp] theorem V_t (v : PVert3 T' w' h') : (ι.V v).1.val = v.1.val + 35 * ι.a := rfl
@[simp] theorem V_x (v : PVert3 T' w' h') : (ι.V v).2.1.val = v.2.1.val + 35 * ι.b := rfl
@[simp] theorem V_y (v : PVert3 T' w' h') : (ι.V v).2.2.val = v.2.2.val + 35 * ι.d := rfl

theorem V_inj : Function.Injective ι.V := fun v v' hv => by
  have h1 := congrArg (fun u : PVert3 T w h => u.1.val) hv
  have h2 := congrArg (fun u : PVert3 T w h => u.2.1.val) hv
  have h3 := congrArg (fun u : PVert3 T w h => u.2.2.val) hv
  simp only [V_t, V_x, V_y] at h1 h2 h3
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

theorem E_inj : Function.Injective ι.E := by
  intro e f hef
  cases e <;> cases f <;>
    simp only [E, PEdge3.hor.injEq, PEdge3.ver.injEq, PEdge3.time.injEq, PEdge3.bot.injEq, PEdge3.top.injEq,
      reduceCtorEq, Fin.mk.injEq] at hef ⊢
  all_goals first
    | exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩
    | exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem toV3_V (v : PVert3 T' w' h') :
    (ι.V v).toV3 = (v.toV3.1 + 35 * (ι.a : ℤ), v.toV3.2.1 + 35 * (ι.b : ℤ), v.toV3.2.2 + 35 * (ι.d : ℤ)) := by
  simp only [PVert3.toV3, V_t, V_x, V_y]
  push_cast
  rfl

/-- The embedding commutes with taking the block of a check. -/
theorem blockOf3_V (v : PVert3 T' w' h') : blockOf3 (ι.V v) = ι.B (blockOf3 v) := by
  simp only [blockOf3, blockOf, ι.toV3_V, B]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> omega

/-- Check-block distances are preserved. -/
theorem distVB_V (v : PVert3 T' w' h') (c : V3) : distVB (ι.V v).toV3 (ι.B c) = distVB v.toV3 c := by
  simp only [distVB, dist1, ι.toV3_V, B]
  congr 1
  · omega
  · congr 1 <;> omega

theorem B_sub (c c' : V3) : ι.B c - ι.B c' = c - c' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [B]

/-- Block distances are preserved. -/
theorem dist3_B (c c' : V3) : dist3 (ι.B c) (ι.B c') = dist3 c c' := by
  simp only [dist3, ι.B_sub]

/-- Windows are preserved. -/
theorem inWin_V (c : V3) (v : PVert3 T' w' h') : InWin (ι.B c) (ι.V v).toV3 ↔ InWin c v.toV3 := by
  rw [inWin_iff_distVB, inWin_iff_distVB, ι.distVB_V]

/-- The ends of the image of a bulk edge are the images of its ends. -/
theorem mem_ends_E {e : PEdge3 T' w' h'} (he : ¬ e.isHalf) (v : PVert3 T' w' h') :
    ι.V v ∈ (ι.E e).ends ↔ v ∈ e.ends := by
  cases e with
  | hor t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, V_t, V_x, V_y,
      Fin.val_castSucc, Fin.val_succ]
    omega
  | ver t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, V_t, V_x, V_y,
      Fin.val_castSucc, Fin.val_succ]
    omega
  | time t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, V_t, V_x, V_y,
      Fin.val_castSucc, Fin.val_succ]
    omega
  | bot t x => exact absurd trivial he
  | top t x => exact absurd trivial he

/-- Every end of the image of a bulk edge is the image of an end. -/
theorem ends_E_sub {e : PEdge3 T' w' h'} (he : ¬ e.isHalf) {u : PVert3 T w h} (hu : u ∈ (ι.E e).ends) :
    ∃ v ∈ e.ends, ι.V v = u := by
  cases e with
  | hor t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨(t, x.castSucc, y), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp))
        (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))⟩
    · exact ⟨(t, x.succ, y), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp))
        (Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp)))⟩
  | ver t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨(t, x, y.castSucc), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp))
        (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))⟩
    · exact ⟨(t, x, y.succ), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp))
        (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp; omega)))⟩
  | time t x y =>
    simp only [E, PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨(t.castSucc, x, y), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp))
        (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))⟩
    · exact ⟨(t.succ, x, y), by simp [PEdge3.ends], Prod.ext (Fin.ext (by simp; omega))
        (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))⟩
  | bot t x => exact absurd trivial he
  | top t x => exact absurd trivial he

/-- The lower end of the image of a bulk edge is the image of its lower end. -/
theorem lowEnd3_E {e : PEdge3 T' w' h'} (he : ¬ e.isHalf) : lowEnd3 (ι.E e) = ι.V (lowEnd3 e) := by
  cases e with
  | hor t x y => rfl
  | ver t x y => rfl
  | time t x y => rfl
  | bot t x => exact absurd trivial he
  | top t x => exact absurd trivial he

/-- Owners of bulk edges are preserved. -/
theorem owner3_E {e : PEdge3 T' w' h'} (he : ¬ e.isHalf) : owner3 (ι.E e) = ι.B (owner3 e) := by
  rw [owner3, ι.lowEnd3_E he, ι.blockOf3_V]
  rfl

end Emb3

end QECD1
