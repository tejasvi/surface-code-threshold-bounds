import QECML.S3.Events

/-!
# Embedding a code into a larger one (for the equality of block types)

`Emb G' G` places the code `G'` inside the code `G` at block offset `(a, b)` (same block side `L` and window radius
`R`): checks `(x, y) ↦ (x + L a, y + L b)`, blocks `(i, j) ↦ (i + a, j + b)`, edges likewise.

* `blockOf_V`, `distVB_VB`, `blockDist_B`, `ends_E`, `owner_E`, `inWin_VB`: the embedding preserves blocks of checks,
  check-block distances, block distances, ends and owners of bulk edges, and windows.
* `V_inj`, `B_inj`, `E_inj`: it is injective.
-/

namespace QECML

namespace S3Geom

/-- An embedding of the code `G'` into the code `G` at block offset `(a, b)` (same `L` and `R`). -/
structure Emb (G' G : S3Geom) where
  a : ℕ
  b : ℕ
  hL : G'.L = G.L
  hR : G'.R = G.R
  hw : G'.nx + a ≤ G.nx
  hh : G'.ny + b ≤ G.ny

/-- Bulk edges (no half-edge). -/
def isBulk {w h : ℕ} : PEdge w h → Prop
  | .hor _ _ => True
  | .ver _ _ => True
  | .bot _ => False
  | .top _ => False

namespace Emb

variable {G' G : S3Geom} (ι : Emb G' G)

theorem x_lt {x : ℕ} (hx : x < G'.w + 1) : x + G.L * ι.a < G.w + 1 := by
  have h1 := G'.w_succ
  have h2 := G.w_succ
  have h3 : (G'.nx + ι.a) * G.L ≤ G.nx * G.L := Nat.mul_le_mul_right _ ι.hw
  have h4 : (G'.nx + ι.a) * G.L = G'.nx * G.L + G.L * ι.a := by ring
  rw [ι.hL] at h1
  omega

theorem y_lt {y : ℕ} (hy : y < G'.h + 1) : y + G.L * ι.b < G.h + 1 := by
  have h1 := G'.h_succ
  have h2 := G.h_succ
  have h3 : (G'.ny + ι.b) * G.L ≤ G.ny * G.L := Nat.mul_le_mul_right _ ι.hh
  have h4 : (G'.ny + ι.b) * G.L = G'.ny * G.L + G.L * ι.b := by ring
  rw [ι.hL] at h1
  omega

theorem x_lt' {x : ℕ} (hx : x < G'.w) : x + G.L * ι.a < G.w := by
  have := ι.x_lt (x := G'.w) (by omega)
  omega

theorem y_lt' {y : ℕ} (hy : y < G'.h) : y + G.L * ι.b < G.h := by
  have := ι.y_lt (y := G'.h) (by omega)
  omega

/-- The image of a check. -/
def V (v : G'.V) : G.V := (⟨v.1.val + G.L * ι.a, ι.x_lt v.1.isLt⟩, ⟨v.2.val + G.L * ι.b, ι.y_lt v.2.isLt⟩)

/-- The image of a block. -/
def B (c : G'.Block) : G.Block :=
  (⟨c.1.val + ι.a, by have := c.1.isLt; have := ι.hw; omega⟩,
    ⟨c.2.val + ι.b, by have := c.2.isLt; have := ι.hh; omega⟩)

/-- The image of an edge (meaningful for bulk edges). -/
def E : G'.Ed → G.Ed
  | .hor x y => .hor ⟨x.val + G.L * ι.a, ι.x_lt' x.isLt⟩ ⟨y.val + G.L * ι.b, ι.y_lt y.isLt⟩
  | .ver x y => .ver ⟨x.val + G.L * ι.a, ι.x_lt x.isLt⟩ ⟨y.val + G.L * ι.b, ι.y_lt' y.isLt⟩
  | .bot x => .bot ⟨x.val + G.L * ι.a, ι.x_lt x.isLt⟩
  | .top x => .top ⟨x.val + G.L * ι.a, ι.x_lt x.isLt⟩

@[simp] theorem V_fst (v : G'.V) : (ι.V v).1.val = v.1.val + G.L * ι.a := rfl
@[simp] theorem V_snd (v : G'.V) : (ι.V v).2.val = v.2.val + G.L * ι.b := rfl
@[simp] theorem B_fst (c : G'.Block) : (ι.B c).1.val = c.1.val + ι.a := rfl
@[simp] theorem B_snd (c : G'.Block) : (ι.B c).2.val = c.2.val + ι.b := rfl

theorem V_inj : Function.Injective ι.V := fun v w h => by
  have h1 := congrArg (fun u : G.V => u.1.val) h
  have h2 := congrArg (fun u : G.V => u.2.val) h
  simp only [V_fst, V_snd] at h1 h2
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem B_inj : Function.Injective ι.B := fun c d h => by
  have h1 := congrArg (fun u : G.Block => u.1.val) h
  have h2 := congrArg (fun u : G.Block => u.2.val) h
  simp only [B_fst, B_snd] at h1 h2
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem E_inj : Function.Injective ι.E := by
  intro e f h
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x <;> rcases f with ⟨x', y'⟩ | ⟨x', y'⟩ | x' | x' <;>
    simp only [E, PEdge.hor.injEq, PEdge.ver.injEq, PEdge.bot.injEq, PEdge.top.injEq, reduceCtorEq,
      Fin.mk.injEq] at h ⊢
  · exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · exact Fin.ext (by omega)
  · exact Fin.ext (by omega)

/-- The embedding commutes with taking the block of a check. -/
theorem blockOf_V (v : G'.V) : G.blockOf (ι.V v) = ι.B (G'.blockOf v) := by
  have hpos : 0 < G.L := G.hL
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show (v.1.val + G.L * ι.a) / G.L = v.1.val / G'.L + ι.a
    rw [ι.hL, Nat.add_mul_div_left _ _ hpos]
  · show (v.2.val + G.L * ι.b) / G.L = v.2.val / G'.L + ι.b
    rw [ι.hL, Nat.add_mul_div_left _ _ hpos]

/-- Check-block distances are preserved. -/
theorem distVB_VB (v : G'.V) (c : G'.Block) : G.distVB (ι.V v) (ι.B c) = G'.distVB v c := by
  have hL1 := G.hL
  simp only [distVB, dist1, V_fst, V_snd, B_fst, B_snd, ι.hL]
  have e1 : (c.1.val + ι.a) * G.L = c.1.val * G.L + G.L * ι.a := by ring
  have e2 : (c.2.val + ι.b) * G.L = c.2.val * G.L + G.L * ι.b := by ring
  rw [e1, e2]
  congr 1 <;> omega

/-- Block distances are preserved. -/
theorem blockDist_B (c d : G'.Block) : G.blockDist (ι.B c) (ι.B d) = G'.blockDist c d := by
  simp only [blockDist, ndist, B_fst, B_snd]
  congr 1 <;> omega

/-- Windows are preserved. -/
theorem inWin_VB (c : G'.Block) (v : G'.V) : G.inWin (ι.B c) (ι.V v) ↔ G'.inWin c v := by
  simp only [inWin, distVB_VB, ι.hR]

/-- The ends of the image of a bulk edge are the images of its ends. -/
theorem mem_ends_E {e : G'.Ed} (he : isBulk e) (v : G'.V) : ι.V v ∈ (ι.E e).ends ↔ v ∈ e.ends := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
  · simp only [E, PEdge.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, V_fst,
      V_snd, Fin.val_castSucc, Fin.val_succ]
    omega
  · simp only [E, PEdge.ends, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, V_fst,
      V_snd, Fin.val_castSucc, Fin.val_succ]
    omega
  · exact absurd he id
  · exact absurd he id

/-- Every end of the image of a bulk edge is the image of an end. -/
theorem ends_E_sub {e : G'.Ed} (he : isBulk e) {u : G.V} (hu : u ∈ (ι.E e).ends) : ∃ v ∈ e.ends, ι.V v = u := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
  · simp only [E, PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨(x.castSucc, y), by simp [PEdge.ends], Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp))⟩
    · exact ⟨(x.succ, y), by simp [PEdge.ends], Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp))⟩
  · simp only [E, PEdge.ends, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨(x, y.castSucc), by simp [PEdge.ends], Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp))⟩
    · exact ⟨(x, y.succ), by simp [PEdge.ends], Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp; omega))⟩
  · exact absurd he id
  · exact absurd he id

/-- Owners of bulk edges are preserved. -/
theorem owner_E {e : G'.Ed} (he : isBulk e) : G.owner (ι.E e) = ι.B (G'.owner e) := by
  have hlow : G.lowEnd (ι.E e) = ι.V (G'.lowEnd e) := by
    rcases e with ⟨x, y⟩ | ⟨x, y⟩ | x | x
    · exact Prod.ext (Fin.ext (by simp [lowEnd, E])) (Fin.ext (by simp [lowEnd, E]))
    · exact Prod.ext (Fin.ext (by simp [lowEnd, E])) (Fin.ext (by simp [lowEnd, E]))
    · exact absurd he id
    · exact absurd he id
  rw [owner, hlow, blockOf_V]
  rfl

end Emb

end S3Geom

end QECML
