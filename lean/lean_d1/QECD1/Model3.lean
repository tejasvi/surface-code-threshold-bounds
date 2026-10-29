import QECD1.Parity3

/-!
# The 3D (phenomenological) code model: checks, edges, syndrome, handshake, rough sides

This is the 3D analogue of the 2D `PVert`/`PEdge` and the start of `S3/Geometry`. Checks sit at
`(t, x, y)` with `t ≤ T` (rounds), `x ≤ w`, `y ≤ h`. There are five kinds of edges:
* `hor t x y`: from `(t, x, y)` to `(t, x + 1, y)`;
* `ver t x y`: from `(t, x, y)` to `(t, x, y + 1)`;
* `time t x y`: from `(t, x, y)` to `(t + 1, x, y)`, the measurement errors;
* `bot t x`, `top t x`: half-edges at the rough sides `y = 0` and `y = h`.

The t and x sides are smooth: they have no half-edges, and the final round is perfect.

* `ends`: two ends for bulk edges (`card_ends_bulk`), one for half-edges.
* `ends_adjacent`: the ends of an edge are `≤ 1` apart in `ℓ∞`. This is the `hunit` input of `confine3` (Lemma A).
* `psyn3`: the syndrome of an edge set `X : PEdge3 → ZMod 2`.
* `sum_psyn3`, `sum_psyn3_eq_zero` (handshake): the syndrome summed over all checks is the sum of `X` over the
  half-edges, and 0 if `X` has no half-edges (2D `sum_psyn_eq_zero`).
* `blockOf3`, `declared_of_rough`: a check on a rough side lies in a block of row 0 or `n_y - 1`, hence in a
  declared block (`declared3`), for `h + 1 = n_y L`.
-/

namespace QECD1

/-- Checks of the 3D code: `(t, x, y)` with `t ≤ T`, `x ≤ w`, `y ≤ h`. -/
abbrev PVert3 (T w h : ℕ) := Fin (T + 1) × Fin (w + 1) × Fin (h + 1)

/-- Edges of the 3D code. -/
inductive PEdge3 (T w h : ℕ) where
  | hor (t : Fin (T + 1)) (x : Fin w) (y : Fin (h + 1))
  | ver (t : Fin (T + 1)) (x : Fin (w + 1)) (y : Fin h)
  | time (t : Fin T) (x : Fin (w + 1)) (y : Fin (h + 1))
  | bot (t : Fin (T + 1)) (x : Fin (w + 1))
  | top (t : Fin (T + 1)) (x : Fin (w + 1))
  deriving DecidableEq, Fintype

variable {T w h : ℕ}

/-- The ends of an edge. -/
def PEdge3.ends : PEdge3 T w h → Finset (PVert3 T w h)
  | .hor t x y => {(t, x.castSucc, y), (t, x.succ, y)}
  | .ver t x y => {(t, x, y.castSucc), (t, x, y.succ)}
  | .time t x y => {(t.castSucc, x, y), (t.succ, x, y)}
  | .bot t x => {(t, x, 0)}
  | .top t x => {(t, x, Fin.last h)}

/-- The integer coordinates of a check. -/
def PVert3.toV3 (v : PVert3 T w h) : V3 := ((v.1 : ℕ), (v.2.1 : ℕ), (v.2.2 : ℕ))

/-- The edge is a half-edge (on a rough side). -/
def PEdge3.isHalf : PEdge3 T w h → Prop
  | .bot _ _ => True
  | .top _ _ => True
  | _ => False

instance (e : PEdge3 T w h) : Decidable e.isHalf := by
  cases e <;> unfold PEdge3.isHalf <;> infer_instance

theorem card_ends_bulk (e : PEdge3 T w h) (he : ¬ e.isHalf) : e.ends.card = 2 := by
  cases e with
  | hor t x y =>
    simp only [PEdge3.ends]
    rw [Finset.card_pair]
    intro heq
    have := congrArg (fun v : PVert3 T w h => (v.2.1 : ℕ)) heq
    simp at this
  | ver t x y =>
    simp only [PEdge3.ends]
    rw [Finset.card_pair]
    intro heq
    have := congrArg (fun v : PVert3 T w h => (v.2.2 : ℕ)) heq
    simp at this
  | time t x y =>
    simp only [PEdge3.ends]
    rw [Finset.card_pair]
    intro heq
    have := congrArg (fun v : PVert3 T w h => (v.1 : ℕ)) heq
    simp at this
  | bot t x => exact absurd trivial he
  | top t x => exact absurd trivial he

theorem card_ends_half (e : PEdge3 T w h) (he : e.isHalf) : e.ends.card = 1 := by
  cases e with
  | hor t x y => exact absurd he id
  | ver t x y => exact absurd he id
  | time t x y => exact absurd he id
  | bot t x => simp [PEdge3.ends]
  | top t x => simp [PEdge3.ends]

/-- **The ends of an edge are unit steps apart.** -/
theorem ends_adjacent (e : PEdge3 T w h) {u u' : PVert3 T w h} (hu : u ∈ e.ends) (hu' : u' ∈ e.ends) :
    linf (u.toV3 - u'.toV3) ≤ 1 := by
  cases e with
  | hor t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
      simp only [PVert3.toV3, linf, Prod.fst_sub, Prod.snd_sub, Fin.val_castSucc, Fin.val_succ] <;> omega
  | ver t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
      simp only [PVert3.toV3, linf, Prod.fst_sub, Prod.snd_sub, Fin.val_castSucc, Fin.val_succ] <;> omega
  | time t x y =>
    simp only [PEdge3.ends, Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
      simp only [PVert3.toV3, linf, Prod.fst_sub, Prod.snd_sub, Fin.val_castSucc, Fin.val_succ] <;> omega
  | bot t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hu'
    subst hu hu'
    simp [linf]
  | top t x =>
    simp only [PEdge3.ends, Finset.mem_singleton] at hu hu'
    subst hu hu'
    simp [linf]

/-- The syndrome of an edge set. -/
def psyn3 (X : PEdge3 T w h → ZMod 2) (v : PVert3 T w h) : ZMod 2 :=
  ∑ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => v ∈ e.ends), X e

/-- **Handshake** (3D): the syndrome summed over all checks is the sum of `X` over the half-edges. -/
theorem sum_psyn3 (X : PEdge3 T w h → ZMod 2) :
    ∑ v, psyn3 X v = ∑ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => e.isHalf), X e := by
  simp only [psyn3]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun e => e.ends) (by intro v e; simp)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e : PEdge3 T w h => e.isHalf)]
  have h1 : ∀ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => e.isHalf), ∑ _v ∈ e.ends, X e = X e := by
    intro e he
    rw [Finset.sum_const, card_ends_half e (Finset.mem_filter.1 he).2, one_smul]
  have h2 : ∀ e ∈ Finset.univ.filter (fun e : PEdge3 T w h => ¬ e.isHalf), ∑ _v ∈ e.ends, X e = 0 := by
    intro e he
    rw [Finset.sum_const, card_ends_bulk e (Finset.mem_filter.1 he).2, two_nsmul]
    exact CharTwo.add_self_eq_zero (X e)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]

/-- **Handshake without half-edges**: an edge set with no half-edges has an even number of odd checks. -/
theorem sum_psyn3_eq_zero (X : PEdge3 T w h → ZMod 2) (hX : ∀ e, e.isHalf → X e = 0) :
    ∑ v, psyn3 X v = 0 := by
  rw [sum_psyn3]
  exact Finset.sum_eq_zero fun e he => hX e (Finset.mem_filter.1 he).2

/-- The block of a check (block side `L = 35`). -/
def blockOf3 (v : PVert3 T w h) : V3 := blockOf v.toV3

/-- **Rough sides are declared**: for `h + 1 = n_y L` (`L = 35`), a check with `y = 0` or `y = h` lies in a block of
row 0 or row `n_y - 1`, which is declared. -/
theorem declared_of_rough (ny : ℕ) (hh : h + 1 = ny * 35) (v : PVert3 T w h)
    (hv : (v.2.2 : ℕ) = 0 ∨ (v.2.2 : ℕ) = h) : declared3 ny (blockOf3 v) := by
  simp only [declared3, blockOf3, blockOf, PVert3.toV3]
  rcases hv with h0 | h1
  · left
    rw [h0]
    norm_num
  · right
    rw [h1]
    omega

end QECD1
