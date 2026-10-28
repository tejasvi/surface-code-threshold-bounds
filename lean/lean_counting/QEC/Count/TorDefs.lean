import QEC.Count.Torus
import QEC.Count.Defs
import QECCountComp.SeamC

/-!
# The toric code with the seam-aware certificate: definitions (Theorem A′)

* Seam offsets. The tie-break function is `φ = x_rep`, the column of a vertex in `[0, L)`. The seam offset of a
  column `x` is `x` if `2x < L` and `x - L` otherwise (`qoffZ`), so the seam lies between the offsets `-1` and `0`;
  `nxtT L` updates an offset by a step, `offAt` gives the offset of a vertex of a walk.
* Walks with offset-dependent exclusions: `LegalG nxt Ex M o w` (windows of `2..M` edges are tested by `Ex` at the
  offset of their first vertex) and `SuccG`. For the torus, `nxt = nxtT L` and `Ex = ExclT L0`, where `ExclT L0 o w`
  is the seam witness check `checkWT` at offset `o`.
* `phiTor L`: `Φ` of an edge, the sum of the columns of its ends.
* `torDir`, `patOfT`: the direction of a torus step and the labelled pattern of a vertex list (label `true` iff the
  edge is not in the given set; for the residual `C ∆ E` and the set `E`, the C-edges).
-/

namespace QEC

open Finset QECComp

/-! ## Seam offsets -/

/-- The seam offset of a column `q` (an integer standing for the column `q mod L`): the residue `r` of `q` modulo `L`
if `2r < L`, else `r - L`. -/
def qoffZ (L : ℕ) (q : ℤ) : ℤ := if 2 * (q % (L : ℤ)) < L then q % (L : ℤ) else q % (L : ℤ) - L

/-- The seam offset of a torus vertex. -/
def qoff {L : ℕ} (v : TorV L) : ℤ := qoffZ L ((v.1 : ℕ) : ℤ)

/-- The x-increment of a direction (`0, 1, 2, 3` = `+x, -x, +y, -y`). -/
def dxOf (d : ℕ) : ℤ := if d = 0 then 1 else if d = 1 then -1 else 0

/-- The seam offset after a step in direction `d` on the torus of size `L`. -/
def nxtT (L : ℕ) (q : ℤ) (d : ℕ) : ℤ := qoffZ L (q + dxOf d)

/-- The offset of the `i`-th vertex of the walk `w` whose first vertex has offset `o` (offset update `nxt`). -/
def offAt (nxt : ℤ → ℕ → ℤ) (o : ℤ) (w : List (ℕ × Bool)) (i : ℕ) : ℤ := ((w.take i).map Prod.fst).foldl nxt o

/-! ## Walks with offset-dependent exclusions (dimension 2) -/

section Walks

variable (nxt : ℤ → ℕ → ℤ) (Ex : ℤ → List (ℕ × Bool) → Prop)

/-- Legal labelled walks from a first vertex of offset `o`, for windows of up to `M` edges: self-avoiding, valid
directions, and no window of `2..M` edges excluded at the offset of its first vertex. -/
def LegalG (M : ℕ) (o : ℤ) (w : List (ℕ × Bool)) : Prop :=
  SelfAv 2 w ∧ DirOK 2 w ∧
    ∀ i m, 2 ≤ m → m ≤ M → i + m ≤ w.length → ¬ Ex (offAt nxt o w i) ((w.drop i).take m)

/-- `x` is a legal successor of the state `s` whose first vertex has offset `o`: the walk stays self-avoiding and no
window of `2..|s|+1` edges ending with the new edge is excluded at the offset of its first vertex. The new state
`(s ++ [x]).tail` has first-vertex offset `offAt nxt o s 1`. -/
def SuccG (s : List (ℕ × Bool)) (o : ℤ) (x : ℕ × Bool) : Prop :=
  x.1 < 4 ∧ SelfAv 2 (s ++ [x]) ∧
    ∀ m, 2 ≤ m → m ≤ s.length + 1 →
      ¬ Ex (offAt nxt o (s ++ [x]) (s.length + 1 - m)) ((s ++ [x]).drop (s.length + 1 - m))

end Walks

/-- An excluded window at seam offset `o` (seam rules with the constant `L0`): some witness passes `checkWT`. -/
def ExclT (L0 : ℕ) (o : ℤ) (w : List (ℕ × Bool)) : Prop := ∃ W, checkWT L0 o w W = true

/-! ## The torus -/

/-- The column of a vertex of the torus graph (`0` for the unused boundary vertices). -/
def xcol {L : ℕ} : Vx (TorV L) → ℤ
  | .det v => ((v.1 : ℕ) : ℤ)
  | _ => 0

/-- `Φ` of an edge of the torus: the sum of the columns `x_rep` of its ends. -/
def phiTor (L : ℕ) : Sym2 (Vx (TorV L)) → ℤ :=
  Sym2.lift ⟨fun a b => xcol a + xcol b, fun _ _ => add_comm _ _⟩

/-- The direction of the step from `u` to a neighbour `v` (`0, 1, 2, 3` = `+x, -x, +y, -y`, modulo `L`). -/
def torDir {L : ℕ} (u v : TorV L) : ℕ :=
  if u.2 = v.2 ∧ ((u.1 : ℕ) + 1) % L = v.1 then 0
  else if u.2 = v.2 ∧ ((v.1 : ℕ) + 1) % L = u.1 then 1
  else if u.1 = v.1 ∧ ((u.2 : ℕ) + 1) % L = v.2 then 2
  else 3

/-- The labelled pattern of a vertex list (label `true` iff the edge is not in `S`). -/
def patOfT {L : ℕ} (S : Finset (Sym2 (Vx (TorV L)))) : List (TorV L) → List (ℕ × Bool)
  | u :: v :: rest => (torDir u v, decide (s(Vx.det u, Vx.det v) ∉ S)) :: patOfT S (v :: rest)
  | _ => []

end QEC
