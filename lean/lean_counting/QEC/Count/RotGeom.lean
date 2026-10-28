import QEC.Count.RDefs
import QEC.Count.BoxSound
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# The rotated surface code as a region code

Lattice coordinates `(U, V) = ((i + j)/2, (i - j)/2)` of the X check at plaquette position `(i, j)` (Z errors, X checks).
The checks are the integer points with `0 ≤ U + V ≤ d - 2` (between the two rough sides) and `-1 ≤ U - V ≤ d - 1`
(between the two smooth sides). The outer points are the integer points with `U + V = -1` (side 1) or `U + V = d - 1`
(side 2) and `-1 ≤ U - V ≤ d - 1`: the "virtual plaquettes" `(i, j)` with `i = -1` or `i = d - 1`. The edges are the
lattice edges between these points (never between two outer points). `RotLayout.lean` proves that the edges are
exactly the qubits of the rotated code, with the checks and the logical parity of the code.

`posR` gives the position of a vertex, `phiRot c` the tie-break function (`φ(a) + φ(b)` for the edge `ab`, outer points
included), `AdjChainR` and `patOfR` the steps and the labelled pattern of a path of checks.
-/

namespace QEC

open Finset QECComp

/-- The checks of the rotated code of distance `d`. -/
def rotChk (d : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(d : ℤ)) d) ×ˢ (Finset.Icc (-(d : ℤ)) d)).filter
    (fun x => 0 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d - 2 ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1)

/-- The outer points of the rotated code of distance `d`. -/
def rotOut (d : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(d : ℤ)) d) ×ˢ (Finset.Icc (-(d : ℤ)) d)).filter
    (fun x => (x.1 + x.2 = -1 ∨ x.1 + x.2 = d - 1) ∧ -1 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d - 1)

/-- The checks as a type. -/
abbrev RChk (d : ℕ) := {x : ℤ × ℤ // x ∈ rotChk d}

/-- The outer points as a type. -/
abbrev ROut (d : ℕ) := {x : ℤ × ℤ // x ∈ rotOut d}

/-- The position of a vertex. -/
def posR {d : ℕ} : RVx (RChk d) (ROut d) → List ℤ
  | .chk v => [v.1.1, v.1.2]
  | .out w => [w.1.1, w.1.2]

/-- The side of an outer point: side 1 is the rough side `U + V = -1`. -/
def rotSide {d : ℕ} (w : ROut d) : Bool := decide (w.1.1 + w.1.2 = -1)

/-- Two vertices are joined by an edge of the rotated code: lattice neighbours, not both outer points. -/
def RotAdj {d : ℕ} : RVx (RChk d) (ROut d) → RVx (RChk d) (ROut d) → Prop
  | .out _, .out _ => False
  | a, b => l1 (posR a) (posR b) = 1

instance {d : ℕ} : DecidableRel (@RotAdj d) := fun a b => by
  cases a <;> cases b <;> simp only [RotAdj] <;> infer_instance

/-- The edges of the rotated code of distance `d` (as a region code). -/
def rotEdges (d : ℕ) : Finset (Sym2 (RVx (RChk d) (ROut d))) :=
  ((univ ×ˢ univ).filter (fun ab : RVx (RChk d) (ROut d) × RVx (RChk d) (ROut d) => RotAdj ab.1 ab.2)).image
    (fun ab => s(ab.1, ab.2))

/-- `φ(a) + φ(b)` for an edge `ab` (outer points by their position). -/
def phiRot {d : ℕ} (c : List ℤ) : Sym2 (RVx (RChk d) (ROut d)) → ℤ :=
  Sym2.lift ⟨fun a b => phiP c (posR a) + phiP c (posR b), fun a b => by simp [add_comm]⟩

/-- Consecutive checks of the list are lattice neighbours. -/
def AdjChainR {d : ℕ} : List (RChk d) → Prop
  | u :: v :: rest => l1 [u.1.1, u.1.2] [v.1.1, v.1.2] = 1 ∧ AdjChainR (v :: rest)
  | _ => True

/-- The direction from a check to a neighbouring check. -/
noncomputable def dirOfR {d : ℕ} (u v : RChk d) : ℕ :=
  open Classical in
  if h : ∃ dd < 4, [v.1.1, v.1.2] = addP [u.1.1, u.1.2] (vecOf 2 dd) then Classical.choose h else 0

/-- The labelled pattern of a path of checks (label `true` = C-edge = not in `S`). -/
noncomputable def patOfR {d : ℕ} (S : Finset (Sym2 (RVx (RChk d) (ROut d)))) : List (RChk d) → List (ℕ × Bool)
  | u :: v :: rest => (dirOfR u v, decide (s(RVx.chk u, RVx.chk v) ∉ S)) :: patOfR S (v :: rest)
  | _ => []

end QEC
