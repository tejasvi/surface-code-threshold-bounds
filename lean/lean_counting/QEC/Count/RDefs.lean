import QEC.Count.Defs

/-!
# Region codes: checks and outer points with two sides

A decoding graph whose vertices are checks (`RVx.chk v`, with a parity constraint) and outer points (`RVx.out w`,
without constraint), each outer point on side 1 (`side w = true`) or side 2. Edges are `Sym2 (RVx V W)`; there are no
parallel edges, because every half-edge has its own outer endpoint (two half-edges of one check end at different
outer points). A correction fails when its number of edges at side-1 outer points has the wrong parity.

For the rotated surface code (one sector, code capacity) the checks are the X checks, the outer points are the lattice
points just beyond the two rough sides, and the edges are the qubits (`QEC/Count/RotGeom.lean`, `RotLayout.lean`).
-/

namespace QEC

open Finset

/-- Vertices of a region code: checks and outer points. -/
inductive RVx (V W : Type*) where
  | chk (v : V) : RVx V W
  | out (w : W) : RVx V W
  deriving DecidableEq, Fintype

section RCode

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The checks of odd degree in `C`. -/
def rbd (C : Finset (Sym2 (RVx V W))) : Finset V := univ.filter (fun v => Odd (vdeg C (RVx.chk v)))

/-- The number of edge ends of `C` at the outer points of side 1. -/
def side1deg (side : W → Bool) (C : Finset (Sym2 (RVx V W))) : ℕ :=
  ∑ w ∈ univ.filter (fun w => side w = true), vdeg C (RVx.out w)

/-- The correction `C` fails for the error `E`: its side-1 parity differs from that of `E`. -/
def FailsR (side : W → Bool) (E C : Finset (Sym2 (RVx V W))) : Prop :=
  ¬ (Odd (side1deg side C) ↔ Odd (side1deg side E))

/-- `C` is a correction (edges of the graph with check boundary `A`) of least size. -/
def IsMinCorrR (Eg : Finset (Sym2 (RVx V W))) (A : Finset V) (C : Finset (Sym2 (RVx V W))) : Prop :=
  C ⊆ Eg ∧ rbd C = A ∧ ∀ C' ⊆ Eg, rbd C' = A → #C ≤ #C'

/-- The probability that some minimum-weight correction of the error's syndrome fails. -/
noncomputable def PfailMWR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) (p : ℝ) : ℝ :=
  PrIID Eg p (fun E => ∃ C, IsMinCorrR Eg (rbd E) C ∧ FailsR side E C)

/-- The failure probability of a decoder that maps the syndrome to a guess of the side-1 parity. -/
noncomputable def PfailDecR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) (p : ℝ) (dec : Finset V → Bool) : ℝ :=
  PrIID Eg p (fun E => dec (rbd E) ≠ decide (Odd (side1deg side E)))

/-- The optimal (maximum-likelihood) failure probability. -/
noncomputable def PfailMLR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) (p : ℝ) : ℝ :=
  ⨅ dec : Finset V → Bool, PfailDecR Eg side p dec

/-- `C` is a failing minimum-weight correction of least `Φ` among the failing ones. -/
def IsPhiMinFailR (Eg : Finset (Sym2 (RVx V W))) (side : W → Bool) (Φ : Sym2 (RVx V W) → ℤ)
    (E C : Finset (Sym2 (RVx V W))) : Prop :=
  IsMinCorrR Eg (rbd E) C ∧ FailsR side E C ∧
    ∀ C', IsMinCorrR Eg (rbd E) C' → FailsR side E C' → ∑ e ∈ C, Φ e ≤ ∑ e ∈ C', Φ e

/-- Degree of a vertex in an edge list (with multiplicity). -/
def rldeg (P : List (Sym2 (RVx V W))) (x : RVx V W) : ℕ := P.countP (fun e => x ∈ e)

/-- The checks of odd degree in an edge list. -/
def roddD (P : List (Sym2 (RVx V W))) : Finset V := univ.filter (fun v => Odd (rldeg P (RVx.chk v)))

end RCode

end QEC
