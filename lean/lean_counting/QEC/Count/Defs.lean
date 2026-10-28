import QEC.Graph.Basic
import QEC.Count.OddEdges
import QECCountComp.Core
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Definitions: noise, decoders, box codes, labelled walks

* `PrIID Eg p A`: the probability of the event `A` when every edge of `Eg` is in the error independently with
  probability `p`.
* `IsMinCorr`, `FailsB`, `PfailMW`: minimum-weight corrections with uniform weights, failure (the parity at `b1`
  differs from the error's), and the probability that SOME minimum-weight correction fails (any tie rule).
* `PfailDec`, `PfailML`: decoders from the syndrome to the class, and the optimum over all of them (ML decoding).
* `BoxV`, `boxEdges`: the box code. Checks are the points of `∏ [0, N i)`, edges join points at ℓ¹ distance `1`,
  half-edges join the points with coordinate `a` equal to `0` to `b1` and those with coordinate `a` equal to
  `N a - 1` to `b2`. With `n = 2`, `a = 0` this is the unrotated planar code (one error sector, code capacity);
  with `n = 3`, coordinates `(t, X, Y)`, `a = 2`, it is the space-time decoding graph of the planar code under
  phenomenological noise (each edge is one error location).
* Labelled walks of the lattice (patterns, from the computational core `QECComp`): `Excl`, `Legal`, `Succ`, `pats`,
  `wtW`.
-/

namespace QEC

open Finset
open scoped symmDiff

/-! ## i.i.d. noise -/

section IID

variable {α : Type*} [DecidableEq α]

open scoped Classical in
/-- Every edge of `Eg` is in the error independently with probability `p`: the probability of the event `A`. -/
noncomputable def PrIID (Eg : Finset α) (p : ℝ) (A : Finset α → Prop) : ℝ :=
  ∑ E ∈ Eg.powerset.filter A, p ^ #E * (1 - p) ^ #(Eg \ E)

end IID

/-! ## Decoders -/

section Decoding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `C` is a correction (edges of the graph with boundary `A`) of least size: a minimum-weight correction with
uniform weights. -/
def IsMinCorr (Eg : Finset (Sym2 (Vx V))) (A : Finset V) (C : Finset (Sym2 (Vx V))) : Prop :=
  C ⊆ Eg ∧ bd C = A ∧ ∀ C' ⊆ Eg, bd C' = A → #C ≤ #C'

/-- The correction `C` fails for the error `E`: its parity at `b1` differs from that of `E`. -/
def FailsB (E C : Finset (Sym2 (Vx V))) : Prop := ¬ (Odd (vdeg C .b1) ↔ Odd (vdeg E .b1))

/-- The probability that some minimum-weight correction of the error's syndrome fails. -/
noncomputable def PfailMW (Eg : Finset (Sym2 (Vx V))) (p : ℝ) : ℝ :=
  PrIID Eg p (fun E => ∃ C, IsMinCorr Eg (bd E) C ∧ FailsB E C)

/-- The failure probability of a decoder that maps the syndrome to a guess of the class (the parity at `b1`). -/
noncomputable def PfailDec (Eg : Finset (Sym2 (Vx V))) (p : ℝ) (dec : Finset V → Bool) : ℝ :=
  PrIID Eg p (fun E => dec (bd E) ≠ decide (Odd (vdeg E .b1)))

/-- The optimal (maximum-likelihood) failure probability: the least failure probability over all decoders. -/
noncomputable def PfailML (Eg : Finset (Sym2 (Vx V))) (p : ℝ) : ℝ := ⨅ dec : Finset V → Bool, PfailDec Eg p dec

/-- `Φ(C) = ∑_{e ∈ C} Φ(e)`. -/
def PhiS (Φ : Sym2 (Vx V) → ℤ) (C : Finset (Sym2 (Vx V))) : ℤ := ∑ e ∈ C, Φ e

/-- `C` is a failing minimum-weight correction of least `Φ` among the failing ones. -/
def IsPhiMinFail (Eg : Finset (Sym2 (Vx V))) (Φ : Sym2 (Vx V) → ℤ) (E C : Finset (Sym2 (Vx V))) : Prop :=
  IsMinCorr Eg (bd E) C ∧ FailsB E C ∧
    ∀ C', IsMinCorr Eg (bd E) C' → FailsB E C' → PhiS Φ C ≤ PhiS Φ C'

end Decoding

/-! ## Box codes -/

section Box

/-- The checks of the box code: the points of `∏ [0, N i)`. -/
abbrev BoxV (n : ℕ) (N : Fin n → ℕ) := (i : Fin n) → Fin (N i)

variable {n : ℕ} {N : Fin n → ℕ}

/-- The ℓ¹ distance between two checks. -/
def l1B (u v : BoxV n N) : ℕ := ∑ i, Int.natAbs ((u i : ℤ) - (v i : ℤ))

variable (n N) in
/-- The edges of the box code: pairs of checks at ℓ¹ distance `1`, half-edges from the checks with coordinate `a`
equal to `0` to `b1`, and from those with coordinate `a` equal to `N a - 1` to `b2`. -/
def boxEdges (a : Fin n) : Finset (Sym2 (Vx (BoxV n N))) :=
  (((univ ×ˢ univ).filter (fun uv : BoxV n N × BoxV n N => l1B uv.1 uv.2 = 1)).image
      (fun uv => s(Vx.det uv.1, Vx.det uv.2))) ∪
    ((univ.filter (fun u : BoxV n N => (u a : ℕ) = 0)).image (fun u => s(Vx.det u, Vx.b1))) ∪
    ((univ.filter (fun u : BoxV n N => (u a : ℕ) + 1 = N a)).image (fun u => s(Vx.det u, Vx.b2)))

/-- The coordinates of a check as a list of integers. -/
def pos (v : BoxV n N) : List ℤ := List.ofFn (fun i => ((v i : ℕ) : ℤ))

/-- `φ` on checks, `Φ` on edges (`φ(a) + φ(b)` for an edge between checks; `0` for half-edges). -/
def phiBox (c : List ℤ) : Sym2 (Vx (BoxV n N)) → ℤ :=
  Sym2.lift ⟨fun x y => match x, y with
    | .det u, .det v => QECComp.phiP c (pos u) + QECComp.phiP c (pos v)
    | _, _ => 0, fun x y => by cases x <;> cases y <;> simp [add_comm]⟩

end Box

/-! ## Labelled walks -/

section Walks

open QECComp

variable (n : ℕ) (c : List ℤ)

/-- An excluded window: some witness passes the check. -/
def Excl (w : List (ℕ × Bool)) : Prop := ∃ W, checkW n c w W = true

/-- The walk of a pattern from the origin has no repeated point. -/
def SelfAv (w : List (ℕ × Bool)) : Prop := (walkPts n (zeros n) (w.map Prod.fst)).Nodup

/-- The directions of a pattern are valid. -/
def DirOK (w : List (ℕ × Bool)) : Prop := ∀ x ∈ w, x.1 < 2 * n

/-- Legal labelled walks for windows of up to `M` edges: self-avoiding, valid directions, and no window of
`2..M` edges excluded. -/
def Legal (M : ℕ) (w : List (ℕ × Bool)) : Prop :=
  SelfAv n w ∧ DirOK n w ∧ ∀ i m, 2 ≤ m → m ≤ M → i + m ≤ w.length → ¬ Excl n c ((w.drop i).take m)

/-- The candidate steps: every direction with both labels. -/
def cands : Finset (ℕ × Bool) := Finset.range (2 * n) ×ˢ Finset.univ

/-- `x` is a legal successor of the state `s`: the walk stays self-avoiding and no window of `2..|s|+1` edges
ending with the new edge is excluded. -/
def Succ (s : List (ℕ × Bool)) (x : ℕ × Bool) : Prop :=
  x.1 < 2 * n ∧ SelfAv n (s ++ [x]) ∧
    ∀ m, 2 ≤ m → m ≤ s.length + 1 → ¬ Excl n c ((s ++ [x]).drop (s.length + 1 - m))

/-- All patterns of length `L` over the candidate steps. -/
def pats : ℕ → Finset (List (ℕ × Bool))
  | 0 => {[]}
  | L + 1 => (cands n ×ˢ pats L).image (fun p => p.1 :: p.2)

/-- The weight of a labelled walk: `ω_E` per E-edge and `ω_C` per C-edge. -/
def wtW (ωE ωC : ℝ) (w : List (ℕ × Bool)) : ℝ := (w.map (fun x => if x.2 then ωC else ωE)).prod

end Walks

end QEC
