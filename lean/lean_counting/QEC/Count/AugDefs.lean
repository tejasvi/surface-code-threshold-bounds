import QEC.Count.TorDefs
import QEC.Count.RotGeom
import QECCountComp.AugC

/-!
# The rotated code with the augmented (region-aware) certificate: definitions (Theorem B at `p ≤ 93/2000`)

* Heights. In the rotated region (`RotGeom`: checks with `0 ≤ U + V ≤ d - 2`, `-1 ≤ U - V ≤ d - 1`) the height of a
  check is `heightR v = (d - 1) - (U - V)`, its distance below the top smooth side. A step in direction `dd` changes
  the height by `-dl2 dd` (`nxtA`).
* Exclusions. `ExclA hN h0 w`: the window `w`, whose first vertex has height `h0`, is excluded by a witness passing
  `checkWA` (`QECCountComp/AugC.lean`). `ExA hN h0 w` also counts a window that reaches a negative height (it would
  cross the top side: such walks do not exist in the region). The counting layer is `CountingT` with `nxt = nxtA`,
  `Ex = ExA hN` (heights in place of seam offsets; no wrap-around).
* The certificate (`ParamsA`, near keys `nk` with potentials `nG`, bulk keys `bk` with potentials `bH`): `headHA`,
  `IsStA`, `HofA`, and `CertOKA`, the checks that the native modules establish.
-/

namespace QEC

open Finset QECComp

/-- The height of a check of the rotated code: its distance below the top smooth side `U - V = d - 1`. -/
def heightR {d : ℕ} (v : RChk d) : ℤ := (d : ℤ) - 1 - (v.1.1 - v.1.2)

/-- The height after a step in direction `dd`. -/
def nxtA (h : ℤ) (dd : ℕ) : ℤ := h - dl2 dd

/-- An excluded window at first-vertex height `h0` (region-aware rules with bottom-side slack range `hN`). -/
def ExclA (hN : ℕ) (h0 : ℤ) (w : List (ℕ × Bool)) : Prop := ∃ W, checkWA hN h0 w W = true

/-- An excluded window, or one that reaches a negative height. -/
def ExA (hN : ℕ) (h0 : ℤ) (w : List (ℕ × Bool)) : Prop :=
  ExclA hN h0 w ∨ ∃ i ≤ w.length, h0 - vdisp (w.take i) < 0

section Cert

variable (P : ParamsA) (nk nG bk bH : Array ℕ)

/-- The head height of a state (pattern `s`, first-vertex height `h0`). -/
def headHA (s : List (ℕ × Bool)) (h0 : ℤ) : ℤ := h0 - vdisp s

/-- The states of the augmented certificate: length `K`, valid directions, and listed (near potential if the head
height is below `HC`, bulk potential otherwise). -/
def IsStA (s : List (ℕ × Bool)) (h0 : ℤ) : Prop :=
  s.length = P.K ∧ DirOK 2 s ∧ (potA P nk nG bk bH s (headHA s h0)).isSome

/-- The potential of a state of the augmented certificate. -/
def HofA (s : List (ℕ × Bool)) (h0 : ℤ) : ℕ := (potA P nk nG bk bH s (headHA s h0)).getD 0

/-- The checks of an augmented certificate. -/
structure CertOKA : Prop where
  hK : 2 ≤ P.K
  hHC : 2 * P.K + 2 ≤ P.HC
  hHC2 : P.HC ≤ 255
  hN0 : P.hN = 0
  hQ : 0 < P.Q
  hlamD : 0 < P.lamD
  hK0d : 0 < P.K0d
  near : nearRowsOKA P nk nG bk bH 0 nk.size = true
  iface : ifRowsOKA P nk nG bk bH 0 bk.size = true
  bulk : bulkRowsOKA P nk nG bk bH 0 bk.size = true
  dfsBig : dfsHA P nk nG bk bH bigH = true
  dfsNear : rangeAllA 0 (P.HC + P.K + 1) (dfsHA P nk nG bk bH) = true
  start : startOKA P nk nG bk bH = true

end Cert

end QEC
