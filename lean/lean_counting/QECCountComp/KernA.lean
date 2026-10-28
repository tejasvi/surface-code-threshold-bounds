import QECCountComp.AugC
import QECCountComp.KernT

/-!
# Kernel route for the augmented certificates (rotated code)

The checks of `AugC.lean`, written for evaluation by the kernel (`decide +kernel`), generic in the lookups as
`KernT.lean`:

* near states are reached by `fN (ckeyA K σ h)`, bulk states by `fB (ckeyA K σ 0)`, each returning (potential, mask); a
  near mask marks the candidate steps whose listed successor the generator found excluded (full window); a bulk entry
  carries two masks `m₀ + 256 m₁`, for the head heights `bigH` and `HC`; a mask is only a hint, every claimed exclusion
  is found again and checked (`exclWinAK`);
* the witness search `findWAK` is `findWA` with the least-`Φ` path under the ceiling computed row by row on lists
  (`dpCeilK`, the recurrence and tie rule of `dpCeil`) and the matching found by recursion (`matchRecA`); it is
  untrusted, its output is checked by `checkWA`;
* start completeness tries the extension before the exclusion search (`dfsAK`);
* the start sums are sums over the entries (`nearContribA`, `bulkContribA`), one per first-vertex height `h0 ≤ HC + K`
  and one for the far heights.
-/

namespace QECComp

/-- One row of the table of `dpCeil`: the entries `(Φ, last step)` of row `i` from those of row `i - 1` (`prev`; empty
for `i = 0`). -/
def dpRowK (INF : Int) (okAt : Nat → Nat → Bool) (phiAt : Nat → Nat → Int) (ny i : Nat) (prev : List (Int × Nat)) :
    List (Int × Nat) :=
  (List.range (ny + 1)).foldl (fun acc j =>
    if i == 0 && j == 0 then acc ++ [(if okAt 0 0 then 0 else INF, 0)]
    else
      let fromX : Int := if i > 0 && okAt i j then
          (let e := prev.getD j (INF, 0); if e.1 ≥ INF then INF else e.1 + phiAt (i - 1) j + phiAt i j) else INF
      let fromY : Int := if j > 0 && okAt i j then
          (let e := acc.getD (j - 1) (INF, 0); if e.1 ≥ INF then INF else e.1 + phiAt i (j - 1) + phiAt i j) else INF
      if fromX ≤ fromY then acc ++ [(fromX, 0)] else acc ++ [(fromY, 1)]) []

/-- The steps back from `(i, j)` to `(0, 0)` through the table `rows` (as `dpCeil`'s `back`). -/
def dpBackK (rows : List (List (Int × Nat))) (stx sty : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, acc => acc
  | fuel + 1, i, j, acc =>
    if i == 0 && j == 0 then acc else
    let e := (rows.getD i []).getD j (0, 0)
    if e.2 == 0 then dpBackK rows stx sty fuel (i - 1) j (stx :: acc) else dpBackK rows stx sty fuel i (j - 1) (sty :: acc)

/-- `dpCeil` on lists: the least-`Φ` monotone path from `a` to `b` under the ceiling `x - y ≤ ceil` (same recurrence and
tie rule). -/
def dpCeilK (ceil : Int) (a b : List Int) : Option (Int × List Nat) :=
  let dx := b.getD 0 0 - a.getD 0 0
  let dy := b.getD 1 0 - a.getD 1 0
  let nx := dx.natAbs
  let ny := dy.natAbs
  let sx : Int := if dx ≥ 0 then 1 else -1
  let sy : Int := if dy ≥ 0 then 1 else -1
  let stx : Nat := if dx ≥ 0 then 0 else 1
  let sty : Nat := if dy ≥ 0 then 2 else 3
  let INF : Int := 1000000000000
  let xAt (i : Nat) : Int := a.getD 0 0 + sx * i
  let yAt (j : Nat) : Int := a.getD 1 0 + sy * j
  let phiAt (i j : Nat) : Int := xAt i + 9 * yAt j
  let okAt (i j : Nat) : Bool := decide (xAt i - yAt j ≤ ceil)
  let rows := (List.range (nx + 1)).foldl (fun acc i => acc ++ [dpRowK INF okAt phiAt ny i (acc.getLastD [])]) []
  let fin := (rows.getD nx []).getD ny (INF, 0)
  if fin.1 ≥ INF then none else some (fin.1, dpBackK rows stx sty (nx + ny + 1) nx ny [])

/-- Least-cost, then least-`Φ` under the ceiling, perfect matching by recursion (as `matchDPA`). -/
def matchRecA (ceil : Int) : Nat → List (List Int) → Option (Nat × Int × List (List Int × List Int))
  | 0, _ => none
  | _, [] => some (0, 0, [])
  | fuel + 1, a :: rest =>
    rest.foldl (fun best b =>
      match matchRecA ceil fuel (rest.erase b) with
      | none => best
      | some (cc, ff, ps) =>
        let cost := cc + l1 a b
        let fp : Int := match dpCeilK ceil a b with
          | some r => r.1
          | none => infPhi
        let phi := if fp ≥ infPhi || ff ≥ infPhi then infPhi else ff + fp
        match best with
        | none => some (cost, phi, (a, b) :: ps)
        | some (bc, bf, _) => if cost < bc || (cost == bc && decide (phi < bf)) then some (cost, phi, (a, b) :: ps)
            else best) none

/-- The region-aware witness search of `findWA`, with `dpCeilK` and `matchRecA` (untrusted). -/
def findWAK (h0 : Int) (w : List (Nat × Bool)) : Option Wit :=
  let pts := walkPts 2 (zeros 2) (w.map Prod.fst)
  let X := cEdges 2 w
  let Y := eEdges 2 w
  let nC := X.length
  let nE := Y.length
  let a := zeros 2
  let b := pts.getLastD a
  let dist := l1 a b
  let phC := phiE cA X
  let g := dpCeilK h0 a b
  let geo : List (List Int × Nat) := match g with
    | some r => chainAlt 2 a r.2
    | none => []
  let fg : Int := match g with
    | some r => r.1
    | none => infPhi
  if nC > nE + dist then (if g.isSome then some ⟨true, geo⟩ else none)
  else if nC > 0 && nC == nE + dist && g.isSome && decide (phiE cA Y + fg < phC) then some ⟨true, geo⟩
  else if nC < 2 then none
  else
    let T := oddVertsL pts (w.map Prod.snd)
    match matchRecA h0 (T.length + 1) T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && decide (f < infPhi) && decide (f < phC)) then
        let alt := pairs.flatMap (fun pr => match dpCeilK h0 pr.1 pr.2 with
          | some r => chainAlt 2 pr.1 r.2
          | none => [])
        some ⟨false, if nC > cost || nodupE (altEdges 2 alt) then alt else oddAlt 2 alt⟩
      else none

/-- The window `u`, whose first vertex has height `h0`, is excluded by a witness found by `findWAK` and checked. -/
def exclWinAK (P : ParamsA) (h0 : Int) (u : List (Nat × Bool)) : Bool :=
  match findWAK h0 u with
  | some W => checkWA P.hN h0 u W
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded (as `exclEndingA`, with
`exclWinAK`). -/
def exclEndingAK (P : ParamsA) (h0 : Int) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) &&
    exclWinAK P (h0 - vdisp (u.take (u.length - m))) (u.drop (u.length - m)))

/-- The potential and mask of the state `(σ, h)` (head height `h`): none if `h < 0`, from the near store if `h < HC`,
from the bulk store otherwise. -/
def potAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (σ : List (Nat × Bool)) (h : Int) : Option (Nat × Nat) :=
  if h < 0 then none
  else if h < (P.HC : Int) then fN (ckeyA P.K σ h.toNat)
  else fB (ckeyA P.K σ 0)

/-- The weighted sum over the successors of the state `(s, h)` with mask `mask` (`none` if a candidate is neither
excluded nor listed, or a claimed exclusion fails). A step to height `< 0` would cross the top side. -/
def rowSumAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (mask : Nat) (s : List (Nat × Bool)) (h : Int) :
    Option Nat :=
  ((candList 2).zip (List.range 8)).foldl (fun acc xi =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [xi.1]
      let h0 := h + vdisp s
      let h2 := h - dl2 xi.1.1
      if !selfAvoid 2 u || decide (h2 < 0) then some tot
      else match potAK P fN fB u.tail h2 with
        | some hm =>
          if mask / 2 ^ xi.2 % 2 == 1 then (if exclWinAK P h0 u then some tot else none)
          else some (tot + (if xi.1.2 then P.wC else P.wE) * hm.1)
        | none => if exclEndingAK P h0 u then some tot else none) (some 0)

/-- A row: `Hmin ≤ H` and the weighted successor sum is at most `λ H`. -/
def rowCheckAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (mask : Nat) (s : List (Nat × Bool)) (h : Int)
    (H : Nat) : Bool :=
  decide (0 < P.Hmin) && decide (P.Hmin ≤ H) &&
  match rowSumAK P fN fB mask s h with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * H)
  | none => false

/-- The row of a near entry `(ckeyA K σ h, G, mask)`, `h < HC`. -/
def nearRowAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (e : Nat × Nat × Nat) : Bool :=
  decide (heightOf P.K e.1 < P.HC) &&
    rowCheckAK P fN fB e.2.2 (decodeA P.K e.1) ((heightOf P.K e.1 : Nat) : Int) e.2.1

/-- The two rows of a bulk entry `(ckeyA K σ 0, Hb, masks)`: at the head heights `bigH` and `HC`. -/
def bulkRowAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (e : Nat × Nat × Nat) : Bool :=
  let s := decodeA P.K e.1
  rowCheckAK P fN fB (e.2.2 % 256) s bigH e.2.1 && rowCheckAK P fN fB (e.2.2 / 256 % 256) s P.HC e.2.1

/-- Start completeness from a first vertex of height `h0` (as `dfsA`, the extension tried first). -/
def dfsAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (h0 : Int) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (potAK P fN fB pfx (h0 - vdisp pfx)).isSome
  | r + 1, pfx => (candList 2).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || decide (h0 - vdisp u < 0) || dfsAK P fN fB h0 r u || exclEndingAK P h0 u)

/-- The start check from the height `h0` for the walks that continue the prefix `pfx` with the candidate steps of
indices `js`, then with any `K - |pfx| - |js|` further steps. -/
def dfsPreAK (P : ParamsA) (fN fB : Nat → Option (Nat × Nat)) (h0 : Int) : List Nat → List (Nat × Bool) → Bool
  | [], pfx => dfsAK P fN fB h0 (P.K - pfx.length) pfx
  | j :: js, pfx =>
    match (candList 2)[j]? with
    | some x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || decide (h0 - vdisp u < 0) || dfsPreAK P fN fB h0 js u || exclEndingAK P h0 u
    | none => true

/-- The first-vertex heights by index: `i` for `i ≤ HC + K`, then `bigH`. -/
def offA (P : ParamsA) (i : Nat) : Int := if i < P.HC + P.K + 1 then (i : Int) else bigH

/-- The weight `ω_E^{K-c} ω_C^c` of a pattern with `c` C-labels (scaled by `Q^K`). -/
def wtA (P : ParamsA) (σ : List (Nat × Bool)) : Nat :=
  let c := (σ.filter (fun x => x.2)).length
  P.wE ^ (P.K - c) * P.wC ^ c

/-- The contributions of a near entry to the start sums (index `h0 = h + vdisp σ` if `h0 ≤ HC + K`). -/
def nearContribA (P : ParamsA) (e : Nat × Nat × Nat) : List Nat :=
  let σ := decodeA P.K e.1
  let h0 : Int := ((heightOf P.K e.1 : Nat) : Int) + vdisp σ
  (List.range (P.HC + P.K + 2)).map (fun i =>
    if i < P.HC + P.K + 1 && h0 == (i : Int) then wtA P σ * e.2.1 else 0)

/-- The contributions of a bulk entry to the start sums: the far heights (last index), and every `h0 ≤ HC + K` from
which its head height is at least `HC`. -/
def bulkContribA (P : ParamsA) (e : Nat × Nat × Nat) : List Nat :=
  let σ := decodeA P.K e.1
  (List.range (P.HC + P.K + 2)).map (fun i =>
    if i == P.HC + P.K + 1 then wtA P σ * e.2.1
    else if ((i : Int) - vdisp σ) < (P.HC : Int) then 0 else wtA P σ * e.2.1)

/-- The start bounds from the near and bulk totals (as `startOKA`). -/
def startOKAK (P : ParamsA) (totN totB : List Nat) : Bool :=
  (List.range (P.HC + P.K + 2)).all (fun i =>
    decide ((P.wE + P.wC) ^ 2 * (totN.getD i 0 + totB.getD i 0) * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2)))

end QECComp
