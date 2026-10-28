import QECCountComp.Core

/-!
# Region-aware certificate checks for the rotated surface code (dimension 2, `φ = x + 9y`)

One sector of the rotated code is `ℤ²` restricted to `s_lo ≤ x - y ≤ s_hi` (smooth sides) and `r_lo ≤ x + y ≤ r_hi`
(rough sides). The height of a point is `h = s_hi - (x - y)`. The canonical choices of the rules bulge towards larger
`x - y`, so the FULL rules are valid except near the top side `h = 0`. A window whose first vertex has height `h0` is
tested with the region-aware rules of the certificate generator tm2d_aug_omp (`excluded_c` with `ceil = h0`): every point of an
alternative has `x - y ≤ h0`, relative to the window's first vertex.

`checkWA hN h0 w W` is `checkW 2 [1, 9] w W` plus two conditions on the points `q` of the alternative (coordinates
relative to the window's first vertex):
- top side: `x - y ≤ h0`;
- bottom side: `x - y ≥ minXY w - (1 if h0 < hN else 0)`, where `minXY w` is the least `x - y` over the window's points.

The certificate has near states (pattern, head height `h < HC`) with potentials `G`, and bulk states (pattern) with
potentials `Hb`; a state of head height `h ≥ HC` has the potential `Hb` of its pattern. Rows: near rows (at the actual
heights); interface rows (bulk patterns at head height `HC`: steps that increase `x - y` lead to near states of
height `HC - 1`); bulk rows (bulk patterns at head height `bigH`, which stands for every height far from the top).

Trusted (the proofs are about these functions): `dl2`, `vdisp`, `xyOf`, `minXY`, `checkWA`, the keys and the
certificate checks of the last section. Untrusted (only their outputs are checked): the search `findWA` and its
helpers `dpCeil`, `matchDPA`.
-/

namespace QECComp

/-- The tie-break weights: `φ(x, y) = x + 9y`. -/
def cA : List Int := [1, 9]

/-- A head height far from the top side, standing for every such height. -/
def bigH : Int := 1000000

/-- The change of `x - y` along direction `d` (`0, 1, 2, 3` = `+x, -x, +y, -y`). -/
def dl2 (d : Nat) : Int := if d == 0 then 1 else if d == 1 then -1 else if d == 2 then -1 else 1

/-- The change of `x - y` along a pattern. -/
def vdisp (w : List (Nat × Bool)) : Int := w.foldl (fun s x => s + dl2 x.1) 0

/-- `x - y` of a point of `ℤ²`. -/
def xyOf (p : List Int) : Int := p.getD 0 0 - p.getD 1 0

/-- The least `x - y` over the points of the window (relative to its first vertex, which has `x - y = 0`). -/
def minXY (w : List (Nat × Bool)) : Int :=
  ((walkPts 2 (zeros 2) (w.map Prod.fst)).map xyOf).foldl min 0

/-- The region-aware witness check for a window whose first vertex has height `h0`. -/
def checkWA (hN : Nat) (h0 : Int) (w : List (Nat × Bool)) (W : Wit) : Bool :=
  let lo := minXY w - (if h0 < (hN : Int) then 1 else 0)
  checkW 2 cA w W &&
  (altEdges 2 W.alt).all (fun e => decide (xyOf e.1 ≤ h0) && decide (xyOf e.2 ≤ h0) &&
    decide (lo ≤ xyOf e.1) && decide (lo ≤ xyOf e.2))

/-! ## Search (untrusted: only its output is checked) -/

/-- The least-`Φ` monotone path from `a` to `b` all of whose points (`a` included) have `x - y ≤ ceil`, with its `Φ`,
as directions (tm2d_aug_omp's `canon_phi_c`, by dynamic programming over the grid of the path); `none` if there is
no such path. -/
def dpCeil (ceil : Int) (a b : List Int) : Option (Int × List Nat) :=
  let dx := b.getD 0 0 - a.getD 0 0
  let dy := b.getD 1 0 - a.getD 1 0
  let nx := dx.natAbs
  let ny := dy.natAbs
  let sx : Int := if dx ≥ 0 then 1 else -1
  let sy : Int := if dy ≥ 0 then 1 else -1
  let stx : Nat := if dx ≥ 0 then 0 else 1
  let sty : Nat := if dy ≥ 0 then 2 else 3
  let W := ny + 1
  let INF : Int := 1000000000000
  let xAt (i : Nat) : Int := a.getD 0 0 + sx * i
  let yAt (j : Nat) : Int := a.getD 1 0 + sy * j
  let phiAt (i j : Nat) : Int := xAt i + 9 * yAt j
  let okAt (i j : Nat) : Bool := decide (xAt i - yAt j ≤ ceil)
  -- best[i * W + j] = (Φ, last step: 0 = from (i-1, j), 1 = from (i, j-1))
  let init : Array (Int × Nat) :=
    (Array.replicate ((nx + 1) * W) (INF, 0)).set! 0 (if okAt 0 0 then 0 else INF, 0)
  let best := (List.range ((nx + 1) * W)).foldl (fun best k =>
    let i := k / W
    let j := k % W
    if k == 0 then best else
    let fromX : Int := if i > 0 && okAt i j then
        (let e := best[(i - 1) * W + j]!; if e.1 ≥ INF then INF else e.1 + phiAt (i - 1) j + phiAt i j) else INF
    let fromY : Int := if j > 0 && okAt i j then
        (let e := best[i * W + (j - 1)]!; if e.1 ≥ INF then INF else e.1 + phiAt i (j - 1) + phiAt i j) else INF
    if fromX ≤ fromY then best.set! k (fromX, 0) else best.set! k (fromY, 1)) init
  let fin := best[nx * W + ny]!
  if fin.1 ≥ INF then none else
  let rec back (fuel i j : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if i == 0 && j == 0 then acc else
      let e := best[i * W + j]!
      if e.2 == 0 then back fuel (i - 1) j (stx :: acc) else back fuel i (j - 1) (sty :: acc)
  some (fin.1, back (nx + ny + 1) nx ny [])

/-- The `Φ` standing for "no path under the ceiling". -/
def infPhi : Int := 1000000000000

/-- Least-cost, then least-`Φ` under the ceiling, perfect matching of the points `T` (tm2d_aug_omp's `min_pairing_c`;
cost: ℓ¹ distance; `Φ`: `dpCeil` of each pair, `infPhi` if there is no path), by dynamic programming over subsets.
Returns (cost, `Φ`, pairs). -/
def matchDPA (ceil : Int) (T : Array (List Int)) : Option (Nat × Int × List (Nat × Nat)) :=
  let t := T.size
  if t % 2 == 1 then none else
  let costT : Array Nat := (List.range (t * t)).foldl (fun acc k => acc.push (l1 T[k / t]! T[k % t]!)) #[]
  let phiT : Array Int := (List.range (t * t)).foldl (fun acc k =>
    acc.push (match dpCeil ceil T[k / t]! T[k % t]! with
      | some r => r.1
      | none => infPhi)) #[]
  let N := 1 <<< t
  let INF : Nat := 1 <<< 40
  let init : Array (Nat × Int × Nat × Nat) := (Array.replicate N (INF, 0, 0, 0)).set! 0 (0, 0, 0, 0)
  let best := (List.range N).foldl (fun best m =>
    let e := best[m]!
    if e.1 ≥ INF then best else
    match (List.range t).find? (fun i => (m >>> i) % 2 == 0) with
    | none => best
    | some i =>
      (List.range t).foldl (fun best j =>
        if j ≤ i || (m >>> j) % 2 == 1 then best else
        let m2 := m + (1 <<< i) + (1 <<< j)
        let cc := e.1 + costT[i * t + j]!
        let fp := phiT[i * t + j]!
        let ff := if fp ≥ infPhi || e.2.1 ≥ infPhi then infPhi else e.2.1 + fp
        let e2 := best[m2]!
        if cc < e2.1 || (cc == e2.1 && ff < e2.2.1) then best.set! m2 (cc, ff, i, j) else best) best) init
  let ef := best[N - 1]!
  if ef.1 ≥ INF then none else some (ef.1, ef.2.1, recon best t (N - 1) [])

/-- The region-aware witness search for a window whose first vertex has height `h0`: tm2d_aug_omp's `excluded_c` with
`ceil = h0`, returning the alternative that excludes the window. (M): the least-`Φ` path under the ceiling (a geodesic
inside the region); (P_M): the same path; (J), (P_J): the least-`Φ` paths under the ceiling of an optimal matching.
(S) is the case `n_C = 2`, `n_E = 0` of (P_M): the corner path is a monotone path under the ceiling iff the fourth
corner is under it. -/
def findWA (h0 : Int) (w : List (Nat × Bool)) : Option Wit :=
  let pts := walkPts 2 (zeros 2) (w.map Prod.fst)
  let X := cEdges 2 w
  let Y := eEdges 2 w
  let nC := X.length
  let nE := Y.length
  let a := zeros 2
  let b := pts.getLastD a
  let dist := l1 a b
  let phC := phiE cA X
  let g := dpCeil h0 a b
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
    let T := oddVerts pts (w.map Prod.snd)
    match matchDPA h0 T with
    | none => none
    | some (cost, f, pairs) =>
      if nC > cost || (nC == cost && decide (f < infPhi) && decide (f < phC)) then
        let alt := pairs.flatMap (fun pr => match dpCeil h0 T[pr.1]! T[pr.2]! with
          | some r => chainAlt 2 T[pr.1]! r.2
          | none => [])
        some ⟨false, if nC > cost || nodupE (altEdges 2 alt) then alt else oddAlt 2 alt⟩
      else none

/-! ## The augmented certificate -/

/-- Parameters of an augmented certificate: memory `K`, near range `HC`, bottom-side slack range `hN` (windows whose
first vertex has height `< hN` may dip one below their least `x - y`), scaled weights (as in `Params`), `λ`, `Hmin`,
start constant bound. -/
structure ParamsA where
  K : Nat
  HC : Nat
  hN : Nat
  wE : Nat
  wC : Nat
  Q : Nat
  lamN : Nat
  lamD : Nat
  Hmin : Nat
  K0n : Nat
  K0d : Nat

/-- The window `u`, whose first vertex has height `h0`, is excluded (found and checked). -/
def exclWinA (P : ParamsA) (h0 : Int) (u : List (Nat × Bool)) : Bool :=
  match findWA h0 u with
  | some W => checkWA P.hN h0 u W
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is excluded; `h0` is the height of the first
vertex of `u`, so the window starting after `j` steps has first-vertex height `h0 - vdisp (u.take j)`. -/
def exclEndingA (P : ParamsA) (h0 : Int) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) &&
    exclWinA P (h0 - vdisp (u.take (u.length - m))) (u.drop (u.length - m)))

/-- The steps of a pattern in base 4, first step least significant. -/
def stepCode : List (Nat × Bool) → Nat
  | [] => 0
  | x :: w => x.1 % 4 + 4 * stepCode w

/-- The labels of a pattern in base 2 (C = 1), first label least significant. -/
def labCode : List (Nat × Bool) → Nat
  | [] => 0
  | x :: w => (if x.2 then 1 else 0) + 2 * labCode w

/-- The key of the state `(σ, h)` with `K` steps and head height `h`: steps, then labels from bit `2K`, then `h` from
bit `3K`. It is an order-preserving compression of tm2d_aug_omp's 64-bit key (step `i` in bits `2i, 2i+1`, label `i`
in bit `32 + i`, `h` from bit 48), so the generator writes the records in the C++ order. Bulk states have `h = 0`. -/
def ckeyA (K : Nat) (σ : List (Nat × Bool)) (h : Nat) : Nat := stepCode σ + 4 ^ K * labCode σ + 8 ^ K * h

/-- The pattern of `K` steps of the key `k`. -/
def decodeA (K k : Nat) : List (Nat × Bool) :=
  (List.range K).map (fun i => ((k / 4 ^ i) % 4, (k / 4 ^ K / 2 ^ i) % 2 == 1))

/-- The head height of the key `k`. -/
def heightOf (K k : Nat) : Nat := k / 8 ^ K

/-- The potential of the state `(σ, h)` (head height `h`): `G` if `0 ≤ h < HC` and listed, `Hb` if `h ≥ HC` and the
pattern is listed. -/
def potA (P : ParamsA) (nk nG bk bH : Array Nat) (σ : List (Nat × Bool)) (h : Int) : Option Nat :=
  if h < 0 then none
  else if h < (P.HC : Int) then (lookup nk (ckeyA P.K σ h.toNat)).map (fun j => nG[j]!)
  else (lookup bk (ckeyA P.K σ 0)).map (fun j => bH[j]!)

/-- The weighted sum over the successors of the state `(s, h)` (head height `h`). A step to height `< 0` would cross
the top side: there is no such edge. -/
def rowSumA (P : ParamsA) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (h : Int) : Option Nat :=
  (candList 2).foldl (fun acc x =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [x]
      let h0 := h + vdisp s
      let h2 := h - dl2 x.1
      if !selfAvoid 2 u || decide (h2 < 0) then some tot
      else match potA P nk nG bk bH u.tail h2 with
        | some H => if exclWinA P h0 u then some tot else some (tot + (if x.2 then P.wC else P.wE) * H)
        | none => if exclEndingA P h0 u then some tot else none) (some 0)

/-- A row: `Hmin ≤ H` and the weighted successor sum is at most `λ H`. -/
def rowOKA (P : ParamsA) (nk nG bk bH : Array Nat) (s : List (Nat × Bool)) (h : Int) (H : Nat) : Bool :=
  decide (0 < P.Hmin) && decide (P.Hmin ≤ H) &&
  match rowSumA P nk nG bk bH s h with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * H)
  | none => false

/-- The near rows of the entries `lo, …, hi - 1` (head height `heightOf K k < HC`). -/
def nearRowsOKA (P : ParamsA) (nk nG bk bH : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i =>
    let k := nk[i]!
    decide (heightOf P.K k < P.HC) &&
      rowOKA P nk nG bk bH (decodeA P.K k) ((heightOf P.K k : Nat) : Int) nG[i]!)

/-- The interface rows (head height `HC`) of the bulk entries `lo, …, hi - 1`. -/
def ifRowsOKA (P : ParamsA) (nk nG bk bH : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i =>
    rowOKA P nk nG bk bH (decodeA P.K bk[i]!) (P.HC : Int) bH[i]!)

/-- The bulk rows (head height `bigH`) of the bulk entries `lo, …, hi - 1`. -/
def bulkRowsOKA (P : ParamsA) (nk nG bk bH : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i =>
    rowOKA P nk nG bk bH (decodeA P.K bk[i]!) bigH bH[i]!)

/-- Start completeness from a first vertex of height `h0`: every self-avoiding extension to `K` steps that stays at
heights `≥ 0` is excluded on the way or is a listed state. -/
def dfsA (P : ParamsA) (nk nG bk bH : Array Nat) (h0 : Int) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (potA P nk nG bk bH pfx (h0 - vdisp pfx)).isSome
  | r + 1, pfx => (candList 2).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid 2 u || decide (h0 - vdisp u < 0) || exclEndingA P h0 u || dfsA P nk nG bk bH h0 r u)

/-- Start completeness from the height `h0`, by the first step. -/
def dfsTopA (P : ParamsA) (nk nG bk bH : Array Nat) (h0 : Int) (j : Nat) : Bool :=
  match (candList 2)[j]? with
  | some x => !selfAvoid 2 [x] || decide (h0 - vdisp [x] < 0) || exclEndingA P h0 [x] ||
      dfsA P nk nG bk bH h0 (P.K - 1) [x]
  | none => true

/-- Start completeness from the height `h0`, every first step. -/
def dfsHA (P : ParamsA) (nk nG bk bH : Array Nat) (h0 : Int) : Bool :=
  (List.range (candList 2).length).all (dfsTopA P nk nG bk bH h0)

/-- `f` holds at the `cnt` integers from `lo`. -/
def rangeAllA (lo : Int) (cnt : Nat) (f : Int → Bool) : Bool := (List.range cnt).all (fun i => f (lo + i))

/-- Near consistency, for the heights not covered by a start check of their own: for every bulk entry `j` in
`lo, …, hi - 1` (pattern `σ`) and every first-vertex height `h0` in `[h1, HC + K]` whose head height `h0 - vdisp σ` is
below `HC`, the near state `(σ, h0 - vdisp σ)` is listed. With `dfsHA` at `bigH`, this gives start completeness from
the heights `h0 ≥ h1` for `h1 ≥ K`: a `K`-step walk from `h0 ≥ K` stays at heights `≥ 0`, and each of its windows of
`m` edges starts at height `≥ m`, while a witness accepted at `bigH` lies in the window's bounding box, where
`x - y ≤ m`; so it passes the top check at the true height too. -/
def consistOKA (P : ParamsA) (nk nG bk bH : Array Nat) (h1 lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun j =>
    let σ := decodeA P.K bk[j]!
    (List.range' h1 (P.HC + P.K + 1 - h1)).all (fun h0 =>
      let h := (h0 : Int) - vdisp σ
      decide (h ≥ (P.HC : Int)) || (decide (0 ≤ h) && (potA P nk nG bk bH σ h).isSome)))

/-- The weights `ω_E^{K - c} ω_C^c` (`c` = the number of C-labels), scaled by `Q^K`. -/
def wtTable (P : ParamsA) : Array Nat := ((List.range (P.K + 1)).map (fun c => P.wE ^ (P.K - c) * P.wC ^ c)).toArray

/-- The start sums (scaled by `Q^K`), in one pass: entry `h0 ≤ HC + K` is the sum of `ω H` over the listed states
whose first vertex has height `h0` (near states `(σ, h)` with `h + vdisp σ = h0`, and bulk patterns whose head height
`h0 - vdisp σ` is at least `HC`); entry `HC + K + 1` is the sum over all bulk patterns (first vertex far from the top). -/
def startSumsA (P : ParamsA) (nk nG bk bH : Array Nat) : Array Nat :=
  let n := P.HC + P.K + 1
  let wt := wtTable P
  let nC (σ : List (Nat × Bool)) : Nat := (σ.filter (fun x => x.2)).length
  let a0 : Array Nat := Array.replicate (n + 1) 0
  let a1 := (List.range nk.size).foldl (fun acc i =>
    let k := nk[i]!
    let σ := decodeA P.K k
    let h0 : Int := ((heightOf P.K k : Nat) : Int) + vdisp σ
    if 0 ≤ h0 ∧ h0 < (n : Int) then acc.modify h0.toNat (· + wt[nC σ]! * nG[i]!) else acc) a0
  (List.range bk.size).foldl (fun acc j =>
    let σ := decodeA P.K bk[j]!
    let v := wt[nC σ]! * bH[j]!
    let acc := acc.modify n (· + v)
    (List.range n).foldl (fun acc (h0 : Nat) =>
      if ((h0 : Int) - vdisp σ) < (P.HC : Int) then acc else acc.modify h0 (· + v)) acc) a1

/-- The start bounds: for every first-vertex height `h0 ≤ HC + K` and for the far heights,
`(ω_E + ω_C)² · S(h0) / Hmin ≤ K0n / K0d`, scaled by `Q^(K+2) K0d`. -/
def startOKA (P : ParamsA) (nk nG bk bH : Array Nat) : Bool :=
  let S := startSumsA P nk nG bk bH
  decide (S.size = P.HC + P.K + 2) &&
  S.all (fun s => decide ((P.wE + P.wC) ^ 2 * s * P.K0d ≤ P.K0n * P.Hmin * P.Q ^ (P.K + 2)))

end QECComp
