import QECCountComp.Core

/-!
# SAFE rules (dimension 2): exclusions valid in boxes and in the rotated code's region

For the rotated surface code (smooth sides `x - y = const`) the tie-break exclusions must use alternatives that stay
inside the region. A SAFE exclusion has TWO witnesses, each accepted by `checkW`: the first with every point's
`x - y` in `[lo, hi + 1]`, the second in `[lo - 1, hi]`, where `[lo, hi]` is the range of `x - y` over the window's
points. In a region whose smooth sides are `x - y = s₀` and `x - y = s₁` with `s₁ - s₀` larger than the window span,
one of the two lies inside.

The search `findWS` reproduces the generator's SAFE tests (tm2d with `TM2D_SAFE=1`): (M), (J) strict; (P_M), (P_J)
with the larger of the least `Φ` over monotone paths with profile in `[lo', hi' + 1]` and in `[lo' - 1, hi']` (`lo'`,
`hi'` the range of the two endpoints of the path); (S) is the case `n_C = 2`, `n_E = 0` of (P_M). Only its output is
used, after `checkWS`.
-/

namespace QECComp

/-- `x - y` of a point of `ℤ²`. -/
def dxy (p : List Int) : Int := p.getD 0 0 - p.getD 1 0

/-- Every end of an edge of the alternative has `x - y` in `[lo, hi]`. -/
def profOK (n : Nat) (alt : List (List Int × Nat)) (lo hi : Int) : Bool :=
  (altEdges n alt).all (fun e => decide (lo ≤ dxy e.1) && decide (dxy e.1 ≤ hi) && decide (lo ≤ dxy e.2) &&
    decide (dxy e.2 ≤ hi))

/-- The least and largest `x - y` over the points of the window. -/
def winRange (n : Nat) (w : List (Nat × Bool)) : Int × Int :=
  let ds := (walkPts n (zeros n) (w.map Prod.fst)).map dxy
  (ds.foldl min 0, ds.foldl max 0)

/-- The SAFE witness check. -/
def checkWS (n : Nat) (c : List Int) (w : List (Nat × Bool)) (W1 W2 : Wit) : Bool :=
  let r := winRange n w
  checkW n c w W1 && checkW n c w W2 && profOK n W1.alt r.1 (r.2 + 1) && profOK n W2.alt (r.1 - 1) r.2

/-! ## Search (untrusted) -/

/-- The least-`Φ` monotone path from `a` to `b` whose points other than `a` have `x - y` in `[lo, hi]`, as directions
(dynamic programming over the grid of the path). -/
def dpPath (c : List Int) (a b : List Int) (lo hi : Int) : Option (Int × List Nat) :=
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
  let phiAt (i j : Nat) : Int := phiP c [a.getD 0 0 + sx * i, a.getD 1 0 + sy * j]
  let okAt (i j : Nat) : Bool :=
    let d := (a.getD 0 0 + sx * i) - (a.getD 1 0 + sy * j)
    decide (lo ≤ d) && decide (d ≤ hi)
  -- best[i * W + j] = (Φ, last step: 0 = from (i-1, j), 1 = from (i, j-1))
  let init : Array (Int × Nat) := (Array.replicate ((nx + 1) * W) (INF, 0)).set! 0 (0, 0)
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
  -- reconstruct backwards
  let rec back (fuel i j : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if i == 0 && j == 0 then acc else
      let e := best[i * W + j]!
      if e.2 == 0 then back fuel (i - 1) j (stx :: acc) else back fuel i (j - 1) (sty :: acc)
  some (fin.1, back (nx + ny + 1) nx ny [])

/-- The two SAFE paths from `a` to `b` (profiles `[lo', hi' + 1]` and `[lo' - 1, hi']`), with their `Φ`. -/
def safePaths (n : Nat) (c : List Int) (a b : List Int) : Option ((Int × List (List Int × Nat)) × (Int × List (List Int × Nat))) :=
  let lo := min (dxy a) (dxy b)
  let hi := max (dxy a) (dxy b)
  match dpPath c a b lo (hi + 1), dpPath c a b (lo - 1) hi with
  | some (f1, d1), some (f2, d2) => some ((f1, chainAlt n a d1), (f2, chainAlt n a d2))
  | _, _ => none

/-- Least-cost, then least SAFE `Φ` (the larger of the two paths' `Φ` per pair), perfect matching by dynamic
programming over subsets; returns the pairs. -/
def matchDPS (n : Nat) (c : List Int) (T : Array (List Int)) : Option (Nat × Int × List (Nat × Nat)) :=
  let t := T.size
  if t % 2 == 1 then none else
  let costT : Array Nat := (List.range (t * t)).foldl (fun acc k => acc.push (l1 T[k / t]! T[k % t]!)) #[]
  let phiT : Array Int := (List.range (t * t)).foldl (fun acc k =>
    match safePaths n c T[k / t]! T[k % t]! with
    | some (p1, p2) => acc.push (max p1.1 p2.1)
    | none => acc.push 1000000000000) #[]
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
        let ff := e.2.1 + phiT[i * t + j]!
        let e2 := best[m2]!
        if cc < e2.1 || (cc == e2.1 && ff < e2.2.1) then best.set! m2 (cc, ff, i, j) else best) best) init
  let ef := best[N - 1]!
  if ef.1 ≥ INF then none else some (ef.1, ef.2.1, recon best t (N - 1) [])

/-- The SAFE witness search. -/
def findWS (n : Nat) (c : List Int) (w : List (Nat × Bool)) : Option (Wit × Wit) :=
  let pts := walkPts n (zeros n) (w.map Prod.fst)
  let X := cEdges n w
  let Y := eEdges n w
  let nC := X.length
  let nE := Y.length
  let a := zeros n
  let b := pts.getLastD a
  let dist := l1 a b
  let phC := phiE c X
  match safePaths n c a b with
  | none => none
  | some (p1, p2) =>
    if nC > nE + dist then some (⟨true, p1.2⟩, ⟨true, p2.2⟩)
    else if nC > 0 && nC == nE + dist && decide (phiE c Y + max p1.1 p2.1 < phC) then some (⟨true, p1.2⟩, ⟨true, p2.2⟩)
    else if nC < 2 then none
    else
      let T := oddVerts pts (w.map Prod.snd)
      match matchDPS n c T with
      | none => none
      | some (cost, f, pairs) =>
        if nC > cost || (nC == cost && decide (f < phC)) then
          let alts := pairs.map (fun pr => safePaths n c T[pr.1]! T[pr.2]!)
          let alt1 := alts.flatMap (fun o => match o with | some (q1, _) => q1.2 | none => [])
          let alt2 := alts.flatMap (fun o => match o with | some (_, q2) => q2.2 | none => [])
          let fix (alt : List (List Int × Nat)) : List (List Int × Nat) :=
            if nC > cost || nodupE (altEdges n alt) then alt else oddAlt n alt
          some (⟨false, fix alt1⟩, ⟨false, fix alt2⟩)
        else none

/-! ## Certificate checks with the SAFE rules (as in `Core.lean`) -/

/-- The window `u` is excluded by SAFE witnesses found by the search and checked. -/
def exclWinS (P : Params) (u : List (Nat × Bool)) : Bool :=
  match findWS P.n P.c u with
  | some (W1, W2) => checkWS P.n P.c u W1 W2
  | none => false

/-- Some window of `2..K+1` edges ending with the last edge of `u` is SAFE-excluded (found and checked). -/
def exclEndingS (P : Params) (u : List (Nat × Bool)) : Bool :=
  (List.range (P.K + 2)).any (fun m => decide (2 ≤ m) && decide (m ≤ u.length) && exclWinS P (u.drop (u.length - m)))

/-- The weighted sum over the successors of the state `s` (SAFE rules). -/
def rowSumS (P : Params) (keys Hs : Array Nat) (s : List (Nat × Bool)) : Option Nat :=
  (candList P.n).foldl (fun acc x =>
    match acc with
    | none => none
    | some tot =>
      let u := s ++ [x]
      if !selfAvoid P.n u then some tot
      else match lookup keys (keyOf P.n u.tail) with
        | some j => if exclWinS P u then some tot else some (tot + (if x.2 then P.wC else P.wE) * Hs[j]!)
        | none => if exclEndingS P u then some tot else none) (some 0)

/-- The row of state `i` (SAFE rules). -/
def rowCheckS (P : Params) (keys Hs : Array Nat) (i : Nat) : Bool :=
  let h := Hs[i]!
  decide (0 < P.Hmin) && decide (P.Hmin ≤ h) &&
  match rowSumS P keys Hs (decodeKey P.n P.K keys[i]!) with
  | some tot => decide (tot * P.lamD ≤ P.lamN * P.Q * h)
  | none => false

/-- The rows of the states `lo, …, hi - 1` (SAFE rules). -/
def rowsOKS (P : Params) (keys Hs : Array Nat) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (rowCheckS P keys Hs)

/-- Start completeness (SAFE rules). -/
def dfsOKS (P : Params) (keys : Array Nat) : Nat → List (Nat × Bool) → Bool
  | 0, pfx => (lookup keys (keyOf P.n pfx)).isSome
  | r + 1, pfx => (candList P.n).all (fun x =>
      let u := pfx ++ [x]
      !selfAvoid P.n u || exclEndingS P u || dfsOKS P keys r u)

/-- The part of the start check that begins with the `j`-th candidate step (SAFE rules). -/
def dfsTopS (P : Params) (keys : Array Nat) (j : Nat) : Bool :=
  match (candList P.n)[j]? with
  | some x => !selfAvoid P.n [x] || exclEndingS P [x] || dfsOKS P keys (P.K - 1) [x]
  | none => true

end QECComp
